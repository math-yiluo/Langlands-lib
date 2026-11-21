import Langlands.Analysis.CountableBranchPushforward
import Langlands.BaseChange.OrdinaryWeylOrbit
import Langlands.Group.GL.LocalFieldTopology

/-! # The ordinary Weyl measure decomposition from local pushforwards -/

namespace Langlands.BaseChange

open Langlands.JacquetLanglands Langlands.QuotientIntegration
open MeasureTheory Set Topology
open scoped ENNReal

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u

variable {F : Type u} [Field F] {n : ℕ}

namespace WeylTorus

/-- An ordinary Weyl map has nonempty image since its torus is a regular centralizer. -/
theorem nonempty_range_ordinaryOrbitMap (T : WeylTorus F n) :
    (range T.ordinaryOrbitMap).Nonempty := by
  obtain ⟨γ, hγ, hT⟩ := T.property
  have hmem : γ ∈ T.val := by
    rw [← hT, glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  let t : T.regularPoints := ⟨⟨γ, hmem⟩, hγ⟩
  exact ⟨_, ⟨(leftQuotientMap T.val 1, t), rfl⟩⟩

/-- Conjugation with a varying regular torus parameter is continuous on the coset product. -/
theorem continuous_ordinaryOrbitMap [TopologicalSpace F]
    [IsTopologicalGroup (GeneralLinear n F)] (T : WeylTorus F n) :
    Continuous T.ordinaryOrbitMap := by
  have hq := (leftQuotient_isOpenQuotientMap T.val).prodMap
    (IsOpenQuotientMap.id (X := T.regularPoints))
  apply hq.continuous_comp_iff.mp
  change Continuous (fun p : GeneralLinear n F × T.regularPoints =>
    p.1⁻¹ * p.2.val.val * p.1)
  exact (continuous_fst.inv.mul
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).mul
    continuous_fst

variable [TopologicalSpace F] [MeasurableSpace (GeneralLinear n F)]

/-- The ordinary Weyl map is locally an open embedding whose pushforward of
the restricted source measure equals the ambient measure on the branch image. -/
def HasOrdinaryLocalPushforwards (T : WeylTorus F n)
    (μ : Measure (GeneralLinear n F)) (ρT : Measure (LeftQuotient T.val × T.regularPoints)) :
    Prop :=
  ∀ x : LeftQuotient T.val × T.regularPoints,
    ∃ V : Set (LeftQuotient T.val × T.regularPoints), x ∈ V ∧ IsOpen V ∧
      IsOpenEmbedding (fun z : V => T.ordinaryOrbitMap z.val) ∧
      (ρT.restrict V).map T.ordinaryOrbitMap = μ.restrict (T.ordinaryOrbitMap '' V)

/-- The range of a Weyl map is open when every point of its source has an open branch. -/
theorem isOpen_range_ordinaryOrbitMap {T : WeylTorus F n} {μ ρT}
    (h : T.HasOrdinaryLocalPushforwards μ ρT) : IsOpen (range T.ordinaryOrbitMap) := by
  choose V hV hopen hemb hmap using h
  have hrange : range T.ordinaryOrbitMap =
      ⋃ x, range (fun z : V x => T.ordinaryOrbitMap z.val) := by
    apply le_antisymm
    · rintro g ⟨x, rfl⟩
      exact mem_iUnion.mpr ⟨x, ⟨⟨x, hV x⟩, rfl⟩⟩
    · intro g hg
      obtain ⟨x, z, hz⟩ := mem_iUnion.mp hg
      exact ⟨z.val, hz⟩
  rw [hrange]
  exact isOpen_iUnion fun x => (hemb x).isOpen_range

variable [ValuativeRel F] [IsNonarchimedeanLocalField F] [BorelSpace (GeneralLinear n F)]

/-- On one ordinary Weyl image the pushforward multiplies the ambient
restriction by the rational Weyl order. -/
theorem map_ordinaryOrbitMap {T : WeylTorus F n} {μ ρT}
    (h : T.HasOrdinaryLocalPushforwards μ ρT) :
    ρT.map T.ordinaryOrbitMap =
      (Nat.card T.RationalWeylGroup : ℝ≥0∞) • μ.restrict (range T.ordinaryOrbitMap) := by
  let : SecondCountableTopology (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_secondCountableTopology F n
  let : SecondCountableTopology (LeftQuotient T.val) :=
    (leftQuotient_isOpenQuotientMap T.val).secondCountableTopology
  let : SecondCountableTopology T.val := IsInducing.subtypeVal.secondCountableTopology
  let : SecondCountableTopology T.regularPoints := IsInducing.subtypeVal.secondCountableTopology
  refine Analysis.map_eq_smul_restrict_range_of_locally T.ordinaryOrbitMap ρT μ
    T.continuous_ordinaryOrbitMap.measurable ?_ T.natCard_rationalWeylGroup_pos
    (fun _ hg => T.natCard_ordinaryOrbitFiber hg)
  intro x
  obtain ⟨V, hx, ho, he, hm⟩ := h x
  exact ⟨V, hx, ho, he.measurableEmbedding, hm⟩

end WeylTorus

/-- Local measure identities for ordinary Weyl maps determine the ambient
measure on the regular semisimple set. -/
def OrdinaryWeylMeasureDecompositionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    (μ : Measure (GeneralLinear n F)) (S : Set (WeylTorus F n)),
    WeylTorus.IsRepresentativeSet S →
    ∀ (ρT : ∀ T : S, Measure (LeftQuotient T.val.val × T.val.regularPoints)),
      (∀ T : S, T.val.HasOrdinaryLocalPushforwards μ (ρT T)) →
      Countable S ∧ μ.restrict {g | IsRegularSemisimple g} =
        Measure.sum (fun T : S =>
          (Nat.card T.val.RationalWeylGroup : ℝ≥0∞)⁻¹ • (ρT T).map T.val.ordinaryOrbitMap)

theorem ordinaryWeylMeasureDecomposition : OrdinaryWeylMeasureDecompositionStatement.{u} := by
  intro F _ _ _ _ n _ _ μ S hS ρT hlocal
  let : SecondCountableTopology (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_secondCountableTopology F n
  let A (T : S) := range T.val.ordinaryOrbitMap
  have hpart := (ordinaryWeylOrbitDecomposition F n S hS).1
  have hopen (T : S) : IsOpen (A T) := T.val.isOpen_range_ordinaryOrbitMap (hlocal T)
  have hcover : ⋃ T : S, A T = {g | IsRegularSemisimple g} := by
    ext g
    constructor
    · intro hg
      obtain ⟨T, p, rfl⟩ := mem_iUnion.mp hg
      exact T.val.isRegularSemisimple_ordinaryOrbitMap p
    · intro hg
      obtain ⟨T, hT, _⟩ := (hpart g).mp hg
      exact mem_iUnion.mpr ⟨⟨T, hT.1⟩, hT.2⟩
  have hd : Pairwise (fun T U : S => Disjoint (A T) (A U)) := by
    intro T U hne
    refine disjoint_left.mpr fun {g} hT hU => hne (Subtype.ext ?_)
    have hg : g ∈ {g | IsRegularSemisimple g} := hcover ▸ mem_iUnion.mpr ⟨T, hT⟩
    obtain ⟨_, _, huniq⟩ := (hpart g).mp hg
    exact (huniq T.val ⟨T.property, hT⟩).trans (huniq U.val ⟨U.property, hU⟩).symm
  have hcount : Countable S := hd.countable_of_isOpen_disjoint hopen fun T =>
    T.val.nonempty_range_ordinaryOrbitMap
  refine ⟨hcount, ?_⟩
  rw [← hcover, Measure.restrict_iUnion hd (fun T => (hopen T).measurableSet)]
  congr 1
  funext T
  have hn : (Nat.card T.val.RationalWeylGroup : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast T.val.natCard_rationalWeylGroup_pos.ne'
  rw [T.val.map_ordinaryOrbitMap (hlocal T), smul_smul,
    ENNReal.inv_mul_cancel hn (by simp), one_smul]

end Langlands.BaseChange
