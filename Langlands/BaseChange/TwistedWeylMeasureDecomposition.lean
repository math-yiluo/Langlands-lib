import Langlands.Analysis.CountableBranchPushforward
import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.BaseChange.TwistedWeylOrbit

/-! # The twisted Weyl measure decomposition from local pushforwards -/

namespace Langlands.BaseChange

open Langlands.QuotientIntegration
open Filter MeasureTheory Set _root_.Topology
open scoped ENNReal

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

private theorem restrict_iUnion_disjoint_open {I X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (A : I → Set X) (ho : ∀ i, IsOpen (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    μ.restrict (⋃ i, A i) = Measure.sum (fun i => μ.restrict (A i)) := by
  let J : Set I := {i | (A i).Nonempty}
  have hdJ : J.PairwiseDisjoint A := by
    intro i hi j hj hij
    exact hd hij
  have hcJ : J.Countable := hdJ.countable_of_isOpen (fun i _ => ho i) (fun _ hi => hi)
  have hU : ⋃ i, A i = ⋃ i ∈ J, A i := by
    ext x
    simp only [mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, ⟨x, hi⟩, hi⟩, fun ⟨i, _, hi⟩ => ⟨i, hi⟩⟩
  rw [hU, Measure.restrict_biUnion hcJ hdJ (fun i => (ho i).measurableSet)]
  ext1 s hs
  simp only [Measure.sum_apply _ hs]
  refine tsum_subtype_eq_of_support_subset (s := J) (f := fun i => (μ.restrict (A i)) s) ?_
  intro i hi
  by_contra hn
  have hempty : A i = ∅ := not_nonempty_iff_eq_empty.mp hn
  simp [Function.mem_support, hempty] at hi

namespace WeylTorus

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type v} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
  {σ : E ≃ₐ[F] E} {l n : ℕ}
  [MeasurableSpace (GeneralLinear n F)] [MeasurableSpace (GeneralLinear n E)]

variable (T : WeylTorus F n) (hσ : IsCyclicAlgebra σ l)
  (lift : T.regularNormPoints σ l → T.points E)
  (hlift : ∀ t, cyclicNorm σ l (lift t).val = baseChange F E n t.val.val)

local notation "Q" => LeftQuotient (T.val.map (baseChange F E n))
local notation "A" => T.regularNormPoints σ l
local notation "p" => T.twistedOrbitMap hσ lift hlift

/-- Local open branches of a chosen twisted Weyl map with exact restricted
pushforwards. -/
def HasTwistedLocalPushforwards (μ : Measure (GeneralLinear n E)) (ρ : Measure (Q × A)) :
    Prop :=
  ∀ x : Q × A, ∃ V : Set (Q × A), x ∈ V ∧ IsOpen V ∧
    IsOpenEmbedding (fun z : V => p z.val) ∧
    (ρ.restrict V).map p = μ.restrict (p '' V)

/-- The local open branches make the chosen twisted Weyl map continuous. -/
theorem continuous_twistedOrbitMap_of_branches {μ ρ}
    (h : T.HasTwistedLocalPushforwards hσ lift hlift μ ρ) : Continuous p := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨V, hx, ho, he, _⟩ := h x
  have hc : ContinuousOn p V := continuousOn_iff_continuous_domRestrict.mpr he.continuous
  exact (hc x hx).continuousAt (ho.mem_nhds hx)

/-- The image of the twisted Weyl map is open when it has local open branches. -/
theorem isOpen_range_twistedOrbitMap {μ ρ}
    (h : T.HasTwistedLocalPushforwards hσ lift hlift μ ρ) : IsOpen (range p) := by
  choose V hV _ hemb _ using h
  have hr : range p = ⋃ x, range (fun z : V x => p z.val) := by
    apply le_antisymm
    · rintro d ⟨x, rfl⟩
      exact mem_iUnion.mpr ⟨x, ⟨⟨x, hV x⟩, rfl⟩⟩
    · intro d hd
      obtain ⟨x, z, hz⟩ := mem_iUnion.mp hd
      exact ⟨z.val, hz⟩
  rw [hr]
  exact isOpen_iUnion fun x => (hemb x).isOpen_range

omit [MeasurableSpace (GeneralLinear n F)] [MeasurableSpace (GeneralLinear n E)] in
include hσ in
private theorem secondCountable_twistedQuotient : SecondCountableTopology Q := by
  let : Module.Finite F E := hσ.1
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : SecondCountableTopology (GeneralLinear n E) :=
    generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := E) n
  exact (leftQuotient_isOpenQuotientMap (T.val.map (baseChange F E n))).secondCountableTopology

omit [MeasurableSpace (GeneralLinear n F)] [MeasurableSpace (GeneralLinear n E)] in
include hσ in
private theorem secondCountable_twistedOrbitDomain : SecondCountableTopology (Q × A) := by
  let : SecondCountableTopology Q := T.secondCountable_twistedQuotient hσ
  let : SecondCountableTopology (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_secondCountableTopology F n
  let : SecondCountableTopology T.val := IsInducing.subtypeVal.secondCountableTopology
  let : SecondCountableTopology A := IsInducing.subtypeVal.secondCountableTopology
  infer_instance

variable [BorelSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n E)]

theorem measurable_twistedOrbitMap_of_branches {μ ρ}
    (h : T.HasTwistedLocalPushforwards hσ lift hlift μ ρ) : Measurable p := by
  let : SecondCountableTopology Q := T.secondCountable_twistedQuotient hσ
  exact (T.continuous_twistedOrbitMap_of_branches hσ lift hlift h).measurable

/-- A twisted Weyl orbit map with local pushforward identities has the same
rational Weyl factor as the ordinary orbit map. -/
theorem map_twistedOrbitMap {μ ρ}
    (h : T.HasTwistedLocalPushforwards hσ lift hlift μ ρ) :
    ρ.map p = (Nat.card T.RationalWeylGroup : ℝ≥0∞) • μ.restrict (range p) := by
  let : SecondCountableTopology (Q × A) := T.secondCountable_twistedOrbitDomain hσ
  let : SecondCountableTopology Q := T.secondCountable_twistedQuotient hσ
  refine Analysis.map_eq_smul_restrict_range_of_locally p ρ μ
    (T.measurable_twistedOrbitMap_of_branches hσ lift hlift h) ?_
    T.natCard_rationalWeylGroup_pos
    (fun _ hd => T.natCard_twistedOrbitFiber hσ lift hlift hd)
  intro x
  obtain ⟨V, hx, ho, he, hm⟩ := h x
  exact ⟨V, hx, ho, he.measurableEmbedding, hm⟩

end WeylTorus

/-- Local pushforwards on the representative twisted branches determine the
ambient measure on the σ-regular locus. Empty norm-image domains are allowed. -/
def TwistedWeylMeasureDecompositionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type v) [CommRing E] [Algebra F E]
    [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ) (hσ : IsCyclicAlgebra σ l)
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    (μ : Measure (GeneralLinear n E)) (S : Set (WeylTorus F n)), WeylTorus.IsRepresentativeSet S →
    ∀ (lift : ∀ T : S, T.val.regularNormPoints σ l → T.val.points E)
      (hlift : ∀ (T : S) (t : T.val.regularNormPoints σ l),
        cyclicNorm σ l (lift T t).val = baseChange F E n t.val.val)
      (ρ : ∀ T : S, Measure (LeftQuotient (T.val.val.map (baseChange F E n)) ×
        T.val.regularNormPoints σ l)),
      (∀ T : S, T.val.HasTwistedLocalPushforwards hσ (lift T) (hlift T) μ (ρ T)) →
      μ.restrict {d | IsSigmaRegular σ l d} = Measure.sum (fun T : S =>
        (Nat.card T.val.RationalWeylGroup : ℝ≥0∞)⁻¹ •
          (ρ T).map (T.val.twistedOrbitMap hσ (lift T) (hlift T)))

theorem twistedWeylMeasureDecomposition : TwistedWeylMeasureDecompositionStatement.{u, v} := by
  intro F _ _ _ _ E _ _ _ _ _ σ l n hσ _ _ _ _ μ S hS lift hlift ρ hlocal
  let : Module.Finite F E := hσ.1
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : SecondCountableTopology (GeneralLinear n E) :=
    generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := E) n
  let A (T : S) := range (T.val.twistedOrbitMap hσ (lift T) (hlift T))
  have hpart := (twistedWeylOrbitDecomposition F E σ l n hσ S hS lift hlift).1
  have hopen (T : S) : IsOpen (A T) :=
    T.val.isOpen_range_twistedOrbitMap hσ (lift T) (hlift T) (hlocal T)
  have hcover : ⋃ T : S, A T = {d | IsSigmaRegular σ l d} := by
    ext d
    constructor
    · intro hd
      obtain ⟨T, p, rfl⟩ := mem_iUnion.mp hd
      exact T.val.isSigmaRegular_twistedOrbitMap hσ (lift T) (hlift T) p
    · intro hd
      obtain ⟨T, hT, _⟩ := (hpart d).mp hd
      exact mem_iUnion.mpr ⟨T, hT⟩
  have hd : Pairwise (fun T U : S => Disjoint (A T) (A U)) := by
    intro T U hne
    refine disjoint_left.mpr fun {d} hT hU => hne ?_
    have hreg : d ∈ {d | IsSigmaRegular σ l d} := hcover ▸ mem_iUnion.mpr ⟨T, hT⟩
    obtain ⟨_, _, huniq⟩ := (hpart d).mp hreg
    exact (huniq T hT).trans (huniq U hU).symm
  rw [← hcover, restrict_iUnion_disjoint_open μ A hopen hd]
  congr 1
  funext T
  have hn : (Nat.card T.val.RationalWeylGroup : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast T.val.natCard_rationalWeylGroup_pos.ne'
  rw [T.val.map_twistedOrbitMap hσ (lift T) (hlift T) (hlocal T), smul_smul,
    ENNReal.inv_mul_cancel hn (by simp), one_smul]

end Langlands.BaseChange
