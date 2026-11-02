import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleFieldPoints
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleCrossLaws
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Symmetric tuple threshold opens and reduced degree loci -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R]

/-- The open image in the symmetric tuple scheme of the inverse image of
the `k`th object threshold under the ordered zeroth-coordinate projection. -/
def tupleSymmetricThresholdOpen (n k : ℕ) : (E.tupleSymmetricScheme n).Opens :=
  ⟨E.tupleSymmetricMap n ''
      ((E.tupleDistinctProjection n 0) ⁻¹' (E.tupleThresholdOpen k : Set E.U)),
    (E.tupleSymmetricMap n).isOpenMap _
      ((E.tupleThresholdOpen k).isOpen.preimage
        (E.tupleDistinctProjection n 0).continuous)⟩

theorem tupleSymmetricThresholdOpen_antitone (n : ℕ) :
    Antitone (E.tupleSymmetricThresholdOpen n) := by
  intro k l h
  exact Set.image_mono (Set.preimage_mono (E.tupleThresholdOpen_antitone h))

theorem tupleSymmetricThresholdOpen_self (n : ℕ) :
    E.tupleSymmetricThresholdOpen n n = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := (E.tupleSymmetricMap n).surjective x
  refine ⟨y, ?_, rfl⟩
  exact E.le_pointSaturationOpen _ ⟨y, rfl⟩

theorem tupleSymmetricThresholdOpen_isCompact (n k : ℕ) :
    IsCompact (E.tupleSymmetricThresholdOpen n k :
      Set (E.tupleSymmetricScheme n)) :=
  ((E.tupleDistinctProjection n 0).isCompact_preimage
    (E.tupleThresholdOpen_isCompact k)).image (E.tupleSymmetricMap n).continuous

theorem tupleSymmetricThresholdOpen_eq_bot (n k : ℕ) (hk : E.tupleLengthBound ≤ k) :
    E.tupleSymmetricThresholdOpen n k = ⊥ := by
  apply Opens.ext
  simp [tupleSymmetricThresholdOpen, E.tupleThresholdOpen_eq_bot k hk]

/-- The closed complement of the next threshold in the symmetric tuple scheme.
This declaration gives a closed set, without choosing its scheme structure. -/
def tupleSymmetricDegreeClosed (n : ℕ) : Closeds (E.tupleSymmetricScheme n) :=
  ⟨(E.tupleSymmetricThresholdOpen n (n + 1) :
      Set (E.tupleSymmetricScheme n))ᶜ,
    (E.tupleSymmetricThresholdOpen n (n + 1)).isOpen.isClosed_compl⟩

/-- The unordered endpoints of a field-valued symmetric cross arrow agree
when its left endpoint avoids the next symmetric threshold. -/
theorem tupleSymmetricCross_fieldPoint_endpoints_eq
    (n : ℕ) (K : Type u) [Field K]
    (f : Spec (.of K) ⟶ E.tupleSymmetricCrossScheme n n)
    (hf : ∀ x : Spec (.of K), (f ≫ E.tupleSymmetricCrossLeft n n) x ∉
      E.tupleSymmetricThresholdOpen n (n + 1)) :
    f ≫ E.tupleSymmetricCrossLeft n n = f ≫ E.tupleSymmetricCrossRight n n := by
  let P := pullback f (E.tupleSymmetricCrossMap n n)
  let q : P ⟶ Spec (.of K) := pullback.fst _ _
  let a : P ⟶ E.tupleCrossScheme n n := pullback.snd _ _
  have : Etale q := inferInstance
  have : Surjective q := inferInstance
  let : IsReduced P := SmoothReducedProof.isReduced_of_smooth_over_field K P q
  have hq : q ≫ f = a ≫ E.tupleSymmetricCrossMap n n := pullback.condition
  have hl : q ≫ f ≫ E.tupleSymmetricCrossLeft n n =
      a ≫ E.tupleCrossLeft n n ≫ E.tupleSymmetricMap n := by
    rw [← Category.assoc, hq, Category.assoc, E.tupleSymmetricCrossMap_left]
  have hr : q ≫ f ≫ E.tupleSymmetricCrossRight n n =
      a ≫ E.tupleCrossRight n n ≫ E.tupleSymmetricMap n := by
    rw [← Category.assoc, hq, Category.assoc, E.tupleSymmetricCrossMap_right]
  apply (cancel_epi q).mp
  rw [hl, hr]
  apply ext_of_fromSpecResidueField_eq _ _ (terminal.from _) Set.univ dense_univ
  · intro x _
    let g := P.fromSpecResidueField x ≫ a
    have hx : (g ≫ E.tupleCrossLeft n n ≫ E.tupleDistinctProjection n 0) default ∉
        E.tupleThresholdOpen (n + 1) := by
      intro hbad
      apply hf (q x)
      have hpoint := congrArg (fun k => k x) hl
      simp only [Scheme.Hom.comp_apply] at hpoint
      simp only [Scheme.Hom.comp_apply]
      rw [hpoint]
      refine ⟨(E.tupleCrossLeft n n) (a x), ?_, rfl⟩
      change (E.tupleDistinctProjection n 0)
        ((E.tupleCrossLeft n n) (a (P.fromSpecResidueField x default))) ∈
          E.tupleThresholdOpen (n + 1) at hbad
      rwa [Scheme.fromSpecResidueField_apply] at hbad
    simpa [g, Category.assoc] using
      E.tupleCross_fieldPoint_symmetric_eq_of_not_threshold n (P.residueField x) g hx
  · exact terminal.hom_ext _ _

/-- The same endpoint equality holds on reduced test schemes. -/
theorem tupleSymmetricCross_endpoints_eq_of_reduced (n : ℕ)
    {T : Scheme.{u}} [IsReduced T] (f : T ⟶ E.tupleSymmetricCrossScheme n n)
    (hf : ∀ x : T, (f ≫ E.tupleSymmetricCrossLeft n n) x ∉
      E.tupleSymmetricThresholdOpen n (n + 1)) :
    f ≫ E.tupleSymmetricCrossLeft n n = f ≫ E.tupleSymmetricCrossRight n n := by
  apply ext_of_fromSpecResidueField_eq _ _ (terminal.from _) Set.univ dense_univ
  · intro x _
    have h := E.tupleSymmetricCross_fieldPoint_endpoints_eq n (T.residueField x)
      (T.fromSpecResidueField x ≫ f) (by
        intro y
        change (E.tupleSymmetricCrossLeft n n)
          (f (T.fromSpecResidueField x y)) ∉ E.tupleSymmetricThresholdOpen n (n + 1)
        rw [Scheme.fromSpecResidueField_apply]
        exact hf x)
    simpa [Category.assoc] using h
  · exact terminal.hom_ext _ _

variable [IsClosedImmersion (prod.lift E.t E.s)]

/-- A symmetric cross arrow on a reduced test scheme outside the next threshold
is the identity arrow of its left endpoint. -/
theorem tupleSymmetricCross_factors_unit_of_reduced (n : ℕ)
    {T : Scheme.{u}} [IsReduced T] (f : T ⟶ E.tupleSymmetricCrossScheme n n)
    (hf : ∀ x : T, (f ≫ E.tupleSymmetricCrossLeft n n) x ∉
      E.tupleSymmetricThresholdOpen n (n + 1)) :
    f = f ≫ E.tupleSymmetricCrossLeft n n ≫ E.tupleSymmetricCrossUnit n := by
  have h := E.tupleSymmetricCross_endpoints_eq_of_reduced n f hf
  apply E.tupleSymmetricCross_hom_ext n n
  · simp
  · simpa using h.symm

theorem tupleSymmetricCross_point_mem_unit_range (n : ℕ)
    (x : E.tupleSymmetricCrossScheme n n)
    (hx : E.tupleSymmetricCrossLeft n n x ∈ E.tupleSymmetricDegreeClosed n) :
    x ∈ Set.range (E.tupleSymmetricCrossUnit n) := by
  let X := E.tupleSymmetricCrossScheme n n
  let f := X.fromSpecResidueField x
  have h := E.tupleSymmetricCross_factors_unit_of_reduced n f (by
    intro y
    change (E.tupleSymmetricCrossLeft n n) (X.fromSpecResidueField x y) ∉
      E.tupleSymmetricThresholdOpen n (n + 1)
    rw [Scheme.fromSpecResidueField_apply]
    exact hx)
  refine ⟨(f ≫ E.tupleSymmetricCrossLeft n n) default, ?_⟩
  have hp := congrArg (fun k => k default) h.symm
  change (E.tupleSymmetricCrossUnit n)
    ((E.tupleSymmetricCrossLeft n n) (X.fromSpecResidueField x default)) =
      X.fromSpecResidueField x default at hp
  rw [Scheme.fromSpecResidueField_apply] at hp
  change (E.tupleSymmetricCrossUnit n)
    ((E.tupleSymmetricCrossLeft n n) (X.fromSpecResidueField x default)) = x
  rw [Scheme.fromSpecResidueField_apply]
  exact hp

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
