import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleUnitLocus

/-! # Exact-degree schemes and their trivial self-correspondences -/

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

section ClosedRelation

variable [IsClosedImmersion (prod.lift E.t E.s)]

/-- Over any test scheme whose left endpoint avoids the next threshold,
the self-correspondence is the unit. No reducedness assumption is needed. -/
theorem tupleSymmetricCross_factors_unit_of_not_threshold (n : ℕ)
    {T : Scheme.{u}} (f : T ⟶ E.tupleSymmetricCrossScheme n n)
    (hf : ∀ x : T, (f ≫ E.tupleSymmetricCrossLeft n n) x ∉
      E.tupleSymmetricThresholdOpen n (n + 1)) :
    f = f ≫ E.tupleSymmetricCrossLeft n n ≫ E.tupleSymmetricCrossUnit n := by
  have h : Set.range f ⊆ Set.range (E.tupleSymmetricCrossUnit n) := by
    rintro _ ⟨x, rfl⟩
    exact E.tupleSymmetricCross_point_mem_unit_range n (f x) (hf x)
  let g := IsOpenImmersion.lift (E.tupleSymmetricCrossUnit n) f h
  have hg : g ≫ E.tupleSymmetricCrossUnit n = f :=
    IsOpenImmersion.lift_fac _ _ h
  have hgl : g = f ≫ E.tupleSymmetricCrossLeft n n := by
    simpa only [Category.assoc, E.tupleSymmetricCrossUnit_left,
      Category.comp_id] using congrArg (· ≫ E.tupleSymmetricCrossLeft n n) hg
  calc
    f = g ≫ E.tupleSymmetricCrossUnit n := hg.symm
    _ = _ := by rw [hgl, Category.assoc]

theorem tupleSymmetricCross_endpoints_eq_of_not_threshold (n : ℕ)
    {T : Scheme.{u}} (f : T ⟶ E.tupleSymmetricCrossScheme n n)
    (hf : ∀ x : T, (f ≫ E.tupleSymmetricCrossLeft n n) x ∉
      E.tupleSymmetricThresholdOpen n (n + 1)) :
    f ≫ E.tupleSymmetricCrossLeft n n =
      f ≫ E.tupleSymmetricCrossRight n n := by
  simpa only [Category.assoc, E.tupleSymmetricCrossUnit_right, Category.comp_id] using
    (congrArg (· ≫ E.tupleSymmetricCrossRight n n)
      (E.tupleSymmetricCross_factors_unit_of_not_threshold n f hf)).symm

/-- The unit identifies the left-endpoint pullback over any scheme mapping
outside the next symmetric threshold. -/
theorem tupleSymmetricCross_unit_isPullback_of_not_threshold (n : ℕ)
    {T : Scheme.{u}} (d : T ⟶ E.tupleSymmetricScheme n)
    (hd : ∀ x : T, d x ∉ E.tupleSymmetricThresholdOpen n (n + 1)) :
    IsPullback (d ≫ E.tupleSymmetricCrossUnit n) (𝟙 T)
      (E.tupleSymmetricCrossLeft n n) d := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro V a b _ h
    simpa using h
  · intro V a b hab
    have ha := E.tupleSymmetricCross_factors_unit_of_not_threshold n a (by
      intro x
      rw [hab]
      exact hd (b x))
    refine ⟨b, ?_, by simp⟩
    calc
      b ≫ (d ≫ E.tupleSymmetricCrossUnit n) =
          (b ≫ d) ≫ E.tupleSymmetricCrossUnit n := (Category.assoc _ _ _).symm
      _ = (a ≫ E.tupleSymmetricCrossLeft n n) ≫
          E.tupleSymmetricCrossUnit n := by rw [hab]
      _ = a := by simpa only [Category.assoc] using ha.symm

end ClosedRelation

/-- The canonical closed scheme defined by the vanishing ideal of the
complement of the next symmetric threshold. -/
def tupleSymmetricDegreeScheme (n : ℕ) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (E.tupleSymmetricDegreeClosed n)).subscheme

/-- The closed inclusion of the exact-degree scheme into the symmetric
tuple scheme. -/
def tupleSymmetricDegreeι (n : ℕ) :
    E.tupleSymmetricDegreeScheme n ⟶ E.tupleSymmetricScheme n :=
  (Scheme.IdealSheafData.vanishingIdeal (E.tupleSymmetricDegreeClosed n)).subschemeι

instance tupleSymmetricDegreeι_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (E.tupleSymmetricDegreeι n) :=
  inferInstanceAs (IsClosedImmersion
    (Scheme.IdealSheafData.vanishingIdeal (E.tupleSymmetricDegreeClosed n)).subschemeι)

instance tupleSymmetricDegreeScheme_isAffine (n : ℕ) :
    IsAffine (E.tupleSymmetricDegreeScheme n) :=
  isAffine_of_isAffineHom (E.tupleSymmetricDegreeι n)

theorem tupleSymmetricDegreeι_range (n : ℕ) :
    Set.range (E.tupleSymmetricDegreeι n) =
      (E.tupleSymmetricDegreeClosed n : Set (E.tupleSymmetricScheme n)) := by
  change Set.range
    (Scheme.IdealSheafData.vanishingIdeal (E.tupleSymmetricDegreeClosed n)).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

theorem tupleSymmetricDegreeι_not_mem_threshold (n : ℕ)
    (x : E.tupleSymmetricDegreeScheme n) :
    E.tupleSymmetricDegreeι n x ∉ E.tupleSymmetricThresholdOpen n (n + 1) := by
  change E.tupleSymmetricDegreeι n x ∈
    (E.tupleSymmetricDegreeClosed n : Set (E.tupleSymmetricScheme n))
  rw [← E.tupleSymmetricDegreeι_range n]
  exact ⟨x, rfl⟩

variable [IsClosedImmersion (prod.lift E.t E.s)]

theorem tupleSymmetricDegree_unit_isPullback (n : ℕ) :
    IsPullback (E.tupleSymmetricDegreeι n ≫ E.tupleSymmetricCrossUnit n)
      (𝟙 (E.tupleSymmetricDegreeScheme n))
      (E.tupleSymmetricCrossLeft n n) (E.tupleSymmetricDegreeι n) :=
  E.tupleSymmetricCross_unit_isPullback_of_not_threshold n
    (E.tupleSymmetricDegreeι n) (E.tupleSymmetricDegreeι_not_mem_threshold n)

/-- The exact-degree self-correspondence is canonically the degree scheme. -/
def tupleSymmetricDegreeCrossIso (n : ℕ) :
    E.tupleSymmetricDegreeScheme n ≅
      pullback (E.tupleSymmetricCrossLeft n n) (E.tupleSymmetricDegreeι n) :=
  (E.tupleSymmetricDegree_unit_isPullback n).isoPullback

@[reassoc (attr := simp)]
theorem tupleSymmetricDegreeCrossIso_hom_fst (n : ℕ) :
    (E.tupleSymmetricDegreeCrossIso n).hom ≫ pullback.fst _ _ =
      E.tupleSymmetricDegreeι n ≫ E.tupleSymmetricCrossUnit n :=
  (E.tupleSymmetricDegree_unit_isPullback n).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem tupleSymmetricDegreeCrossIso_hom_snd (n : ℕ) :
    (E.tupleSymmetricDegreeCrossIso n).hom ≫ pullback.snd _ _ = 𝟙 _ :=
  (E.tupleSymmetricDegree_unit_isPullback n).isoPullback_hom_snd

theorem tupleSymmetricDegreeCrossIso_inv_eq_snd (n : ℕ) :
    (E.tupleSymmetricDegreeCrossIso n).inv = pullback.snd _ _ := by
  simpa only [tupleSymmetricDegreeCrossIso, Category.comp_id] using
    (E.tupleSymmetricDegree_unit_isPullback n).isoPullback_inv_snd

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
