import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Extending generic sections of finite schemes over valuation rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A point over the fraction field of a valuation ring extends uniquely to a
section of any finite scheme over that ring. -/
theorem existsUnique_section_of_finite
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (C : Over (Spec (CommRingCat.of R))) [IsFinite C.hom]
    (p : Over.mk (Spec.algebraMap R K) ⟶ C) :
    ∃! s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ C,
      (Over.homMk (Spec.algebraMap R K) : Over.mk (Spec.algebraMap R K) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ s = p := by
  let sq : ValuativeCommSq C.hom :=
    { R := R
      K := K
      i₁ := p.left
      i₂ := 𝟙 _
      commSq := ⟨by simp⟩ }
  have he : ValuativeCriterion.Existence C.hom := by
    have h : UniversallyClosed C.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨l⟩ := (he sq).exists_lift
  let s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ C :=
    Over.homMk l.l l.fac_right
  refine ⟨s, Over.OverMorphism.ext l.fac_left, ?_⟩
  intro t ht
  let lt : sq.commSq.LiftStruct :=
    { l := t.left
      fac_left := congrArg (fun q => q.left) ht
      fac_right := Over.w t }
  have hu : lt = l := (IsSeparated.valuativeCriterion C.hom sq).elim _ _
  exact Over.OverMorphism.ext (congrArg (fun q => q.l) hu)

/-- The unique integral section extending a prescribed generic point. -/
noncomputable def finiteGenericSection
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (C : Over (Spec (CommRingCat.of R))) [IsFinite C.hom]
    (p : Over.mk (Spec.algebraMap R K) ⟶ C) :
    Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ C :=
  (existsUnique_section_of_finite R K C p).choose

/-- The chosen section retains the specified generic point exactly. -/
theorem finiteGenericSection_generic
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (C : Over (Spec (CommRingCat.of R))) [IsFinite C.hom]
    (p : Over.mk (Spec.algebraMap R K) ⟶ C) :
    (Over.homMk (Spec.algebraMap R K) : Over.mk (Spec.algebraMap R K) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ finiteGenericSection R K C p = p :=
  (existsUnique_section_of_finite R K C p).choose_spec.1

/-- Every section with the prescribed generic restriction is the chosen one. -/
theorem finiteGenericSection_unique
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (C : Over (Spec (CommRingCat.of R))) [IsFinite C.hom]
    (p : Over.mk (Spec.algebraMap R K) ⟶ C)
    (s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ C)
    (hs : (Over.homMk (Spec.algebraMap R K) : Over.mk (Spec.algebraMap R K) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ s = p) :
    s = finiteGenericSection R K C p :=
  (existsUnique_section_of_finite R K C p).choose_spec.2 s hs

end Langlands.AlgebraicGeometry
