import Langlands.AlgebraicGeometry.LinearSystem.Nondegeneracy

/-! # Vanishing of linear combinations at field-valued points -/

universe u

open CategoryTheory AlgebraicGeometry Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.ProjectiveSpace

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.LinearSystem

variable {K : Type u} [CommRing K] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of K)) {L : LineBundle X} {n : ℕ}

/-- The homogeneous linear polynomial with coefficients `c` has degree one. -/
lemma linearPolynomial_mem_grading (c : Fin (n + 1) → K) :
    (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) ∈ projectiveSpaceGrading K n 1 := by
  apply Submodule.sum_mem
  intro i _
  exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    ((MvPolynomial.isHomogeneous_C (Fin (n + 1)) (c i)).mul
      (MvPolynomial.isHomogeneous_X K i))

/-- At a field-valued point, a linear combination of generating sections vanishes
exactly when the image of the point under the linear-system map lies on the
hyperplane with the same coefficients. -/
lemma vanishesAlong_linComb_iff {F : Type u} [Field F] (y : Spec (CommRingCat.of F) ⟶ X)
    (s : Fin (n + 1) → GlobalSections L.obj)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) (c : Fin (n + 1) → K) :
    VanishesAlong L y (linComb p s c) ↔
      (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) ∈
        ((linearSystemMap p hs) (y (IsLocalRing.closedPoint F))).asHomogeneousIdeal := by
  obtain ⟨j, hj⟩ := exists_mem_trivializationOpen hs (y (IsLocalRing.closedPoint F))
  have hg : ∀ t, y t ∈ trivializationOpen L.obj (s j) := fun t ↦ by
    rwa [Subsingleton.elim t (IsLocalRing.closedPoint F)]
  have himage : (linearSystemMap p hs) (y (IsLocalRing.closedPoint F)) =
      (pointMap p s y j hg) (IsLocalRing.closedPoint F) := by
    rw [← comp_linearSystemMap p hs y j hg, Scheme.Hom.comp_apply]
  have hpre : (pointMap p s y j hg) ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading K n)
      (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) =
      (Spec (CommRingCat.of F)).basicOpen
        (chartRingHom p s y j (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i)) := by
    rw [pointMap, chartMap_preimage_basicOpen _ _ (projectiveSpace_X_mem K n j)
      one_pos (linearPolynomial_mem_grading c) one_pos]
  have hmem : ∀ (x : ProjectiveSpace K n) (h : ProjectiveCoordinateRing K n),
      h ∈ x.asHomogeneousIdeal ↔ x ∉ Proj.basicOpen (projectiveSpaceGrading K n) h :=
    fun _ _ ↦ not_not.symm
  have hpt : (pointMap p s y j hg) (IsLocalRing.closedPoint F) ∈
        Proj.basicOpen (projectiveSpaceGrading K n)
          (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) ↔
      IsLocalRing.closedPoint F ∈ (Spec (CommRingCat.of F)).basicOpen
        (chartRingHom p s y j (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i)) := by
    rw [← hpre]
    rfl
  rw [vanishesAlong_iff_sectionRatio_eq_zero hg, sectionRatio_linComb_eq_chartRingHom p s hg c,
    himage, hmem, hpt]
  constructor
  · intro h hmem
    rw [h, Scheme.basicOpen_zero] at hmem
    exact hmem
  · intro h
    apply AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot
    rw [eq_bot_iff]
    intro t ht
    rw [Subsingleton.elim t (IsLocalRing.closedPoint F)] at ht
    exact (h ht).elim

end Langlands.AlgebraicGeometry.LinearSystem
