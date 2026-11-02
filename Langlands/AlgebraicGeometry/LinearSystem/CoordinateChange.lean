import Langlands.AlgebraicGeometry.LinearSystem.Morphism
import Langlands.AlgebraicGeometry.LinearSystem.ChartFunctoriality
import Langlands.AlgebraicGeometry.ProjectiveSpace.LinearAction

/-! # Linear changes of generating sections -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.ProjectiveSpace

namespace Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [CommRing K] {X T : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of K)) {L : LineBundle X} {n : ℕ}
  (s : Fin (n + 1) → GlobalSections L.obj)

/-- Apply a coordinate linear map to the ordered family of sections. -/
def linearChangeSections (f : (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K)) :
    Fin (n + 1) → GlobalSections L.obj :=
  fun i ↦ linComb p s (fun j ↦ f (Pi.single j 1) i)

/-- The identity coordinate map fixes the ordered sections. -/
@[simp]
lemma linearChangeSections_id : linearChangeSections p s LinearMap.id = s := by
  classical
  funext i
  simp [linearChangeSections, linComb, Pi.single_apply]

/-- Coordinate changes compose as their linear maps do. -/
lemma linearChangeSections_comp
    (f h : (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K)) :
    linearChangeSections p (linearChangeSections p s f) h =
      linearChangeSections p s (h.comp f) := by
  classical
  funext i
  have hcoeff (k : Fin (n + 1)) :
      (h.comp f) (Pi.single k 1) i =
        ∑ j, h (Pi.single j 1) i * f (Pi.single k 1) j := by
    have H := congrArg (fun v ↦ h v i)
      ((Pi.basisFun K (Fin (n + 1))).sum_repr (f (Pi.single k 1)))
    simpa [map_sum, map_smul, Finset.sum_apply, Pi.basisFun_apply, mul_comm] using H.symm
  simp only [linearChangeSections, linComb, Finset.smul_sum, ← mul_smul, ← map_mul]
  rw [Finset.sum_comm]
  simp_rw [hcoeff, map_sum, Finset.sum_smul]

/-- Applying an invertible change and then its inverse recovers every section. -/
@[simp]
lemma linearChangeSections_symm
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    linearChangeSections p (linearChangeSections p s e.toLinearMap) e.symm.toLinearMap = s := by
  rw [linearChangeSections_comp, LinearEquiv.symm_comp, linearChangeSections_id]

/-- An invertible coordinate change preserves generation at every scheme point. -/
lemma linearChangeSections_generate
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    ∀ x : X, ∃ j, x ∈ nonvanishingLocus L.obj (linearChangeSections p s e.toLinearMap j) := by
  classical
  intro x
  by_contra hx
  simp only [mem_nonvanishingLocus, not_exists, not_not] at hx
  obtain ⟨i, hi⟩ := hs x
  apply (mem_nonvanishingLocus L.obj (s i) x).mp hi
  rw [← linearChangeSections_symm p s e]
  change pullbackSection (X.fromSpecResidueField x) L.obj
    (∑ j, Scheme.Modules.scalarsFromBase p (e.symm (Pi.single j 1) i) •
      linearChangeSections p s e.toLinearMap j) = 0
  rw [pullbackSection_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [pullbackSection_smul]
  change _ • residueSection L.obj (linearChangeSections p s e.toLinearMap j) x = 0
  rw [hx j, smul_zero]

/-- Substitution of coordinate polynomials evaluates as the transformed sections. -/
lemma chartRingHom_comp_linearSubstitution
    (f : (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K))
    {g : T ⟶ X} {i : Fin (n + 1)}
    (hi : ∀ t, g t ∈ trivializationOpen L.obj (s i)) :
    (chartRingHom p s g i).comp (gradedLinearSubstitution K n f).toRingHom =
      MvPolynomial.eval₂Hom (Scheme.Modules.scalarsFromBase (g ≫ p))
        (fun j ↦ sectionRatio L g (linearChangeSections p s f j) (s i)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, GradedRingHom.coe_toRingHom,
      gradedLinearSubstitution_apply, linearSubstitution_C, chartRingHom_C,
      MvPolynomial.eval₂Hom_C]
  · intro j
    simp only [RingHom.comp_apply, GradedRingHom.coe_toRingHom,
      gradedLinearSubstitution_apply, linearSubstitution_X,
      linearFormPolynomialEquiv_coe, MvPolynomial.smul_eq_C_mul,
      map_sum, map_mul, chartRingHom_C, chartRingHom_X, MvPolynomial.eval₂Hom_X']
    exact (sectionRatio_linComb p s hi (fun k ↦ f (Pi.single k 1) j)).symm

/-- On two frame loci, the substituted evaluation differs by one homogeneous scalar. -/
lemma chartRingHom_linearChange_scale
    (f : (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K))
    {g : T ⟶ X} {i j : Fin (n + 1)}
    (hi : ∀ t, g t ∈ trivializationOpen L.obj (s i))
    (hj : ∀ t, g t ∈ trivializationOpen L.obj (linearChangeSections p s f j))
    (m : ℕ) (a : ProjectiveCoordinateRing K n)
    (ha : a ∈ projectiveSpaceGrading K n m) :
    ((chartRingHom p s g i).comp (gradedLinearSubstitution K n f).toRingHom) a =
      sectionRatio L g (linearChangeSections p s f j) (s i) ^ m *
        chartRingHom p (linearChangeSections p s f) g j a := by
  rw [chartRingHom_comp_linearSubstitution p s f hi]
  have hx : (fun k ↦ sectionRatio L g (linearChangeSections p s f k) (s i)) =
      fun k ↦ sectionRatio L g (linearChangeSections p s f j) (s i) *
        sectionRatio L g (linearChangeSections p s f k) (linearChangeSections p s f j) := by
    funext k
    rw [mul_comm, sectionRatio_mul hi hj]
  rw [hx]
  exact eval₂_mul_of_isHomogeneous _ _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mp ha)

/-- The chart morphism of the transformed sections is the original chart morphism
followed by the actual projective linear action. -/
lemma pointMap_linearChange
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    {g : T ⟶ X} {i j : Fin (n + 1)}
    (hi : ∀ t, g t ∈ trivializationOpen L.obj (s i))
    (hj : ∀ t, g t ∈ trivializationOpen L.obj (linearChangeSections p s e.toLinearMap j)) :
    pointMap p s g i hi ≫ linearAction K n e =
      pointMap p (linearChangeSections p s e.toLinearMap) g j hj := by
  let f := gradedLinearSubstitution K n e.toLinearMap
  have hu : IsUnit (chartRingHom p s g i (f (MvPolynomial.X j))) := by
    change IsUnit (((chartRingHom p s g i).comp f.toRingHom) (MvPolynomial.X j))
    rw [chartRingHom_comp_linearSubstitution p s e.toLinearMap hi,
      MvPolynomial.eval₂Hom_X']
    exact isUnit_sectionRatio hi hj
  unfold pointMap linearAction
  rw [chartMap_eq _ _ (projectiveSpace_X_mem K n i) one_pos
    (f.map_mem (projectiveSpace_X_mem K n j)) one_pos _ hu]
  rw [chartMap_comp_projMap _ _ f _ _ (projectiveSpace_X_mem K n j) one_pos hu]
  exact chartMap_eq_of_scale _ (chartRingHom p (linearChangeSections p s e.toLinearMap) g j)
    ((chartRingHom p s g i).comp f.toRingHom) (projectiveSpace_X_mem K n j)
    one_pos (isUnit_chartRingHom_X p _ hj) hu _
    (chartRingHom_linearChange_scale p s e.toLinearMap hi hj)

/-- Equality of the actual glued morphisms under an invertible coordinate change. -/
lemma linearSystemMap_linearChange_of_generate
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i))
    (ht : ∀ x : X, ∃ j, x ∈ nonvanishingLocus L.obj (linearChangeSections p s e.toLinearMap j)) :
    linearSystemMap p hs ≫ linearAction K n e = linearSystemMap p ht := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨i, hi⟩ := exists_mem_trivializationOpen hs x
  obtain ⟨j, hj⟩ := exists_mem_trivializationOpen ht x
  let U := trivializationOpen L.obj (s i) ⊓
    trivializationOpen L.obj (linearChangeSections p s e.toLinearMap j)
  have hi' : ∀ t, U.ι t ∈ trivializationOpen L.obj (s i) :=
    fun t ↦ (ι_mem U t).1
  have hj' : ∀ t, U.ι t ∈ trivializationOpen L.obj (linearChangeSections p s e.toLinearMap j) :=
    fun t ↦ (ι_mem U t).2
  refine ⟨U, ⟨hi, hj⟩, ?_⟩
  rw [← Category.assoc, comp_linearSystemMap p hs _ i hi',
    comp_linearSystemMap p ht _ j hj']
  exact pointMap_linearChange p s e hi' hj'

/-- Changing generating sections by an invertible coordinate map applies the
corresponding actual projective-space automorphism. -/
lemma linearSystemMap_linearChange
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    linearSystemMap p hs ≫ linearAction K n e =
      linearSystemMap p (linearChangeSections_generate p s e hs) :=
  linearSystemMap_linearChange_of_generate p s e hs (linearChangeSections_generate p s e hs)

end Langlands.AlgebraicGeometry.LinearSystem
