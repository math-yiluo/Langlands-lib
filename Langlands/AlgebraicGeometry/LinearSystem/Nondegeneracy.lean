import Langlands.AlgebraicGeometry.LinearSystem.Morphism
import Langlands.AlgebraicGeometry.ProjectiveSpace.LinearForms
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Picard.TranslationInvariantH0VanishingProof

/-! # Nondegeneracy of a complete linear system on a reduced scheme -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.ProjectiveSpace
open Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [CommRing K] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of K)) {L : LineBundle X} {n : ℕ}
  (basis : Module.Basis (Fin (n + 1)) K ((relativeGlobalSections p).obj L.obj))

/-- Match each actual homogeneous linear polynomial with the section having
the same coefficients in the specified full section basis. -/
def basisHyperplaneSectionEquiv :
    projectiveSpaceGrading K n 1 ≃ₗ[K] (relativeGlobalSections p).obj L.obj :=
  (degreeOneBasis K n).equivFun.trans basis.equivFun.symm

/-- The matched section is the actual scalar combination of basis sections. -/
lemma basisHyperplaneSectionEquiv_eq_linComb (F : projectiveSpaceGrading K n 1) :
    (show GlobalSections L.obj from basisHyperplaneSectionEquiv p basis F) =
      linComb p (fun i ↦ basis i) ((degreeOneBasis K n).equivFun F) := by
  simp only [basisHyperplaneSectionEquiv, LinearEquiv.trans_apply,
    Module.Basis.equivFun_symm_apply]
  rfl

/-- The coefficients of a homogeneous linear polynomial recover that polynomial. -/
lemma degreeOneBasis_expansion (F : projectiveSpaceGrading K n 1) :
    (F : ProjectiveCoordinateRing K n) =
      ∑ i, MvPolynomial.C ((degreeOneBasis K n).equivFun F i) * MvPolynomial.X i := by
  have h := congrArg Subtype.val ((degreeOneBasis K n).sum_equivFun F).symm
  simpa only [Submodule.coe_sum, Submodule.coe_smul, degreeOneBasis_coe,
    MvPolynomial.smul_eq_C_mul] using h

variable {basis}

/-- A nonzero actual scalar combination of generating sections is not contained
in its corresponding hyperplane at every image point of a reduced scheme. -/
lemma exists_not_mem_hyperplane_of_linComb_ne_zero [IsReduced X]
    (s : Fin (n + 1) → GlobalSections L.obj)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i))
    (c : Fin (n + 1) → K) (hc : linComb p s c ≠ 0) :
    ∃ x : X, (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) ∉
      ((linearSystemMap p hs) x).asHomogeneousIdeal := by
  have hopen : trivializationOpen L.obj (linComb p s c) ≠ ⊥ := by
    intro h
    exact hc (L.eq_zero_of_trivializationOpen_eq_bot _ h)
  obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).mp hopen
  obtain ⟨j, hj⟩ := exists_mem_trivializationOpen hs x
  let g := X.fromSpecResidueField x
  have hg : ∀ t, g t ∈ trivializationOpen L.obj (s j) := by
    intro t
    simpa only [g, Scheme.fromSpecResidueField_apply] using hj
  have hr : sectionRatio L g (linComb p s c) (s j) ≠ 0 := by
    intro hz
    have hv := (vanishesAlong_iff_sectionRatio_eq_zero hg _).mpr hz
    have hn := (vanishesAlong_iff_not_mem g _).mp hv
    apply hn
    change X.fromSpecResidueField x _ ∈ trivializationOpen L.obj (linComb p s c)
    rw [Scheme.fromSpecResidueField_apply]
    exact hx
  have he : chartRingHom p s g j (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) ≠ 0 := by
    rwa [← sectionRatio_linComb_eq_chartRingHom p s hg c]
  have hB : (Spec (X.residueField x)).basicOpen
      (chartRingHom p s g j (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i)) ≠ ⊥ := by
    intro hb
    exact he (AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot _ hb)
  obtain ⟨t, ht⟩ := (Opens.ne_bot_iff_nonempty _).mp hB
  have hhom : (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) ∈
      projectiveSpaceGrading K n 1 := by
    apply Submodule.sum_mem
    intro i _
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      ((MvPolynomial.isHomogeneous_C (Fin (n + 1)) (c i)).mul
        (MvPolynomial.isHomogeneous_X K i))
  have ht' : t ∈ pointMap p s g j hg ⁻¹ᵁ
      Proj.basicOpen (projectiveSpaceGrading K n)
        (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) := by
    rw [pointMap, chartMap_preimage_basicOpen _ _ (projectiveSpace_X_mem K n j)
      one_pos hhom one_pos]
    exact ht
  have himage : (pointMap p s g j hg) t = (linearSystemMap p hs) x := by
    rw [← comp_linearSystemMap p hs g j hg, Scheme.Hom.comp_apply]
    simp only [g, Scheme.fromSpecResidueField_apply]
  refine ⟨x, ?_⟩
  change (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) ∉
    ((pointMap p s g j hg) t).asHomogeneousIdeal at ht'
  rwa [himage] at ht'

/-- A generating full section basis on a reduced scheme defines a projective
map whose image is not contained in any nonzero linear hyperplane. -/
theorem linearSystemMap_basis_nondegenerate [IsReduced X]
    (basis : Module.Basis (Fin (n + 1)) K ((relativeGlobalSections p).obj L.obj))
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (basis i))
    (F : projectiveSpaceGrading K n 1) (hF : (F : ProjectiveCoordinateRing K n) ≠ 0) :
    ∃ x : X, (F : ProjectiveCoordinateRing K n) ∉
      ((linearSystemMap p hs) x).asHomogeneousIdeal := by
  have hσ : linComb p (fun i ↦ basis i) ((degreeOneBasis K n).equivFun F) ≠ 0 := by
    rw [← basisHyperplaneSectionEquiv_eq_linComb p basis F]
    intro hz
    apply hF
    have hF0 : F = 0 := (basisHyperplaneSectionEquiv p basis).injective
      (hz.trans (map_zero _).symm)
    exact congrArg Subtype.val hF0
  simpa only [← degreeOneBasis_expansion] using
    exists_not_mem_hyperplane_of_linComb_ne_zero p (fun i ↦ basis i) hs _ hσ

end Langlands.AlgebraicGeometry.LinearSystem
