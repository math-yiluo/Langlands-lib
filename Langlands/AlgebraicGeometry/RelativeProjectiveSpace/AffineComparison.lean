import Langlands.AlgebraicGeometry.RelativeProjectiveSpace
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X

/-! # Comparison of relative projective space over an affine base with polynomial Proj -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

private abbrev integralAlgebra (R : Type u) [CommRing R] : Algebra (ULift.{u} ℤ) R :=
  ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom).toAlgebra

private lemma toSpec_eq (R : Type u) [CommRing R] (n : ℕ) :
    projectiveSpaceToSpec R n = ProjSpace.π R n := by
  congr 1

/-- The map from polynomial projective space to its integral model. -/
def polynomialToIntegral (R : Type u) [CommRing R] (n : ℕ) :
    ProjectiveSpace R n ⟶ ProjectiveSpace (ULift.{u} ℤ) n :=
  letI := integralAlgebra R
  ProjSpace.map (ULift.{u} ℤ) R n

/-- Homogeneous coordinate charts pull back to the corresponding polynomial charts. -/
lemma polynomialToIntegral_preimage_coordinateOpen (R : Type u) [CommRing R] (n : ℕ)
    (i : Fin (n + 1)) :
    (polynomialToIntegral R n) ⁻¹ᵁ projectiveSpaceCoordinateOpen (ULift.{u} ℤ) n i =
      projectiveSpaceCoordinateOpen R n i := by
  let := integralAlgebra R
  exact ProjSpace.map_preimage_basicOpen_X (ULift.{u} ℤ) R n i

set_option backward.isDefEq.respectTransparency false in
private lemma isPullback_polynomialToIntegral (R : Type u) [CommRing R] (n : ℕ) :
    IsPullback (projectiveSpaceToSpec R n) (polynomialToIntegral R n)
      (terminal.from (Spec (CommRingCat.of R)))
      (terminal.from (ProjectiveSpace (ULift.{u} ℤ) n)) := by
  let := integralAlgebra R
  have h := (ProjSpace.isPullback_map (ULift.{u} ℤ) R n).flip
  rw [← toSpec_eq R n, ← toSpec_eq (ULift.{u} ℤ) n] at h
  exact h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal)
    (by simp) (by simp [polynomialToIntegral])
    (by apply terminalIsTerminal.hom_ext) (by apply terminalIsTerminal.hom_ext)

/-- Polynomial projective space over `R` is canonically relative projective space over `Spec R`. -/
def affineComparisonIso (R : Type u) [CommRing R] (n : ℕ) :
    ProjectiveSpace R n ≅ RelativeProjectiveSpace (Spec (CommRingCat.of R)) n :=
  (isPullback_polynomialToIntegral R n).isoPullback

@[reassoc (attr := simp)]
lemma affineComparisonIso_hom_toBase (R : Type u) [CommRing R] (n : ℕ) :
    (affineComparisonIso R n).hom ≫ toBase (Spec (CommRingCat.of R)) n =
      projectiveSpaceToSpec R n :=
  (isPullback_polynomialToIntegral R n).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma affineComparisonIso_hom_toIntegral (R : Type u) [CommRing R] (n : ℕ) :
    (affineComparisonIso R n).hom ≫ toIntegral (Spec (CommRingCat.of R)) n =
      polynomialToIntegral R n :=
  (isPullback_polynomialToIntegral R n).isoPullback_hom_snd

@[reassoc (attr := simp)]
lemma affineComparisonIso_inv_toSpec (R : Type u) [CommRing R] (n : ℕ) :
    (affineComparisonIso R n).inv ≫ projectiveSpaceToSpec R n =
      toBase (Spec (CommRingCat.of R)) n := by
  rw [← affineComparisonIso_hom_toBase, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma affineComparisonIso_inv_toIntegral (R : Type u) [CommRing R] (n : ℕ) :
    (affineComparisonIso R n).inv ≫ polynomialToIntegral R n =
      toIntegral (Spec (CommRingCat.of R)) n := by
  rw [← affineComparisonIso_hom_toIntegral, Iso.inv_hom_id_assoc]

/-- The comparison identifies each inverse-image integral chart with its polynomial chart. -/
lemma affineComparisonIso_hom_preimage_chart (R : Type u) [CommRing R] (n : ℕ)
    (i : Fin (n + 1)) :
    (affineComparisonIso R n).hom ⁻¹ᵁ
        ((toIntegral (Spec (CommRingCat.of R)) n) ⁻¹ᵁ
          projectiveSpaceCoordinateOpen (ULift.{u} ℤ) n i) =
      projectiveSpaceCoordinateOpen R n i := by
  rw [← Scheme.Hom.comp_preimage, affineComparisonIso_hom_toIntegral,
    polynomialToIntegral_preimage_coordinateOpen]

end Langlands.AlgebraicGeometry.RelativeProjectiveSpace
