import Langlands.GroupScheme.Rational.GeneralLinearCharacterSchemes
import Mathlib.Algebra.Polynomial.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u}) [IsDomain R]

/-- A field containing the GL coordinate algebra and a transcendental element. -/
abbrev CharacterLargeField := FractionRing (Polynomial (CoordinateRing n R))

/-- The faithful map from GL coordinates to the enlarged generic field. -/
def characterLargeFieldMap : CoordinateRing n R →ₐ[R] CharacterLargeField n R :=
  IsScalarTower.toAlgHom R (CoordinateRing n R) (CharacterLargeField n R)

omit [IsDomain R] in
theorem characterLargeFieldMap_injective : Function.Injective (characterLargeFieldMap n R) := by
  exact (IsFractionRing.injective (Polynomial (CoordinateRing n R))
    (CharacterLargeField n R)).comp Polynomial.C_injective

theorem characterLargeField_has_scalingElement :
    ∃ s : CharacterLargeField n R, s ≠ 0 ∧ s ≠ 1 := by
  let P := Polynomial (CoordinateRing n R)
  let j := @algebraMap P (FractionRing P)
    (inferInstance : CommSemiring P) (inferInstance : Semiring (FractionRing P)) inferInstance
  let s : CharacterLargeField n R :=
    j (Polynomial.X : P)
  refine ⟨s, ?_, ?_⟩
  · intro h
    apply Polynomial.X_ne_zero (R := CoordinateRing n R)
    exact (IsFractionRing.injective (Polynomial (CoordinateRing n R)) (CharacterLargeField n R))
      (h.trans (map_zero (algebraMap (Polynomial (CoordinateRing n R))
        (CharacterLargeField n R))).symm)
  · intro h
    have hX : (Polynomial.X : Polynomial (CoordinateRing n R)) = 1 :=
      (IsFractionRing.injective (Polynomial (CoordinateRing n R)) (CharacterLargeField n R))
        (h.trans (map_one (algebraMap (Polynomial (CoordinateRing n R))
          (CharacterLargeField n R))).symm)
    exact Polynomial.X_ne_C (1 : CoordinateRing n R) (by simpa using hX)

variable {n R}

omit [IsDomain R] in
/-- Equality of characters on affine matrices detects equality of scheme morphisms. -/
theorem characterOnAffineMatrices_ext
    {φ ψ : groupScheme n R ⟶ (Gm (Spec R)).toGrp}
    (h : ∀ (A : CommAlgCat.{u} R) (g : GL n A),
      characterOnAffineMatrices φ A g = characterOnAffineMatrices ψ A g) : φ = ψ := by
  have hid : affinePointsEquiv n R (coordinateAlgebra n R) (𝟙 _) = universal n R := by
    have hh := affinePointsEquiv_map (n := n) (R := R)
      (coordinateAlgebra n R) (𝟙 (coordinateAlgebra n R))
    change affinePointsEquiv n R (coordinateAlgebra n R)
      ((algSpec R).map (𝟙 (op (coordinateAlgebra n R)))) = universal n R at hh
    rwa [CategoryTheory.Functor.map_id] at hh
  have hi : (affinePointsEquiv n R (coordinateAlgebra n R)).symm (universal n R) = 𝟙 _ := by
    rw [← hid, MulEquiv.symm_apply_apply]
  have he := h (coordinateAlgebra n R) (universal n R)
  change Gm.affinePointsEquiv ((algSpec R).obj (op (coordinateAlgebra n R))).hom
      ((affinePointsEquiv n R (coordinateAlgebra n R)).symm (universal n R) ≫ φ.hom.hom) =
    Gm.affinePointsEquiv ((algSpec R).obj (op (coordinateAlgebra n R))).hom
      ((affinePointsEquiv n R (coordinateAlgebra n R)).symm (universal n R) ≫ ψ.hom.hom) at he
  rw [hi] at he
  have hf :=
    (Gm.affinePointsEquiv ((algSpec R).obj (op (coordinateAlgebra n R))).hom).injective he
  change (𝟙 (groupScheme n R).X) ≫ φ.hom.hom =
    (𝟙 (groupScheme n R).X) ≫ ψ.hom.hom at hf
  simp only [Category.id_comp] at hf
  exact hom_ext_points (fun _ _ => by rw [hf])

/-- The integer exponent detected on a specified coordinate cocharacter. -/
def coordinateCharacterExponent (φ : groupScheme n R ⟶ (Gm (Spec R)).toGrp) (i : n) : ℤ :=
  Classical.choose (Gm.exists_eq_multiplication R (coordinateDiagonalHom n R i ≫ φ))

theorem coordinateCharacterExponent_spec
    (φ : groupScheme n R ⟶ (Gm (Spec R)).toGrp) (i : n) :
    coordinateDiagonalHom n R i ≫ φ =
      multiplication (Gm (Spec R)).toGrp (coordinateCharacterExponent φ i) :=
  Classical.choose_spec (Gm.exists_eq_multiplication R (coordinateDiagonalHom n R i ≫ φ))

theorem characterOnAffineMatrices_field_power
    (φ : groupScheme n R ⟶ (Gm (Spec R)).toGrp) (i : n)
    (F : Type u) [Field F] [Algebra R F] (s : F) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (g : GL n F) :
    characterOnAffineMatrices φ (CommAlgCat.of R F) g =
      Matrix.GeneralLinearGroup.det g ^ coordinateCharacterExponent φ i := by
  rw [fieldCharacter_determinantFactor (characterOnAffineMatrices φ (CommAlgCat.of R F))
    s hs0 hs1 i g]
  exact characterOnAffineMatrices_coordinate φ i _ (coordinateCharacterExponent_spec φ i)
    (CommAlgCat.of R F) _

theorem characterOnAffineMatrices_universal_power
    (φ : groupScheme n R ⟶ (Gm (Spec R)).toGrp) (i : n) :
    characterOnAffineMatrices φ (coordinateAlgebra n R) (universal n R) =
      Matrix.GeneralLinearGroup.det (universal n R) ^ coordinateCharacterExponent φ i := by
  let F := CharacterLargeField n R
  let f : coordinateAlgebra n R ⟶ CommAlgCat.of R F :=
    CommAlgCat.ofHom (characterLargeFieldMap n R)
  obtain ⟨s, hs0, hs1⟩ := characterLargeField_has_scalingElement n R
  apply Units.map_injective
    (f := (characterLargeFieldMap n R).toRingHom.toMonoidHom)
    (characterLargeFieldMap_injective n R)
  calc
    _ = characterOnAffineMatrices φ (CommAlgCat.of R F)
        (Matrix.GeneralLinearGroup.map f.hom.toRingHom (universal n R)) :=
      (characterOnAffineMatrices_naturality φ f (universal n R)).symm
    _ = Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map f.hom.toRingHom (universal n R)) ^
          coordinateCharacterExponent φ i :=
      characterOnAffineMatrices_field_power φ i F s hs0 hs1 _
    _ = _ := by rw [Matrix.GeneralLinearGroup.map_det, map_zpow]; rfl

/-- The value of every GL scheme character is one fixed integer power of the determinant,
over every test algebra, including nonreduced algebras. -/
theorem characterOnAffineMatrices_power
    (φ : groupScheme n R ⟶ (Gm (Spec R)).toGrp) (i : n)
    (A : CommAlgCat.{u} R) (g : GL n A) :
    characterOnAffineMatrices φ A g =
      Matrix.GeneralLinearGroup.det g ^ coordinateCharacterExponent φ i := by
  let f : coordinateAlgebra n R ⟶ A := CommAlgCat.ofHom (classify g)
  have hg : Matrix.GeneralLinearGroup.map f.hom.toRingHom (universal n R) = g :=
    point_classify g
  have h := characterOnAffineMatrices_naturality φ f (universal n R)
  rw [hg, characterOnAffineMatrices_universal_power φ i, map_zpow] at h
  have hd := Matrix.GeneralLinearGroup.map_det f.hom.toRingHom (universal n R)
  rw [hg] at hd
  change Matrix.GeneralLinearGroup.det g =
    Units.map f.hom.toRingHom.toMonoidHom (Matrix.GeneralLinearGroup.det (universal n R)) at hd
  rw [← hd] at h
  exact h

omit [IsDomain R] in
theorem characterOnAffineMatrices_empty [IsEmpty n]
    (φ : groupScheme n R ⟶ (Gm (Spec R)).toGrp)
    (A : CommAlgCat.{u} R) (g : GL n A) :
    characterOnAffineMatrices φ A g = 1 := by
  have hg : g = 1 := by
    apply Units.ext
    ext i
    exact isEmptyElim i
  rw [hg, map_one]

/-- Every actual GL character over a domain is a determinant power on all affine points. -/
theorem exists_characterOnAffineMatrices_power
    (φ : groupScheme n R ⟶ (Gm (Spec R)).toGrp) :
    ∃ m : ℤ, ∀ (A : CommAlgCat.{u} R) (g : GL n A),
      characterOnAffineMatrices φ A g = Matrix.GeneralLinearGroup.det g ^ m := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
      let := hn
      refine ⟨0, fun A g => ?_⟩
      rw [characterOnAffineMatrices_empty, zpow_zero]
  | inr hn =>
      obtain ⟨i⟩ := hn
      exact ⟨coordinateCharacterExponent φ i, characterOnAffineMatrices_power φ i⟩

end Langlands.GroupScheme.GeneralLinear
