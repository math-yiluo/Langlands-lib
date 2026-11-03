import Langlands.GroupScheme.Rational.StandardLeviPointHomeomorph
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.Representation.Plancherel.RationalCharacterTopology

/-! # Actual rational norm characters on the literal standard Levi subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology Plancherel

variable {F : Type u} [Field F] [TopologicalSpace F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν))

local instance instRationalLeviNormTopology1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance instRationalLeviNormTopology2 :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance instRationalLeviNormTopology3 : IsAffine (Standard.leviScheme i ν (rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance instRationalLeviNormTopology4 : TopologicalSpace (rationalPoints G) := pointTopology
local instance instRationalLeviNormTopology5 :
    TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (rootSet i ν I)).X

/-- The actual standard Levi scheme and the literal simple-root-indexed Levi
subgroup have the same canonical multiplicative point topology. -/
def leviRationalPointHomeomorph :
    rationalPoints (Standard.leviScheme i ν (rootSet i ν I)) ≃ₜ* levi i ν I :=
  standardLeviRationalPointsHomeomorph i ν (rootSet i ν I)
    (Standard.leviHom i ν (rootSet i ν I))
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
    (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))

@[simp]
theorem leviRationalPointHomeomorph_toMulEquiv :
    (leviRationalPointHomeomorph i ν I).toMulEquiv =
      standardLeviRationalPointsEquiv i ν (rootSet i ν I)
        (Standard.leviHom i ν (rootSet i ν I))
        (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I)) :=
  standardLeviRationalPointsHomeomorph_toMulEquiv _ _ _ _ _ _

@[simp]
theorem leviRationalPointHomeomorph_apply_coe
    (m : rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :
    (leviRationalPointHomeomorph i ν I m : rationalPoints G) =
      rationalPoints.map (Standard.leviHom i ν (rootSet i ν I)) m := rfl

section LocalField

variable [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- Pull the actual continuous rational norm on the standard Levi scheme back
through the inverse canonical point homeomorphism. -/
def leviRationalNormContinuousCharacter
    (χ : rationalCharacters (Standard.leviScheme i ν (rootSet i ν I))) :
    levi i ν I →ₜ* ℝ≥0ˣ where
  toMonoidHom :=
    (rationalNormContinuousCharacter (Standard.leviScheme i ν (rootSet i ν I)) χ).toMonoidHom.comp
      (leviRationalPointHomeomorph i ν I).symm.toMulEquiv.toMonoidHom
  continuous_toFun :=
    (rationalNormContinuousCharacter (Standard.leviScheme i ν (rootSet i ν I)) χ).continuous.comp
      (leviRationalPointHomeomorph i ν I).symm.continuous

@[simp]
theorem leviRationalNormContinuousCharacter_apply
    (χ : rationalCharacters (Standard.leviScheme i ν (rootSet i ν I)))
    (m : levi i ν I) :
    leviRationalNormContinuousCharacter i ν I χ m =
      fieldNormUnits F
        (rationalCharacterEval χ ((leviRationalPointHomeomorph i ν I).symm m)) := rfl

@[simp]
theorem leviRationalNormContinuousCharacter_apply_points
    (χ : rationalCharacters (Standard.leviScheme i ν (rootSet i ν I)))
    (m : rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :
    leviRationalNormContinuousCharacter i ν I χ (leviRationalPointHomeomorph i ν I m) =
      fieldNormUnits F (rationalCharacterEval χ m) := by
  rw [leviRationalNormContinuousCharacter_apply]
  congr 2
  exact (leviRationalPointHomeomorph i ν I).symm_apply_apply m

/-- The full family indexed by all actual rational characters of the same
standard Levi scheme, as homomorphisms on the literal subgroup. -/
def leviRationalNormCharacters :
    rationalCharacters (Standard.leviScheme i ν (rootSet i ν I)) →
      (levi i ν I →* ℝ≥0ˣ) :=
  fun χ => (leviRationalNormContinuousCharacter i ν I χ).toMonoidHom

theorem continuous_leviRationalNormCharacters
    (χ : rationalCharacters (Standard.leviScheme i ν (rootSet i ν I))) :
    Continuous (leviRationalNormCharacters i ν I χ) :=
  (leviRationalNormContinuousCharacter i ν I χ).continuous

@[simp]
theorem leviRationalNormCharacters_apply_points
    (χ : rationalCharacters (Standard.leviScheme i ν (rootSet i ν I)))
    (m : rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :
    leviRationalNormCharacters i ν I χ (leviRationalPointHomeomorph i ν I m) =
      (rationalNormCharacters (Standard.leviScheme i ν (rootSet i ν I)) χ).toMul m :=
  leviRationalNormContinuousCharacter_apply_points i ν I χ m

end LocalField

end Langlands.Aubert.General.RationalPointFamily
