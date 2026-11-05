import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Analysis.Local.NormalSubgroupModularCharacter

/-! # The ambient modular character on actual norm-one adelic points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Restriction of the actual full adelic modular character to norm-one points. -/
def normOneAmbientModularCharacter : normOneSubgroup F G →* ℝ≥0 :=
  (modularCharacter (G := AdelicGroupPoints F G)).comp (normOneSubgroup F G).subtype

/-- The restricted ambient character is the intrinsic subgroup modular character. -/
theorem normOneAmbientModularCharacter_eq (g : normOneSubgroup F G) :
    normOneAmbientModularCharacter F G g = modularCharacter g := by
  let H := normOneSubgroup F G
  let _ : MeasurableSpace (Langlands.QuotientIntegration.LeftQuotient H) := borel _
  let _ : BorelSpace (Langlands.QuotientIntegration.LeftQuotient H) := ⟨rfl⟩
  let _ : MeasurableSpace (AdelicGroupPoints F G ⧸ H) := borel _
  let _ : BorelSpace (AdelicGroupPoints F G ⧸ H) := ⟨rfl⟩
  exact (Langlands.QuotientIntegration.modularCharacter_normalSubgroup H
    (isClosed_normOneSubgroup F G) g).symm

/-- A character-norm formula makes the restricted ambient modular character trivial. -/
theorem normOneAmbientModularCharacter_eq_one_of_characterNorm
    (χ : AlgebraicCharacter F G)
    (hχ : ∀ g : AdelicGroupPoints F G,
      modularCharacter g = (characterNorm F G χ g : ℝ≥0))
    (g : normOneSubgroup F G) :
    normOneAmbientModularCharacter F G g = 1 := by
  change modularCharacter (g : AdelicGroupPoints F G) = 1
  rw [hχ, (mem_normOneSubgroup F G _).mp g.property χ]
  rfl

/-- The same formula kills the intrinsic modular character of actual norm-one points. -/
theorem modularCharacter_normOneSubgroup_eq_one_of_characterNorm
    (χ : AlgebraicCharacter F G)
    (hχ : ∀ g : AdelicGroupPoints F G,
      modularCharacter g = (characterNorm F G χ g : ℝ≥0))
    (g : normOneSubgroup F G) :
    modularCharacter g = 1 := by
  rw [← normOneAmbientModularCharacter_eq F G g]
  exact normOneAmbientModularCharacter_eq_one_of_characterNorm F G χ hχ g

/-- A genuine ambient character-norm comparison implies right invariance of the fixed
Haar measure on the actual norm-one subgroup. -/
theorem normOneHaarRightInvariant_of_characterNorm
    (χ : AlgebraicCharacter F G)
    (hχ : ∀ g : AdelicGroupPoints F G,
      modularCharacter g = (characterNorm F G χ g : ℝ≥0)) :
    (haar : Measure (normOneSubgroup F G)).IsMulRightInvariant := by
  constructor
  intro g
  rw [map_right_mul_eq_modularCharacterFun_smul,
    show modularCharacterFun g = 1 from
      modularCharacter_normOneSubgroup_eq_one_of_characterNorm F G χ hχ g,
    one_smul]

end Langlands.Global.AdelicGroupPoints
