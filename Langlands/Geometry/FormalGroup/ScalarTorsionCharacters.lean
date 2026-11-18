import Langlands.Geometry.FormalGroup.ScalarTorsionSchemes
import Langlands.GroupScheme.Cartier.Characters

/-! # Relative Cartier characters of scalar-power torsion -/

noncomputable section
universe u v

namespace Langlands.FormalGroup.ModuleLaw.IsPiDivisible
open CategoryTheory Opposite AlgebraicGeometry
open Langlands.GroupScheme

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]
variable {M : ModuleLaw O R σ} {π : O} (hM : M.IsPiDivisible π)

/-- The relative Cartier character presheaf of the actual scalar-power kernel. -/
abbrev torsionCharacters (n : ℕ) :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ AddCommGrpCat.{v} :=
  Cartier.characters (hM.torsionKernelModel n).commGroupScheme

/-- The inverse character system restricts along the primal kernel inclusions. -/
def torsionCharacterTower :
    ℕᵒᵖ ⥤ ((Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ AddCommGrpCat.{v}) :=
  hM.torsionSchemeInclusions.op ⋙ Cartier.relativeHomBifunctor (Gm (Spec (CommRingCat.of R)))

/-- The direct character system pulls back along the primal multiplication transitions. -/
def torsionCharacterInclusions :
    ℕ ⥤ ((Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ AddCommGrpCat.{v}) :=
  opOp ℕ ⋙ hM.torsionSchemeTower.op ⋙
    Cartier.relativeHomBifunctor (Gm (Spec (CommRingCat.of R)))

variable {m n : ℕ} (i : m ⟶ n) {T : Over (Spec (CommRingCat.of R))}

/-- Restricting a character along an inclusion pairs against the included point. -/
theorem evaluation_torsionCharacterTower_map (χ : (hM.torsionCharacters n).obj (op T))
    (x : T ⟶ (hM.torsionKernelModel m).commGroupScheme.X) :
    Cartier.evaluation ((hM.torsionCharacterTower.map i.op).app (op T) χ) x =
      Cartier.evaluation χ (x ≫ (hM.torsionSchemeInclusions.map i).toMul.hom.hom) :=
  Cartier.evaluation_precompose (hM.torsionSchemeInclusions.map i) χ x

/-- Pulling back a character along multiplication pairs against the multiplied point. -/
theorem evaluation_torsionCharacterInclusions_map (χ : (hM.torsionCharacters m).obj (op T))
    (x : T ⟶ (hM.torsionKernelModel n).commGroupScheme.X) :
    Cartier.evaluation ((hM.torsionCharacterInclusions.map i).app (op T) χ) x =
      Cartier.evaluation χ (x ≫ (hM.torsionSchemeTower.map i.op).toMul.hom.hom) :=
  Cartier.evaluation_precompose (hM.torsionSchemeTower.map i.op) χ x

end Langlands.FormalGroup.ModuleLaw.IsPiDivisible
