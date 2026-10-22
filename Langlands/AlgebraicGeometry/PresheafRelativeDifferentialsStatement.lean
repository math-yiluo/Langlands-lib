import Langlands.AlgebraicGeometry.PresheafRelativeDifferentials

/-!
# Universality of the constructed relative derivation

The proposition that the derivation `Langlands.PresheafDifferentials.derivation φ`
is universal among `φ`-derivations into presheaves of `R`-modules at universe `u`.
-/

universe u v₁ v₂ u₁ u₂

open CategoryTheory

namespace Langlands.PresheafDifferentials

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}}

/-- The constructed derivation `derivation φ : (relativeDifferentials φ).Derivation φ`
admits Mathlib's universal structure `PresheafOfModulesOfCommRing.Derivation.Universal`. -/
def DerivationUniversalStatement (φ : S ⟶ F.op ⋙ R) : Prop :=
  Nonempty (derivation φ).Universal

end Langlands.PresheafDifferentials
