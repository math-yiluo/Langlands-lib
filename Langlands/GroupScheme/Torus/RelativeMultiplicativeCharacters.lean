import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeLocality
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.FppfRelativeTorusDescent
import Langlands.GroupScheme.Cartier.Characters

/-! # Actual relative characters of groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeMultiplicativeType

variable {S S' : Scheme.{u}} {H : GroupScheme S}

/-- Making the commutative law explicit commutes with arbitrary base change. -/
@[simp]
theorem IsMultiplicativeType.commGroupScheme_baseChange
    (hH : IsMultiplicativeType H) (b : S' ⟶ S) :
    (hH.baseChange b).commGroupScheme =
      (CommGroupScheme.baseChange b).obj hH.commGroupScheme := rfl

/-- The actual relative character presheaf of a group of multiplicative type. -/
def IsMultiplicativeType.characters (hH : IsMultiplicativeType H) :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  Cartier.characters hH.commGroupScheme

/-- Its values are canonically actual homomorphisms from `H_T` to `Gm_T`. -/
def IsMultiplicativeType.characterHomEquiv (hH : IsMultiplicativeType H)
    (T : Over S) :
    hH.characters.obj (.op T) ≃+
      Cartier.CharacterHom hH.commGroupScheme T :=
  Cartier.characterHomEquiv hH.commGroupScheme T

/-- Restriction is the published pullback operation on actual character homomorphisms. -/
theorem IsMultiplicativeType.characterHomEquiv_restrict
    (hH : IsMultiplicativeType H) {T T' : Over S} (a : T' ⟶ T)
    (χ : hH.characters.obj (.op T)) :
    hH.characterHomEquiv T' (hH.characters.map a.op χ) =
      Cartier.characterHomRestrict hH.commGroupScheme a
        (hH.characterHomEquiv T χ) :=
  Cartier.characterHomEquiv_restrict hH.commGroupScheme a χ

end Langlands.GroupScheme.RelativeMultiplicativeType
