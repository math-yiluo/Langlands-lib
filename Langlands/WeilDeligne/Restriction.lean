import Langlands.WeilDeligne.Basic
import Langlands.Weil.Representation.Restriction

/-!
# Restriction of Weil–Deligne pairs

The character is pulled back along the same group homomorphism as the action.
The carrier and nilpotent monodromy are unchanged.
-/

noncomputable section

universe uK uG uH uV uW

open CategoryTheory

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} {G : Type uG} {H : Type uH}
  [Field K] [Group G] [Group H] {ν : G →* Kˣ}

/-- Restrict a pair along an actual group homomorphism, with pulled-back norm character. -/
def restrict (φ : H →* G) (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    WeilDeligneRepresentation.{uK, uH, uV} K H (ν.comp φ) where
  toFiniteRepresentation := FiniteRepresentation.restrict φ A.toFiniteRepresentation
  monodromy := A.monodromy
  nilpotent := A.nilpotent
  covariance h := by
    change A.representation (φ h) * A.monodromy *
      A.representation (φ h⁻¹) = (ν (φ h) : K) • A.monodromy
    rw [map_inv]
    exact A.covariance (φ h)

/-- The same linear map defines a morphism after restricting both pairs. -/
def restrictMap (φ : H →* G)
    {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (f : Hom A B) :
    Hom (restrict φ A) (restrict φ B) where
  intertwiner := ⟨f.intertwiner.toLinearMap, fun h => f.intertwiner.isIntertwining' (φ h)⟩
  comm_monodromy := f.comm_monodromy

/-- Restriction is a functor between categories with the corresponding norm characters. -/
def restrictFunctor (φ : H →* G) :
    WeilDeligneRepresentation.{uK, uG, uV} K G ν ⥤
      WeilDeligneRepresentation.{uK, uH, uV} K H (ν.comp φ) where
  obj := restrict φ
  map := restrictMap φ
  map_id _ := by apply Hom.ext; rfl
  map_comp _ _ := by apply Hom.ext; rfl

/-- Restriction of actual pair equivalences. -/
def restrictEquiv (φ : H →* G)
    {A B : WeilDeligneRepresentation.{uK, uG, uV} K G ν} (e : Equiv A B) :
    Equiv (restrict φ A) (restrict φ B) :=
  Equiv.ofIso ((restrictFunctor φ).mapIso e.toIso)

/-- The well-defined restriction operation on genuine pair isomorphism classes. -/
def restrictClass (φ : H →* G) :
    IsomorphismClasses.{uK, uG, uV} K G ν →
      IsomorphismClasses.{uK, uH, uV} K H (ν.comp φ) :=
  Quotient.map (restrict φ) (fun _ _ ⟨e⟩ => ⟨restrictEquiv φ e⟩)

end Langlands.WeilDeligneRepresentation
