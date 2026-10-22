import Langlands.Weil.Representation.Basic
import Langlands.Representation.Twist.Definitions
import Mathlib.LinearAlgebra.Determinant

/-! # Determinant characters and their scalar representations -/

noncomputable section

universe uK uG uV uW

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- The actual determinant homomorphism, valued in units because each action is invertible. -/
def determinantCharacter (A : FiniteRepresentation.{uK, uG, uV} K G) : G →* Kˣ :=
  (Units.map (LinearMap.det : Module.End K A →* K)).comp A.representation.asGroupHom

/-- The scalar determinant character evaluates to the determinant of the action operator. -/
theorem determinantCharacter_apply (A : FiniteRepresentation.{uK, uG, uV} K G) (g : G) :
    (determinantCharacter A g : K) = LinearMap.det (A.representation g) := rfl

/-- Genuine representation equivalence preserves the determinant character. -/
theorem determinantCharacter_eq {A : FiniteRepresentation.{uK, uG, uV} K G}
    {B : FiniteRepresentation.{uK, uG, uW} K G} (e : Equiv A B) :
    determinantCharacter A = determinantCharacter B := by
  ext g
  change LinearMap.det (A.representation g) = LinearMap.det (B.representation g)
  have hc : e.toLinearMap ∘ₗ A.representation g ∘ₗ e.symm.toLinearMap =
      B.representation g := by
    ext b
    simpa using Representation.IntertwiningMap.isIntertwining _ _
      e.toIntertwiningMap g (e.symm b)
  rw [← LinearMap.det_conj (A.representation g) e.toLinearEquiv]
  exact congrArg LinearMap.det hc

/-- Determinant characters descend to genuine isomorphism classes. -/
def determinantCharacterClass : IsomorphismClasses.{uK, uG, uV} K G → (G →* Kˣ) :=
  Quotient.lift determinantCharacter (fun _ _ ⟨e⟩ => determinantCharacter_eq e)

/-- The determinant representation realized on the scalar line `K`. -/
def determinant (A : FiniteRepresentation.{uK, uG, uV} K G) :
    FiniteRepresentation.{uK, uG, uK} K G :=
  of (Langlands.characterRepresentation (determinantCharacter A))

/-- The scalar determinant representation has rank one, including for rank-zero inputs. -/
theorem rank_determinant (A : FiniteRepresentation.{uK, uG, uV} K G) :
    (determinant A).rank = 1 := by
  change Module.finrank K K = 1
  exact Module.finrank_self K

/-- Equivalent representations have equivalent scalar determinant representations. -/
def determinantEquiv {A : FiniteRepresentation.{uK, uG, uV} K G}
    {B : FiniteRepresentation.{uK, uG, uW} K G} (e : Equiv A B) :
    Equiv (determinant A) (determinant B) := by
  unfold determinant
  rw [determinantCharacter_eq e]
  exact Representation.Equiv.refl _

/-- Determinant on genuine isomorphism classes, with target the scalar carrier universe. -/
def determinantClass : IsomorphismClasses.{uK, uG, uV} K G →
    IsomorphismClasses.{uK, uG, uK} K G :=
  Quotient.map determinant (fun _ _ ⟨e⟩ => ⟨determinantEquiv e⟩)

end Langlands.FiniteRepresentation
