import Langlands.Weil.Representation.Basic
import Langlands.Representation.Twist.Definitions

/-! # Character twists of finite-dimensional representations -/

noncomputable section

universe uK uG uV uW

open CategoryTheory

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- Scalar character twisting retains the actual vector space. -/
def twist (χ : G →* Kˣ) (A : FiniteRepresentation.{uK, uG, uV} K G) :
    FiniteRepresentation.{uK, uG, uV} K G :=
  of (Langlands.twist χ A.representation)

/-- Twisting on the finite-representation category uses the published intertwiner map. -/
def twistFunctor (χ : G →* Kˣ) : FiniteRepresentation.{uK, uG, uV} K G ⥤
    FiniteRepresentation.{uK, uG, uV} K G where
  obj := twist χ
  map f := (homEquiv _ _).symm (Langlands.twistIntertwining χ (homEquiv _ _ f))
  map_id _ := by apply (homEquiv _ _).injective; rfl
  map_comp _ _ := by apply (homEquiv _ _).injective; rfl

/-- Twisting is fully faithful by cancellation of the common unit character. -/
def twistFullyFaithful (χ : G →* Kˣ) : (twistFunctor.{uK, uG, uV} χ).FullyFaithful where
  preimage f := (homEquiv _ _).symm (Langlands.untwistIntertwining χ (homEquiv _ _ f))
  map_preimage _ := by apply (homEquiv _ _).injective; rfl
  preimage_map _ := by apply (homEquiv _ _).injective; rfl

/-- Twisting retains the underlying genuine linear equivalence. -/
def twistEquiv (χ : G →* Kˣ) {A : FiniteRepresentation.{uK, uG, uV} K G}
    {B : FiniteRepresentation.{uK, uG, uW} K G} (e : Equiv A B) :
    Equiv (twist χ A) (twist χ B) :=
  Langlands.twistEquiv χ e

/-- Character twisting on genuine isomorphism classes. -/
def twistClass (χ : G →* Kˣ) : IsomorphismClasses.{uK, uG, uV} K G →
    IsomorphismClasses.{uK, uG, uV} K G :=
  Quotient.map (twist χ) (fun _ _ ⟨e⟩ => ⟨twistEquiv χ e⟩)

end Langlands.FiniteRepresentation
