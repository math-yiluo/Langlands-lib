import Langlands.Weil.Representation.Basic
import Langlands.Representation.Dual.Definitions
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Algebraic duality for finite-dimensional representations -/

noncomputable section

universe uK uG uV uW

open CategoryTheory Opposite

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- The full algebraic dual on the actual dual vector space. -/
def dual (A : FiniteRepresentation.{uK, uG, uV} K G) :
    FiniteRepresentation.{uK, uG, max uK uV} K G :=
  of A.representation.dual

/-- The algebraic dual is contravariant, using the published dual intertwiner. -/
def dualFunctor : (FiniteRepresentation.{uK, uG, uV} K G)ᵒᵖ ⥤
    FiniteRepresentation.{uK, uG, max uK uV} K G where
  obj A := dual A.unop
  map f := (homEquiv _ _).symm (Langlands.dualIntertwining (homEquiv _ _ f.unop))
  map_id _ := by
    apply (homEquiv _ _).injective
    ext ℓ
    rfl
  map_comp _ _ := by
    apply (homEquiv _ _).injective
    ext ℓ
    rfl

/-- Duality reverses genuine representation equivalences, across carrier universes. -/
def dualEquiv {A : FiniteRepresentation.{uK, uG, uV} K G}
    {B : FiniteRepresentation.{uK, uG, uW} K G} (e : Equiv A B) :
    Equiv (dual B) (dual A) :=
  Langlands.dualEquiv e

/-- Duality is well-defined on genuine isomorphism classes. -/
def dualClass : IsomorphismClasses.{uK, uG, uV} K G →
    IsomorphismClasses.{uK, uG, max uK uV} K G :=
  Quotient.map dual (fun _ _ ⟨e⟩ => ⟨(dualEquiv e).symm⟩)

end Langlands.FiniteRepresentation
