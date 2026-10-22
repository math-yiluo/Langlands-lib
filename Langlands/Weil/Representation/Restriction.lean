import Langlands.Weil.Representation.Basic
import Mathlib.RepresentationTheory.Rep.Res

/-!
# Restriction of finite-dimensional representations

Restriction uses Mathlib's precomposition functor and keeps the original carrier.
-/

noncomputable section

universe uK uG uH uV

open CategoryTheory

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} {H : Type uH}
  [Field K] [Monoid G] [Monoid H]

/-- Restriction along a monoid homomorphism on the original vector space. -/
def restrict (φ : H →* G) (A : FiniteRepresentation.{uK, uG, uV} K G) :
    FiniteRepresentation.{uK, uH, uV} K H :=
  ⟨Rep.res φ A.obj, inferInstanceAs (Module.Finite K A)⟩

/-- Restriction on objects and intertwiners is Mathlib's restriction functor. -/
def restrictFunctor (φ : H →* G) :
    FiniteRepresentation.{uK, uG, uV} K G ⥤ FiniteRepresentation.{uK, uH, uV} K H where
  obj := restrict φ
  map f := ObjectProperty.homMk (Rep.resMap φ f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restriction of actual representation equivalences. -/
def restrictEquiv (φ : H →* G) {A B : FiniteRepresentation.{uK, uG, uV} K G}
    (e : Equiv A B) : Equiv (restrict φ A) (restrict φ B) :=
  equivOfIso ((restrictFunctor φ).mapIso (isoOfEquiv e))

/-- The restriction operation on genuine isomorphism classes. -/
def restrictClass (φ : H →* G) :
    IsomorphismClasses.{uK, uG, uV} K G → IsomorphismClasses.{uK, uH, uV} K H :=
  Quotient.map (restrict φ) (fun _ _ ⟨e⟩ => ⟨restrictEquiv φ e⟩)

end Langlands.FiniteRepresentation
