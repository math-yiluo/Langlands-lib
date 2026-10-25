import Langlands.Algebra.EssFinitePresentation
import Mathlib.RingTheory.RingHomProperties

/-! # Localization construction and isomorphism transport for essential finite presentation -/

universe u v w

namespace Langlands.Algebra

/-- Derived transport facts for the published essential finite presentation predicate:
arbitrary localizations of finitely presented algebras satisfy it, and its ring-hom
interpretation respects source and target isomorphisms. This states the facts only. -/
def EssFinitePresentationTransportStatement : Prop :=
  (∀ (R : Type u) (A : Type v) (B : Type w)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [_root_.Algebra.FinitePresentation R A]
    (M : Submonoid A) [IsLocalization M B],
    EssFinitePresentation R B) ∧
  RingHom.RespectsIso
    (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) =>
      @EssFinitePresentation R S _ _ f.toAlgebra)

end Langlands.Algebra
