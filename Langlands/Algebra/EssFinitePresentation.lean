import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.Defs

/-! # Essentially finitely presented algebras (Stacks Project, tag 00QM) -/

universe u v

namespace Langlands.Algebra

/-- Stacks Project, Definition 10.54.1 (tag 00QM): an `R`-algebra `S` is *essentially of finite
presentation* if `S` is a localization of a finitely presented `R`-algebra, where localization
means inverting an arbitrary multiplicatively closed subset.

Concretely: there are `n : ℕ`, a finitely generated ideal `I` of the polynomial ring
`MvPolynomial (Fin n) R`, a submonoid `M` of the quotient `MvPolynomial (Fin n) R ⧸ I`, and an
`R`-algebra isomorphism from the localization of that quotient at `M` onto `S`. The finitely
presented algebra is taken in its standard form, so it lives in the universe of `R` and the
predicate makes sense for `R : Type u` and `S : Type v` in independent universes. The
localization map need not be injective. -/
def EssFinitePresentation (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    Prop :=
  ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)), I.FG ∧
    ∃ M : Submonoid (MvPolynomial (Fin n) R ⧸ I), Nonempty (Localization M ≃ₐ[R] S)

end Langlands.Algebra
