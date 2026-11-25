module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

set_option autoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section

universe u v w

/-!
# An étale local homomorphism is an isomorphism modulo powers of a principal ideal

Let `(R, m_R) → (S, m_S)` be a local homomorphism of local rings, with `S` the localization at a
prime `q` of an étale `R`-algebra `T`, and assume the residue field extension `κ(m_R) → κ(m_S)`
is surjective. This file proves Stacks 0GSD: there is a `t ∈ m_R` with `R/tⁿR → S/tⁿS` bijective
for every `n`.

The witness is produced by Newton's method. Shrinking `T` to a principal localization that is
*standard étale* over `R` (Proposition 00UE) presents `S` as a ring of fractions of polynomials
in one element: there are a monic `f ∈ R[X]` and a `ξ₀ ∈ S` with `f(ξ₀) = 0` and `f'(ξ₀)` a unit,
such that every `z ∈ S` satisfies `z·Q₁(ξ₀) = Q₂(ξ₀)` with `Q₁(ξ₀)` a unit. The residue field
hypothesis provides an `a ∈ R` with `ξ := ξ₀ - a ∈ m_S`. Writing `f(X + a) = X·h + t` with `t` its
constant term gives `t = -ξ·h(ξ) ∈ m_R`, and `h(ξ)` is a unit because it agrees with the unit
`f'(ξ)` modulo `m_S`. The recursion `ξ = -t·h(ξ)⁻¹` then produces, for every `n`, an `r ∈ m_R`
with `tⁿ ∣ ξ - r` in `S`; lifting along the principal ideal `tⁿ` rather than along `m_R` is what
makes a single element `t` work for all `n` at once.

Surjectivity of `R/tⁿR → S/tⁿS` follows: in `z·Q₁(ξ₀) = Q₂(ξ₀)` both sides are congruent modulo
`tⁿ` to images of elements of `R`, and the one coming from `Q₁` is a unit of `R` because it is a
unit of `S` and `R → S` is local. Injectivity is faithful flatness: `R → S` is flat, being a
localization of an étale algebra, and a flat local homomorphism of local rings is faithfully flat
(Lemmas 00HR, 05CK), so `tⁿS ∩ R = tⁿR`.

## Main results

* `Stacks.Etale.PrincipalPowerIso.solution`: the statement of
  `IsLocalRing.exists_mem_maximalIdeal_bijective_algebraMap_quotient_span_pow`, Lemma 0GSD.

## Implementation notes

The source reaches surjectivity by a second shrinking of `T`, to `R[x]_{hg}/(f)`, in which
`T/tT` is a quotient of `R/tR`, lifts that to `tⁿ` with Lemma 07RD, and then transfers from `T`
to `S`. The route taken here does the lifting in `S` directly, by the Newton recursion above, so
neither the second localization of `T` nor Lemma 07RD is needed; the finiteness of `T` over `R`
that 07RD consumes enters instead as the presentation of `S` by one simple root with polynomial
denominators, `exists_hasMap_forall_exists_mul_aeval_eq`.

## References

* [StacksProject 0GSD](https://stacks.math.columbia.edu/tag/0GSD), Lemma 10.153.1.
* [Lindel], the Lemma on page 321.
* [KC], Lemma 4.1.5.
-/

open Polynomial IsLocalRing

namespace Stacks.Etale.PrincipalPowerIso

section Polynomials

variable {R : Type*} [CommRing R]

end Polynomials

section LocalRing

variable {S : Type*} [CommRing S] [IsLocalRing S]

end LocalRing

section Newton

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- **Every element of a local ring is congruent modulo the maximal ideal to one in the image of
a ring homomorphism whose composite with the residue map is surjective.**

Only the target need be local, and the homomorphism need not be local: the hypothesis is
surjectivity of `residue B ∘ F` itself, which is what the proof uses. -/
public theorem exists_sub_mem_maximalIdeal_of_surjective_residue_comp {A B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing B] (F : A →+* B)
    (hres : Function.Surjective ((residue B).comp F)) (b : B) :
    ∃ a : A, b - F a ∈ maximalIdeal B := by
  obtain ⟨a, ha⟩ := hres (residue B b)
  exact ⟨a, Ideal.Quotient.eq.1 ha.symm⟩

end Newton

section FaithfullyFlat

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]

end FaithfullyFlat

section Presentation

end Presentation

end Stacks.Etale.PrincipalPowerIso

/-!
# An étale local homomorphism is an isomorphism modulo powers of a principal ideal

Let `(R, m_R) → (S, m_S)` be a local homomorphism of local rings and assume that `S` is the
localization at a prime `q` of an étale `R`-algebra `T`, and that the induced extension of
residue fields `κ(m_R) → κ(m_S)` is an isomorphism. Then `R → S` is an isomorphism after
reduction modulo all powers of a suitable nonunit: there is `t ∈ m_R` with
`R/tⁿR → S/tⁿS` bijective for every `n`.

The witness is not an arbitrary element of `m_R`. In the source's proof `R → T` is reduced to a
*standard étale* map `T = R[x]_g/(f)` (Proposition 00UE, Definition 00UB); the residue field
hypothesis allows `x` to be translated so that `q = (m_R, x)`, and then
`f = xᵈ + a_{d-1}x^{d-1} + ⋯ + a₁x + t` with `t = f(0)`, which lies in `m_R` precisely because
`x ∈ q`. Writing `f = t + x h` with `h = a₁ + a₂x + ⋯ + x^{d-1}`, invertibility of `f'` on `T`
forces `a₁`, hence `h`, to be a unit at `q`, so `T` may be shrunk to `R[x]_{hg}/(f)` and then
`T/tT = (R/tR)[x]_{hg}/(x)` is a quotient of `R/tR`. Lemma 07RD upgrades this to surjectivity of
`R/tⁿR → T/tⁿT` for all `n`, injectivity comes from faithful flatness of the flat local map
`R/tⁿR → S/tⁿS` (Lemmas 00HR, 05CK), and finally `S/tⁿS` is a localization of the local ring
`T/tⁿT = R/tⁿR` at a prime containing its maximal ideal, hence equal to it.

The typical instance: `R = ℤ_(5)`, `T = R[x]/(x² - x + 5)`, `q = (5, x)`. Here `T` is the ring of
integers of `ℚ(√-19)` localized at `5`, in which `5` splits, `S = T_q` is a discrete valuation
ring strictly larger than `R`, the residue fields are both `𝔽₅`, and `t = f(0) = 5` gives
`R/5ⁿ ≅ S/5ⁿ ≅ ℤ/5ⁿ`.

## Main results

* `IsLocalRing.exists_mem_maximalIdeal_bijective_algebraMap_quotient_span_pow`: Lemma 0GSD.

## Implementation notes

The quotient map `R/tⁿR → S/tⁿS` is the `algebraMap` of the canonical algebra structure
`Ideal.Quotient.algebraQuotientMapQuotient` on `S ⧸ (Ideal.span {t ^ n}).map (algebraMap R S)`
over `R ⧸ Ideal.span {t ^ n}`; it is characterized by
`algebraMap _ _ (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R S r)`, which holds by
`rfl`. Stating bijectivity of this map, rather than the existence of some isomorphism between the
two quotients, is what pins the source's map.

Three departures from the source's form, none of them weakening it.

The hypothesis "`S` is the localization of an étale ring extension of `R`" is expressed by an
ambient `R`-algebra `T` with `[Algebra.Etale R T]` and a prime `q` of `T` with
`[IsLocalization.AtPrime S q]`, rather than by an existential inside the statement; the
statement is thereby universally quantified over the presentation of `S`, which is how a user
supplies one. The source's further condition that `q` lies over `m_R` is omitted because it is
implied: `q = m_S.comap (algebraMap T S)` for a localization at a prime, so its contraction to
`R` is `m_S.comap (algebraMap R S) = m_R` by `[IsLocalHom (algebraMap R S)]`.

The conclusion is stated for every `n : ℕ` rather than for `n ≥ 1`. For `n = 0` both quotients are
the zero ring, so that case is true and carrying `1 ≤ n` would leave a hypothesis the conclusion
does not use.

The residue field hypothesis asks only that `κ(m_R) → κ(m_S)` be surjective. It is automatically
injective, being a ring homomorphism out of a field into a nontrivial ring, so this is the same
condition as the source's "is an isomorphism", stated with the weaker of the two hypotheses.

Faithfulness to [StacksProject 0GSD]:

1. No dead hypothesis. `t ∈ IsLocalRing.maximalIdeal R` is load-bearing in the conclusion:
   without it `t = 1` makes both quotients zero and the statement vacuous. The residue field
   surjectivity is used and not implied by the rest: `R = ℤ_(5)`, `T = R[x]/(x² + x + 1)`,
   `q = (5, x)` is étale with `κ(q) = 𝔽_25`, and no `t ∈ 5R` can give `R/tR ≅ S/tS`, since
   `S/5S = 𝔽_25` is not a quotient of `R/5R = 𝔽₅`, while every other hypothesis holds.
   `[IsLocalHom (algebraMap R S)]` is used twice over: it is what makes `κ(m_R) → κ(m_S)` exist
   at all, and it is load-bearing on its own — for `R = ℤ_(5)`, `T = R[1/5] = ℚ`, which is étale
   over `R` as a localization away from `5`, and `q = 0`, we get `S = ℚ`, all the remaining
   hypotheses hold (the residue field condition cannot even be formulated), and every `t ∈ m_R`
   fails, since `S/tⁿS = 0` while `R/tⁿR ≠ 0`. `[Algebra.Etale R T]` is used: for `T = R[x]` and
   `q = (5, x)` all other hypotheses hold, `κ(m_S) = 𝔽₅`, and `R/tⁿR → S/tⁿS` fails to be
   bijective for every `t ∈ 5R`, since `S/5S = 𝔽₅[x]_(x)` is not a quotient of `𝔽₅`.
2. The scalars and the base are the source's. Both quotients are taken of `R` and of `S`
   themselves by the ideals generated by `tⁿ` and by its image, and the map compared is the one
   induced by the given `R → S`; no localization of `R` intervenes, and the ideal in `S` is
   `tⁿS`, the ideal generated by the image of `tⁿ`, not the contraction or an abstract ideal.
3. What the source names is pinned. The residue field extension `κ(m_R) → κ(m_S)` is
   `IsLocalRing.ResidueField.map (algebraMap R S)`, the map induced by the given local
   homomorphism, and the comparison map `R/tⁿR → S/tⁿS` is the canonical `algebraMap` described
   above; neither is merely asserted to exist.
4. The instantiation is not degenerate. The witness `R = ℤ_(5)`, `T = R[x]/(x² - x + 5)`,
   `q = (5, x)`, `t = 5` recorded above has `S ≠ R` — `S` is a localization of a rank two
   `R`-algebra, with fraction field `ℚ(√-19)` — so the conclusion is not the tautology obtained
   when `T = R`, and `t = 5` is a nonzero nonunit, so no `tⁿR` is `0` or `R`.

## References

* [StacksProject 0GSD](https://stacks.math.columbia.edu/tag/0GSD), Lemma 10.153.1, in
  Section 10.153 "Local homomorphisms".
* [Lindel], the Lemma on page 321.
* [KC], Lemma 4.1.5.
-/

@[expose] public section

end
