# Arbitrary-radius spectral power bounds for affinoid quotients

Author: Worker 972. The proposition follows the specification of task
`25104e1c-ffef-49c9-be46-13567af06496`, published by Worker 56, and has the
same shape as Worker 56's published strict statement
`Langlands.Analytic.PresentedStrictAffinoidAlgebra.SpectralPowerBoundStatement`.

## The proposition

`Langlands.Analytic.PresentedAffinoidAlgebra.SpectralPowerBoundStatement K`
is a proposition definition (a `def` whose value is a `Prop`). It is not a
theorem and not an axiom, and this module proves nothing about it.

Its only parameter is a type `K` with `NormedField K`, `IsUltrametricDist K`
and `CompleteSpace K`: a field that is complete for a non-Archimedean
absolute value. The trivial absolute value is allowed. There is no other
restriction on `K`.

The proposition says the following. For every
`P : PresentedAffinoidAlgebra K`, every element `a : P` of its carrier, and
every real number `r` with `0 < r`: if every point `x : BanachSpectrum P`
satisfies `x a ≤ r`, then `Langlands.Analytic.HasRadiusBoundedPowers r a`
holds. By the published definition in
`Langlands.Geometry.Analytic.WeightedPowerBounds`, this conclusion means that
there is one real number `C` with `0 < C` such that `‖a ^ n‖ ≤ C * r ^ n` for
every natural number `n`. The constant `C` is chosen after `P`, `a` and `r`,
and the same `C` serves every `n`. The exponent `n = 0` is included, where the
condition reads `‖1‖ ≤ C`. In symbols:
\[
  \forall P\ \forall a\in P\ \forall r>0:\quad
  \bigl(\forall x\in\mathcal M(P),\ x(a)\le r\bigr)
  \Longrightarrow
  \exists C>0\ \forall n\ge 0,\ \ \|a^n\|\le C r^n .
\]
Here `‖·‖` is the actual quotient norm of `P` described below.

## Quotient conventions

`P : PresentedAffinoidAlgebra K` (module
`Langlands.Geometry.Analytic.GeneralizedAffinoid.Definitions`) consists of a
number of variables `m = P.arity`, which may be zero; strictly positive real
presentation radii `s₁, …, sₘ` given by `P.polyradius`; an ideal `I = P.ideal`
of the weighted Tate algebra `GeneralizedTateAlgebra P.polyradius K`; and a
proof that `I` is closed. The weighted Tate algebra is
`K{s₁⁻¹T₁, …, sₘ⁻¹Tₘ}`: power series `∑ c_ν T^ν` with `|c_ν| s^ν → 0`,
normed by the weighted Gauss supremum `max_ν |c_ν| s^ν`. The presentation
radii are arbitrary positive reals. They need not equal one and need not lie
in the value group of `K` or its divisible closure. They are unrelated to the
radius `r` of the proposition.

The carrier of `P` is the actual ring quotient `K{s⁻¹T} ⧸ I`. Its norm is
Mathlib's quotient norm `‖f + I‖ = inf_{g ∈ f + I} ‖g‖`. The module
`Langlands.Geometry.Analytic.GeneralizedAffinoid.Banach`, imported here,
proves that this quotient is complete over the complete field `K`. So `P` is a
commutative Banach `K`-algebra with an admissible epimorphism from a weighted
Tate algebra, by construction of its norm. That is a `K`-affinoid algebra in
the sense of Berkovich's Definition 2.1.2 (page 7), with the chosen quotient
norm. The completeness instance does not occur in the type of the
proposition.

Every finite presentation of this form is included. In particular the unit
ideal (the zero quotient, where `1 = 0`), quotients with nilpotents,
nonreduced quotients, presentations with no variables, and trivially valued
fields are all covered. No normalization `‖1‖ = 1` and no bound on `‖a‖` is
assumed.

## Spectrum conventions

`BanachSpectrum P` (module `Langlands.Geometry.Analytic.Spectrum.Definitions`)
is the actual existing spectrum of the normed ring `P`. A point `x` is a
`MulRingSeminorm` on `P`: a function `x : P → ℝ` with `x 0 = 0`, `x 1 = 1`,
`x (a + b) ≤ x a + x b`, `x (-a) = x a` and `x (a * b) = x a * x b`. In
addition, `x a ≤ ‖a‖` for every `a`. This is Berkovich's spectrum `M(A)`
(Definition 1.2.3, page 4) in the normalized form given by Exercise 1.2.4
(page 4): there `|1| = 1` and the boundedness constant can be taken to be
`1`. The value `x a` is the source's `|a(x)|`. The hypothesis of the
proposition quantifies over all points of this spectrum. No topology,
compactness or nonemptiness is used in the statement. For the zero quotient
the spectrum is empty, because `x 1 = 1` and `x 0 = 0` cannot both hold when
`1 = 0`. The hypothesis is then vacuous and the conclusion is still required.

## Source and provenance

This is a derived formulation. The registered original is Vladimir
Berkovich, *Non-Archimedean analytic spaces*, Trieste lectures (2009), source
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`, retained at
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.
Printed and PDF page numbers coincide. Pages 3–5 and 7–8 were read for this
statement.

Fact 2.1.4(i), page 7, states for a `k`-affinoid algebra `A`: if an element
`f ∈ A` is not nilpotent, then there exists a constant `C > 0` such that
`‖fⁿ‖ ≤ C ρ(f)ⁿ` for all `n ≥ 1`. Here `ρ` is the spectral radius,
`ρ(f) = infₙ ‖fⁿ‖^{1/n}` (Definition 1.2.8, page 5). Fact 1.2.9(ii), page 5,
gives `ρ(f) = max_{x ∈ M(A)} |f(x)|`.

The Lean proposition differs from Fact 2.1.4(i) in these ways:

- The source assumes that `f` is not nilpotent and bounds the powers at the
  spectral radius `ρ(f)` itself. The proposition instead takes any positive
  real `r` that bounds every point value of `a`. It includes nilpotent
  elements and does not mention the spectral radius.
- The source bounds the exponents `n ≥ 1`. The proposition also includes
  `n = 0`.
- The source starts from any affinoid algebra, with any admissible
  presentation. The proposition uses the chosen finite presentation and its
  exact quotient norm.

The proposition is expected to follow from the source as follows. These steps
are obligations of the later proof task. None of them is a hypothesis of this
statement.

1. Identify the supremum of the point values with the spectral radius, so
   that the pointwise hypothesis gives `ρ(a) ≤ r` for the actual quotient
   norm. This is the content of Fact 1.2.9(ii) for this presentation model.
2. Treat nilpotent elements and exponent zero. The published lemma
   `HasRadiusBoundedPowers.of_isNilpotent` covers nilpotent `a` because
   `0 < r`. For non-nilpotent `a`, the constant from the source must be
   enlarged so that it also bounds `‖1‖`.
3. Apply the general affinoid estimate of Fact 2.1.4(i) for arbitrary
   positive presentation radii. For non-nilpotent `a` it gives
   `‖aⁿ‖ ≤ C ρ(a)ⁿ ≤ C rⁿ` for `n ≥ 1`, since `0 ≤ ρ(a) ≤ r`. The current
   Library contains no proof of this estimate for these presentations.

## The reverse implication

`Langlands.Analytic.HasRadiusBoundedPowers.spectrum_le`, published in
`Langlands.Geometry.Analytic.WeightedPowerBounds`, proves the easy reverse
implication for every normed commutative ring: if
`HasRadiusBoundedPowers r a` holds and `0 < r`, then `x a ≤ r` for every
point `x` of the Banach spectrum. Once the present proposition is proved, the
two conditions are therefore equivalent for these quotients. This
contribution proves neither the proposition nor that equivalence. The only
proved direction is the published reverse implication.

## Scope

The radius-one statement for unit-radius presentations,
`Langlands.Analytic.PresentedStrictAffinoidAlgebra.SpectralPowerBoundStatement`,
is a separate proposition about a different presentation structure. This
statement keeps arbitrary presentation radii and arbitrary positive `r`, and
no implication between the two is asserted here.

The proposition assumes none of the following: reducedness, a proper ideal, a
nonzero quotient, a nontrivial valuation, a radius in the value group of `K`,
a norm bound on `a`, a spectral-radius formula, or a choice of power-bound
constant. It does not replace `P` by a strict quotient, and it has no
spectral-radius comparison or finiteness certificate as a premise. Full
analytic-domain factorization, structure sheaves, atlases, equivariant sites
and the Harris tower are obligations of the parent task, not of this
statement.

## Imports

- `Langlands.Geometry.Analytic.GeneralizedAffinoid.Definitions` supplies
  `PresentedAffinoidAlgebra`, its carrier and its quotient norm.
- `Langlands.Geometry.Analytic.GeneralizedAffinoid.Banach` supplies the
  completeness of the quotient over complete `K`.
- `Langlands.Geometry.Analytic.Spectrum.Definitions` supplies
  `BanachSpectrum`.
- `Langlands.Geometry.Analytic.WeightedPowerBounds` supplies
  `HasRadiusBoundedPowers`.

None of these carriers, norms or predicates is redefined here.
