# Highly ramified L-vanishing for pairs of Whittaker type

Author: Worker 386.

This module defines the proposition
`Langlands.RankinSelberg.WhittakerTypeHighlyRamifiedLVanishingStatement.{uF,uV,uW}`.
It states Jacquet–Piatetski-Shapiro–Shalika (JPSS), Proposition 2.13, for
actual representations of arbitrary positive ranks over a p-adic field.
Representations of Whittaker type may be reducible. The module supplies
neither a proof nor an assumption asserting this proposition.

## Original source and scope

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`. The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 385, 390–391 and 403–404 (PDF pages 20, 25–26 and 38–39,
counting the cover as page 1) were read visually. No source-specific erratum
was found in the available project, Library or central-source filenames;
the project and Library have no `notes/errata` directory at this reading.

Section 2.1, printed page 385, defines Whittaker type by admissibility,
finite type and a one-dimensional space of Whittaker functionals. It
explicitly distinguishes this class from irreducible generic
representations. The Library's `IsOfWhittakerType n θ π` implements these
conditions as `IsAdmissible π`, finite generation of `π.asModule` over the
group algebra, and the existence of a complex linear equivalence from
the `θ`-functional space to `ℂ`. In particular the representation is
nonzero.

Theorem 2.7(i)–(ii), printed pages 390–391, gives convergence, rationality
and the normalized reciprocal-polynomial generator of the zeta integral
ideal for representations of Whittaker type. It includes equal rank and
all unequal-rank blocks. Section 2.12, printed page 403, gives independence
of the additive character, equal-rank symmetry, and the convention that
an unequal-rank pair is read with the larger rank first.

Proposition 2.13, printed page 404, states that, for fixed `π` and `σ`,
`L(s, (π ⊗ χ) × σ) = 1` once the conductor of `χ` is sufficiently large.
The representations retain the scope of Section 2.1. Section 3.1 on the
same page reiterates that the representations of Section 2 are of
Whittaker type. Thus the present scope comes directly from JPSS 1983.
The existing `HighlyRamifiedStatement` module records the narrower
Jacquet–Shalika 1985 generic statement with an additive-conductor
normalization; that module is preserved.

## Exact proposition

For every prime `p` and `F : PadicField.{uF} p`, use the canonical
topological data of `F`. Quantify over every nontrivial continuous
unitary additive character `ψ` and every supplied
`ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`.
Nontriviality is part of `UnitaryAdditiveCharacter`. The proposition does
not assert self-dual Haar existence; it quantifies over supplied measures.
There is no condition on the additive conductor of `ψ`. The source treats
nonarchimedean local fields generally; this statement uses the Library's
canonical p-adic specialization.

For all `r t : ℕ`, take actual complex representations `π` of
`GL_(r+1)(F)` on `V : Type uV` and `σ` of `GL_(t+1)(F)` on
`W : Type uW`. The carrier universes are independent. The two hypotheses
are exactly
`IsOfWhittakerType r (standardCharacter ψ r) π` and
`IsOfWhittakerType t (standardCharacter ψ t) σ`.
Both use the standard character of the same `ψ`. The integral relation
uses the inverse character for its second member; the character
transport of Section 2.1 explains why the source can use these two
conventions for Whittaker type.

There exists `A : ℕ` such that every
`χ : HarmonicAnalysis.Quasicharacter F.Carrier` with
`A ≤ F.canonicalTopologicalData.multiplicativeConductor χ` satisfies

```text
IsPadicSymmetricLPolynomial F ψ ν.val
  (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) σ 1.
```

Here `Quasicharacter` is the existing
`ContinuousMonoidHom F.Carrierˣ ℂˣ`; unitarity of `χ` is not required.
The determinant twist acts by `g ↦ χ(det g) π(g)`.
The existing multiplicative conductor is the least unit level on which
`χ` is trivial, with level zero for an unramified character. The bound is
chosen after the field, character, measure and representations, and
before `χ`. It is therefore uniform over every quasicharacter above the
threshold, including arbitrary unramified parts. A natural-number
threshold suffices since multiplicative conductors are natural numbers.

## Factor existence and measure quantifiers

The conclusion is the full existing `IsPadicSymmetricLPolynomial`
relation at polynomial `1`. If `t ≤ r` it is
`IsPadicPairLPolynomial` for `(π ⊗ (χ ∘ det), σ)`, including equal ranks;
if `r < t` it is that relation for `(σ, π ⊗ (χ ∘ det))`.
Thus all positive ranks, both rank orders and rank one are included.

For the smaller rank, `IsPadicPairLPolynomial` requires a right
invariance witness for the fixed unipotent Haar measure and existence
of a quotient measure compatible with the fixed general-linear and
unipotent Haar measures. It further quantifies over every such right
invariance instance and every quotient measure satisfying
`QuotientIntegration.IsCompatible`. For each it requires the full
`IsPairLPolynomial` certificate at `1`, with the canonical residue
cardinality and normalized absolute value. In unequal rank this covers
every rectangular block, using the additive measure `ν.val`; equal
rank uses the equal-rank zeta ideal.

The polynomial is the normalized denominator:
`L(s, π × σ) = 1 / P(q^(-s))`. Certifying `P = 1` asserts that the
normalized generator exists and is `1`, as well as compatible quotient
measure existence. Factor existence is consequently part of the
conclusion. No pre-existing factor or analytic-existence proposition
is a hypothesis.

## Separate proof obligation

The source proof on page 404 uses the finite-function expansions from
the proof of Theorem 2.7. For fixed representations the finite functions
come from a fixed finite set; sufficiently ramified twists remove the
possible denominators in the resulting one-variable integrals. The
normalized reciprocal-polynomial generator is then `1`. This describes
the source argument only; no part of it is proved by this module.

A proof successor must supply the analytic and asymptotic prerequisites
and the required uniform conductor bound. Full L-factor multiplicativity
must not be used to justify this prerequisite: JPSS explicitly uses
Proposition 2.13 later in Section 7. Compilation and inspection of the
Prop definition establish well-formedness, independently of this
remaining mathematical proof obligation.

## Lean check

The exact declaration compiled and was inspected with `lean_check` in
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with no errors or warnings.
The inspection reports a definition returning `Prop`, universe parameters
`uF uV uW`, and only `propext`, `Classical.choice` and `Quot.sound` as
logical assumptions. This is a statement check, not a proof of the target.
