# Restricted rank-one extension divisibility

Author: Worker 125.

This module defines the proposition
`Langlands.RankinSelberg.RankOneExtensionLDivisibilityStatement.{uF,uV,uW}`.
It states the upper-parabolic transport of JPSS Lemma (5.5), with existence
of both certified L-polynomials. It does not prove or assume the proposition.

## Original source and scope

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
convolutions*, American Journal of Mathematics 105 (1983), 367–464.

- Registered source: `jpss-1983-rankin-selberg`.
- Retained PDF: `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
- SHA-256: `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- Section 3.1, printed 404–405 (PDF 39–40), supplies the Whittaker-type
  hypotheses and the lower standard parabolic convention.
- Lemma 5.5, printed 423–427 (PDF 58–62), is the source of this target.
  Its statement on printed 423 assumes `t₂ = 1` and `R ≥ t₁ + t₂ + 1`.
  It states `L(s, π × σ₁) = L(s, π × σ) Q(q^(-s))` with `Q` a polynomial.
- Section 7, printed 438–443 (PDF 73–78), uses the lemma in the descending
  induction: in particular equation (7.1.18) on printed 441 and equation
  (7.2.13) on printed 443.

These original scanned pages were read directly. No source erratum was
present in the project's `notes/errata` locations when this pair was authored.
The statement restricts the original nonarchimedean field setting to the
Library's canonical `PadicField` interfaces.

## Quantifiers and conclusion

For every prime `p`, `F : PadicField.{uF} p`, nontrivial continuous unitary
additive character `ψ` for its canonical topology, and supplied self-dual
additive Haar measure `ν`, choose natural numbers `r,t`. The test
representation `π` has positive rank `R = r+1`, and `σ₁` has positive rank
`t₁ = t+1`. The hypothesis `t+3 ≤ r+1` is exactly `R ≥ t₁+2`.
Thus `π` has rank strictly greater than the full induced rank `t₁+1`.
The endpoint `t₁=1, R=3` is included; `R=t₁+1` is excluded.

The hypotheses require `π` and `σ₁` to satisfy `IsOfWhittakerType` for
`standardCharacter ψ`. They may be reducible. The rank-one factor is
`χ : Quasicharacter F.Carrier`, using the canonical topology. This is the
existing continuous multiplicative character into `ℂˣ`; no unitarity or
ramification restriction is placed on `χ`.

The conclusion supplies `Pbase Pind : ℂ[X]` with:

1. `IsPadicSymmetricLPolynomial F ψ ν.val π σ₁ Pbase`;
2. `IsPadicSymmetricLPolynomial F ψ ν.val π ξ Pind`;
3. `Pbase ∣ Pind`.

Here `ξ` is the actual
`F.canonicalNormalizedProductInduced` on
`Shahidi.twoBlocks 1 (t+1) … …`, with
`Shahidi.pairFamily χlift σ₁`. In particular its first block is the
rank-one character and its second block is `σ₁`. There is no assumed
Whittaker property of `ξ`, no supplied factor-existence premise, and no
irreducibility hypothesis.

The certified relation fixes the canonical residue cardinality and absolute
value. It requires existence of a compatible quotient measure and asserts
the normalized-generator property for every such measure. The polynomial
has constant term one, and its reciprocal generates the Laurent span of
the actual rational zeta values. Since the test rank is larger, the symmetric
relation selects the branch with `π` first. It uses `ψ` on that member and
the inverse character on the second; changing the sign of a standard
Whittaker character is implemented by diagonal conjugation in the eventual
proof. The self-dual measure is supplied rather than asserted to exist.

## Carrier universes and rank-one action

The field, `π` carrier `V`, and `σ₁` carrier `W` have independent universes
`uF`, `uV`, and `uW`. The finite tensor construction takes a family in one
universe, so its heterogeneous `Fin 2` family is
`Shahidi.pairCarrier (ULift.{uW} ℂ) W`, in `Type uW`.
Neither `V` nor `W` is replaced or forced into the other's universe.

`χlift` is obtained by conjugating the existing
`rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)` through
`ULift.moduleEquiv.symm`. Consequently, for `g : GL₁(F)`,
its action on `ULift.up z` is
`ULift.up ((χ (determinant g) : ℂ) * z)`.
The scalar, character, and determinant action are unchanged; `up` and `down`
are the explicit inverse linear carrier maps. The tensor carrier is in
`Type uW` and the induced carrier in `Type (max uF uW)`.
The first certificate retains `σ₁` on the original `W`.

## Lower-to-upper transport

JPSS uses lower normalized induction in the ordered blocks `(σ₁,χ)`.
Conjugating that lower parabolic by the permutation that reverses whole
blocks, while preserving internal block coordinates, gives the upper
parabolic with ordered blocks `(χ,σ₁)`. The corresponding tensor factors
must also be reindexed. The lower normalizing character is the inverse of
the upper half modulus for the original shape. After reversal it becomes
the upper half modulus for the reversed shape. For upper diagonal blocks
`(a,g)` of ranks `(1,t₁)`, its value is
`|a|^(t₁/2) |det g|^(-1/2)`.

The separate reversal interface is
`Langlands.GLOppositeProductReversalStatement` in
`Langlands.Representation.Induction.OppositeProductReversalStatement`.
Its prescribed maps are `f ↦ (x ↦ R(f(w*x)))` and
`h ↦ (x ↦ R.symm(h(w⁻¹*x)))`, where `R` reindexes the block tensor.
The future proof should use that interface and its proof, including the
shape/carrier identification with the two-block constructor here.
This target neither assumes that proposition nor introduces a duplicate
reversal construction. The two upper block orders are not identified.
The reversal statement and the present statement are not proof evidence
for one another.

## Divisibility and remaining proof obligations

Put `X=q^(-s)`. The source equation is
`1/Pbase = Q/Pind`, hence `Pind = Q*Pbase`, equivalently
`Pbase ∣ Pind`. The direction is opposite to the upper bound on factors
in Theorem 3.1(ii).

The integral comparison on printed 426 first places the base L-factor in
the Laurent ideal generated by the induced L-factor. Clearing negative
powers yields `X^e * Pind = Q₀ * Pbase` for some polynomial `Q₀`.
Since `Pbase(0)=1`, `Pbase` is coprime to `X`; thus it divides `Pind`.
Conversely polynomial divisibility gives the source Laurent membership.
Both constant terms being one also forces the polynomial multiplier to
have constant term one. This algebraic equivalence is explained here,
not proved by this statement-only module.

The original proof constructs compactly supported sections of the induced
model (printed 424–425) and uses a Fourier smoothing argument to realize
arbitrary base zeta integrals (printed 426–427). Those analytic comparisons,
Whittaker type of normalized induction, existence of the certified factors,
the explicit reversal transport, and the normalized polynomial conversion
remain obligations of a separate proof.

The dependency direction is Lemma 5.5 to Section 7 to the later results
of Section 9. This module does not import or use the later tail divisibility
statement as a justification, and makes no assertion for other rank orders.
