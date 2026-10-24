# Tail L-polynomial divisibility for upper two-block induction

Author: Worker 82.

This module defines `Langlands.RankinSelberg.InducedTailLFactorStatement`, a
proposition, and does not prove it. It states the Whittaker-type extension of
JPSS Lemma (9.3), using the existing canonical normalized induction and certified
rank-symmetric L-polynomial relation. The extension of the third representation
beyond the lemma's literal wording is justified below from its proof.

## Original source

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
convolutions*, American Journal of Mathematics 105 (1983), 367–464.

- Registered source: `jpss-1983-rankin-selberg`.
- Retained file: `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
- SHA-256: `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- Section 2.1, printed 385–386 (PDF 20–21): Whittaker type, genericity,
  and the Whittaker function space, which may be a proper quotient.
- Section 2.12, printed 403 (PDF 38): symmetry and the smaller-rank-first
  convention for L-factors.
- Section 2.13, printed 404 (PDF 39): vanishing of L-factors after a
  sufficiently ramified character twist, under the Whittaker-type scope of
  Section 2.
- Theorem 3.1, printed 404–405 (PDF 39–40): multiplicativity and divisibility
  for Whittaker-type representations.
- Sections 9.1–9.3, printed 452–457 (PDF 87–92): upper induction, Whittaker
  extension, localization, and the tail-factor lemma; its statement is on
  printed 455 and its proof ends on printed 457.
- Section 9.4, printed 458–460 (PDF 93–95): the Langlands-type induced pairs
  and the use of tail divisibility in the double induction on printed 460.

## Statement and constructions

For every prime `p`, algebraic p-adic field `F : PadicField p`, nontrivial
continuous unitary additive character `ψ` of its canonical topology, and
supplied `ν : SelfDualHaar F.canonicalTopologicalData ψ`, take nonnegative
integers `a`, `b`, `t`. The two blocks have positive ranks `A = a + 1` and
`B = b + 1`; the test representation has arbitrary positive rank `T = t + 1`.
The block representations `π₁`, `π₂` and test representation `σ` each satisfy
`IsOfWhittakerType` for the standard character attached to `ψ`.

The conclusion supplies `Pfull Ptail : ℂ[X]` such that:

1. `IsPadicSymmetricLPolynomial F ψ ν.val ξ σ Pfull`;
2. `IsPadicSymmetricLPolynomial F ψ ν.val π₂ σ Ptail`;
3. `Ptail ∣ Pfull`.

Here `ξ` is explicitly
`F.canonicalNormalizedProductInduced (Shahidi.twoBlocks A B … …)` of the
published `Shahidi.pairFamily` of the two explicitly lifted block actions.
There is no variable standing for an unspecified induction and no assumed
representation equivalence. `twoBlocks` has block order `(A, B)` and its
parabolic is the standard upper parabolic with zero lower-left block. This
agrees directly with §9.1. In particular the tail is the **second** block;
no reversal to the lower-parabolic convention of §3.1 occurs in the target.

The construction acts by right translation on right-smooth covariant functions
with values in the external tensor product. Its normalizing character is the
positive half modulus of the canonical local-field data. On diagonal blocks
`(g₁, g₂)` the full modulus is `|det g₁|^B / |det g₂|^A`, so the inducing
factor is `|det g₁|^(B/2) |det g₂|^(-A/2)`. This is the normalized induction
used in §9.1; the definition does not invoke Shahidi's separately twisted
`source` representation.

The original carriers lie in independent universes `uV₁`, `uV₂`, and `uW`,
with field universe `uF`. The published finite block family needs both block
carriers in one universe. The statement therefore uses `ULift.{uV₂} V₁` and
`ULift.{uV₁} V₂`, both in `max uV₁ uV₂`, and conjugates each action through
`ULift.moduleEquiv.symm.conjRingEquiv`. Explicitly the lifted action sends
`ULift.up v` to `ULift.up (πᵢ g v)`; the maps `up` and `down` are inverse
linear intertwining maps. This is a constructed change of carrier, not a new
mathematical hypothesis. The induction's carrier lies in
`max uF uV₁ uV₂`; the tail factor retains the original `π₂` carrier.
No universe equality or countability reduction is assumed.

`IsOfWhittakerType` means admissibility, finite generation over the group
algebra, and a functional space linearly equivalent to `ℂ`. It neither
asserts irreducibility nor requires the coefficient map to be injective.
`UnitaryAdditiveCharacter` already includes continuity and nontriviality.
The symmetric relation uses the larger rank first, with `ψ` on that member
and its inverse on the other, in accordance with §2.12. Thus the statement
includes every rank order, including equality with the tail and with the
full rank. The sign change of the Whittaker character is harmless by diagonal
conjugation as in §2.1; it adds no hypothesis.

The L-polynomial relation uses the canonical residue cardinality and
normalized absolute value, requires existence of a compatible quotient
measure, and quantifies over every compatible quotient measure. It asserts
that `1/P` generates the Laurent span of the actual rational zeta integrals
and that `P(0) = 1`. Thus the witnesses certify the factors and their
normalization, rather than merely supplying arbitrary polynomials. The
self-dual additive measure is supplied, not asserted to exist here.

## Divisibility direction

Writing `X = q^(-s)`, the source conclusion is
`L(s, π₂ × σ) = R(X) L(s, ξ × σ)` for a polynomial `R`. Since the two
L-factors are `1/Ptail(X)` and `1/Pfull(X)`, respectively, this says
`Pfull = R * Ptail`, equivalently `Ptail ∣ Pfull`. The Lean conclusion uses
polynomial divisibility, not just Laurent divisibility and not its reverse.

The direct integral comparisons in the proof first give Laurent-ideal
inclusion. For the normalized polynomials that inclusion implies
`Ptail ∣ X^e * Pfull` for some `e`; since `Ptail(0) = 1`, it is coprime to
`X` and divides `Pfull`. This explains why the source can state a polynomial
multiplier. It also forces `R(0) = 1`, though that redundant equality is not
an extra clause in the Lean statement.

## Why the test representation may be of Whittaker type

The literal statement on printed 455 calls `σ` generic. Section 2.1,
printed 385, defines genericity in the irreducible case, and separately defines
Whittaker type; these words cannot simply be identified. The present target
is a **derived extension**, not a quotation of a stronger literal lemma.
The proof extends as follows, with `r = A + B` and `T` the test rank.

1. If `T = B`, Proposition 9.1 extends an arbitrary tail Whittaker function
   and Schwartz function to one for `ξ`. The displayed integral identity
   on printed 455 realizes the tail equal-rank integral as a full-pair
   unequal-rank integral. The test function is an arbitrary member of
   the Whittaker space of `σ`; no irreducibility or injective Whittaker
   realization is used.
2. If `T < B`, the cutoff in printed 456 and Proposition 9.1 identify
   the tail and full integrals. The support input is for the block
   Whittaker function. Again the test representation enters only through
   its Whittaker functions, whose zeta integrals generate the factor by
   Theorem 2.7 in the Whittaker-type setting.
3. If `B < T < r`, Proposition 9.1 and Lemma 9.2 localize an extended
   Whittaker function. Lemma 9.2 itself assumes Whittaker type. Shrinking
   compact open subgroups makes the test Whittaker function invariant under
   the required right translations; this uses smoothness, not
   irreducibility. The identity on printed 457, up to a nonzero volume
   scalar, gives the reversed-rank tail integral. The cutoff and
   Laurent-ideal argument apply to Whittaker functions of Whittaker-type
   representations as in the preceding cases.
4. If `T ≥ r`, add `T-r+1` rank-one characters before the first block, so
   the enlarged induction `ξ'` has rank `T+1` and the same last block.
   Transitivity of normalized induction gives both groupings used on
   printed 457. The previous case gives `Ptail ∣ Pξ'`. Theorem 3.1 gives
   `Pξ' ∣ (∏ P(μᵢ × σ)) * Pfull`. Its hypotheses are Whittaker type,
   preserved under induction by Proposition 2.3; irreducibility is not
   needed. Choose each `μᵢ` sufficiently ramified. Proposition 2.13,
   printed 404, is stated in the Section 2 Whittaker-type setting and
   proves the needed rank-one vanishing from a fixed finite collection
   of asymptotic characters. Hence each `P(μᵢ × σ) = 1` also for general
   Whittaker-type `σ`. The two divisibilities yield `Ptail ∣ Pfull`.

Thus the only potentially restrictive final step has a source-supported
Whittaker-type input already in §2.13. No appeal to the irreducible-only
modern highly ramified pair statement is needed. The representation `ξ`
is itself of Whittaker type by §2.3, which is an obligation of the eventual
proof, not a hypothesis added to this statement. Factor existence comes
from Theorem 2.7 after that induction result and is also part of the eventual
proof obligation.

This reading agrees with §9.4: printed 458 identifies both Langlands-type
inductions as Whittaker type, and the double induction on printed 460 uses
tail divisibility with the other full induction as test representation,
without assuming that it is irreducible. That later use corroborates the
extension; the justification above is the proof analysis rather than an
inference from terminology alone.

## Scope and status

The field scope is finite extensions of `ℚ_p`, because the existing canonical
induction and certified factor interfaces are p-adic; the original paper
allows all nonarchimedean local fields. All three ranks are positive and
the two blocks have fixed order. There are no unitarity, temperedness,
irreducibility, induced-genericity, or pre-existing factor hypotheses.

This is one statement-only unit. It does not prove Lemma 9.3, the derived
extension, Whittaker preservation under induction, Theorem 2.7, ramified
vanishing, or multiplicativity. Those inputs and the analytic integral
comparisons remain proof obligations; the existing published pairs are
unchanged.

## Lean validation

Development check `60c040ef-dc6f-47f6-a424-aacbf816d5fa` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled this module with zero errors
and warnings. Declaration inspection reports a definition returning `Prop`,
universe parameters `uF`, `uV₁`, `uV₂`, `uW`, and only the standard
`propext`, `Classical.choice`, and `Quot.sound` axioms. There are no proof
holes or newly introduced axioms. This check is not semantic acceptance
or a proof of the proposition.
