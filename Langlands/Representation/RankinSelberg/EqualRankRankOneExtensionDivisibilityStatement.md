# Equal-rank rank-one extension reverse divisibility

Author: Worker 571. Worker 465 specified this focused prerequisite. The
quantifier and lifted-character pattern is adapted from Worker 125's published
`RankOneExtensionDivisibilityStatement` pair.

This module defines
`Langlands.RankinSelberg.EqualRankRankOneExtensionLDivisibilityStatement.{uF,uV,uW}`.
It is an internal prerequisite motivated by the general-rank descent in JPSS
section 7.2. It defines a proposition and provides no proof of it. In particular,
this statement-only contribution does not repair the equal-rank analytic gap.

## Original source and internal provenance

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
convolutions*, American Journal of Mathematics 105 (1983), 367–464.

- Registered source: `jpss-1983-rankin-selberg`.
- Retained scan: `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
- SHA-256: `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- Theorem 3.1 and its setup: printed 404–405, PDF 39–40.
- Section 5.5, including Lemma 5.5 and its proof: printed 423–427, PDF 58–62.
- Section 7: printed 438–443, PDF 73–78, especially section 7.2(13)
  on printed 443.

These scanned passages were read visually for this contribution, and the source
fingerprint was checked. On 2026-10-26 no JPSS erratum was found in the registered
literature pointer index or the checked project, workspace and Library
`notes/errata` locations. This bounded check does not establish that no erratum
exists elsewhere. The rank mismatch below is recorded as a source-to-formalization
boundary, not as an established published erratum.

Theorem 3.1 uses representations of Whittaker type and lower standard normalized
induction. Its part (ii) places the induced L-factor in the Laurent ideal generated
by the product of the block L-factors. That is a forward multiplicativity bound.
The reverse divisibility targeted here has a different direction and is not
inferred from that theorem.

In Lemma 5.5, write `A` for the rank of the base block, `T=A+1` for the
rank of its rank-one extension, and `R` for the test rank. The printed assumptions
are `t₂=1` and `R≥T+1`. Thus the literal lemma only concerns `R>T`.
The published `RankOneExtensionLDivisibilityStatement` preserves this restriction
as `t+3 ≤ r+1`, with `A=t+1` and `R=r+1`.

Section 7.1 first treats source second block rank one; its descending induction
uses `r≤T-2`, so the auxiliary extension has rank `r+1<T`, within the strict
range of Lemma 5.5 after exchanging the pair. Section 7.2 then treats arbitrary
two-block induction, assumes `r<T`, and introduces the auxiliary lower induction
`π′=Ind(π,μ)` of rank `r+1`. Equation 7.2(13) invokes the same reverse relation
with test representation `σ` of rank `T`. At the first step `r=T-1`, the auxiliary
extension and the test representation both have rank `T`. This is outside the
printed Lemma 5.5 range. Renaming that step's test as the present `π`, its base as
`σ₁`, its auxiliary character as `χ`, and `T` as `t+2` gives the endpoint stated
here. Its test is allowed to be any Whittaker-type representation, so it includes
the induced test needed in that descent once its Whittaker type is established.

Section 6's adjacent-rank base, recalled in section 7.1, assumes source second
block rank one. After reversal this is upper first block rank one. It does not
supply the arbitrary-two-block first descent step. The present proposition is
therefore an explicitly internal additional proof target, not a transcription
or proof of Lemma 5.5. The restricted pair and all imported pairs are unchanged.

## Exact scope and polynomial certificates

The statement quantifies over every prime `p`, every canonical
`F : PadicField.{uF} p`, a continuous nontrivial unitary additive character `ψ`
for its canonical topology, and a supplied
`ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`.
It asserts no existence of this supplied self-dual measure.

For every `t : Nat`, the representations `π` and `σ₁` have ranks `t+2` and
`t+1`, on independent complex module carriers `V : Type uV` and `W : Type uW`.
The two hypotheses are exactly `IsOfWhittakerType (t+1)` for `π` and
`IsOfWhittakerType t` for `σ₁`, each for `standardCharacter ψ` in the canonical
topology. This predicate includes admissibility, finite generation over the
actual group algebra, and a one-dimensional space of Whittaker functionals.
Reducible representations are allowed. The rank-one factor is an arbitrary
continuous `χ : Quasicharacter F.Carrier`; it need not be unitary or unramified.
The endpoint `t=0`, with ranks two and one, is included.

Let `ξ` denote the actual constructor in the Lean conclusion:

```
F.canonicalNormalizedProductInduced
  (Shahidi.twoBlocks 1 (t+1) (Nat.succ_pos 0) (Nat.succ_pos t))
  (Shahidi.pairFamily χlift σ₁).
```

Its rank is `1+(t+1)=t+2`, equal to the test rank. The conclusion supplies
`Pbase Pind : Complex[X]`, certificates
`IsPadicSymmetricLPolynomial F ψ ν.val π σ₁ Pbase` and
`IsPadicSymmetricLPolynomial F ψ ν.val π ξ Pind`, and `Pbase ∣ Pind`.
There is no induced Whittaker-type hypothesis, supplied polynomial certificate,
or target-proposition premise.

These are the existing certificates for actual representations, with the canonical
residue cardinality and normalized absolute value. Each includes existence of
a compatible quotient measure and the L-polynomial property for every compatible
quotient measure. Each polynomial has constant term one and its reciprocal
generates the Laurent span of the relevant rational zeta values. The symmetric
relation reads the larger rank first and retains the first member at equal rank.
Consequently the base certificate uses the unequal-rank branch and the induced
certificate uses the equal-rank branch with `π` first. The latter includes the
Schwartz–Bruhat variable `Φ : SchwartzBruhat (Fin (t+2) → F.Carrier)` in its zeta
values; it is not the unequal-rank relation with a zero-size rectangular variable.
The first Whittaker model uses `ψ` and the second its inverse, as prescribed by
the existing factor definitions. Transport from the stated standard-character
hypotheses to those sign conventions is part of the future proof.

Writing `X=q^(-s)`, the intended reverse relation is
`1/Pbase = Q/Pind`, hence `Pind=Q*Pbase` and `Pbase ∣ Pind`.
An integral proof may first produce Laurent ideal membership. Clearing powers
of `X` and using `Pbase(0)=1` must then justify the polynomial divisibility.
These observations explain the target's direction; this module proves neither
that membership nor that divisibility.

## Lifted carrier and whole-block reversal

The field universe `uF`, test-carrier universe `uV`, and base-carrier universe
`uW` are independent. Exactly as in the restricted published target, `χlift`
is obtained by composing `rankOneCharacter (χ : F.Carrierˣ →* Complexˣ)` with
`ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom`. It acts on
`ULift.{uW} Complex`; on `ULift.up z` its action is
`ULift.up ((χ (determinant g) : Complex) * z)`.
The pair carrier is `Shahidi.pairCarrier (ULift.{uW} Complex) W`, and the
induced carrier lies in `Type (max uF uW)`. The base certificate retains `σ₁`
on its original `W`, and the test remains on `V`.

The source lower ordered induction `(σ₁,χ)` must be transported to the upper
ordered induction `(χ,σ₁)`. The permutation reverses whole blocks and preserves
coordinates within each block. The tensor factors must be reindexed as well.
The lower normalizing character is the inverse upper half modulus for the
original shape; after reversal it matches the upper half modulus for the
reversed shape. For upper blocks `(a,g)` of ranks `(1,t+1)`, this is
`|a|^((t+1)/2) |det g|^(-1/2)`.

The separate published interface
`Langlands.GLOppositeProductReversalStatement`, in
`Langlands.Representation.Induction.OppositeProductReversalStatement`, prescribes
the maps `f ↦ (x ↦ R(f(w*x)))` and
`h ↦ (x ↦ R.symm(h(w⁻¹*x)))`, with `R` the actual tensor reindexing.
Its proof and the shape/carrier identification with this exact two-block
constructor remain separate obligations. This proposition does not assume that
interface or identify the two possible upper block orders.

## Separate proof obligations and dependency direction

A successor proof must establish the equal-rank integral or ideal comparison
independently, including its Schwartz-function variable, convergence and rational
continuations, compatible measures, and both certified factor existences.
It must justify Whittaker type of the actual normalized induction from the
factor hypotheses, carry out the lower-to-upper whole-block and carrier
transport, and derive the stated polynomial divisibility. The compact-section
and Fourier-smoothing proof on printed 424–427 explains the strict-rank source
lemma; it does not by itself provide an equal-rank proof with a Schwartz variable.

This endpoint is upstream of the general two-block section 7 assembly, finite-block
multiplicativity and the later section 9.3 tail result. None of those full results
may be used to justify its future proof. Existing proposition definitions and
pending proof tasks provide no proof evidence. Independent semantic acceptance
and Library publication of this statement must precede the separate proof
successor; publication of this pair will establish only the statement target.
