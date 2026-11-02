# Tail L-polynomial divisibility for upper two-block induction

Author: Worker 53.

`Langlands.RankinSelberg.inducedTailLFactor` proves exactly the published
[`InducedTailLFactorStatement`](InducedTailLFactorStatement.md) at the four
independent universes `uF`, `uV₁`, `uV₂`, and `uW`. For arbitrary positive
ordered block ranks `A`, `B` and positive test rank `T`, it constructs
polynomials `Pfull` and `Ptail` with complete
`IsPadicSymmetricLPolynomial` certificates for the full induced pair and the
second block against the test, and proves `Ptail ∣ Pfull` in `ℂ[X]`.
All three original representations may be reducible and satisfy the
existing full Whittaker-type predicate.

The full representation is the target's actual
`F.canonicalNormalizedProductInduced` of `Shahidi.twoBlocks A B` and
`Shahidi.pairFamily` on the two explicitly `ULift`-conjugated actions.
The ordered second block retains its original carrier in the tail
certificate. The theorem quantifies over every canonical p-adic field,
nontrivial continuous unitary additive character, and supplied self-dual
Haar measure. Each certificate includes existence of a compatible quotient
measure, its universal measure clause, the actual rational-zeta Laurent
span, and constant coefficient one.

The implementation applies
[`inducedTailConditionalAssembly`](InducedTailConditionalAssemblyProof.md)
to these six closed Library results, in the order required by that assembly:

| Prerequisite | Supplied theorem |
| --- | --- |
| Three direct-rank Laurent-span inclusions | `inducedTailSpan` |
| Full Whittaker type of normalized product induction | `normalizedProductWhittakerType` |
| Certified symmetric L-polynomial existence | `symmetricLPolynomialExists` |
| Opposite two-block L-divisibility | `twoBlockLFactorMultiplicativity` |
| Actual ordered heterogeneous three-block associativity | `Parabolic.threeBlockInductionAssociativity` |
| Full Whittaker-type high-ramification vanishing | `whittakerTypeHighlyRamifiedLVanishing` |

For the first five inputs all carrier universes are specialized to
`u = max uF uV₁ uV₂ uW`. The last input uses first carrier universe zero
for the scalar character and second carrier universe `u`. The field
universe remains `uF` throughout. The assembly's actual representation
equivalences transport the common-universe conclusion to the original
independent universes, including the literal lifts in the target. The
polynomials and their divisibility are retained by this transport.

The imported assembly handles the four rank ranges as follows. Below the
full induced rank `A+B`, the direct assembly applies the equal-tail-rank,
smaller-test-rank, or intermediate-rank span inclusion according as `T=B`,
`T<B`, or `B<T<A+B`. These are the three closed clauses of
[`inducedTailSpan`](InducedTailSpanProof.md). Full Whittaker type and common
factor existence supply the certified factors needed to turn the actual
span inclusions into divisibility.

For `T≥A+B`, the assembly prepends one sufficiently ramified scalar
character and inducts on the remaining rank deficit, keeping the original
second block and test fixed. Writing `ξ=ρ×π₂`, it compares
`η=μ×ξ` with `(μ×ρ)×π₂` through the exact ordered associator, including
its ambient rank cast. The induction gives `Ptail ∣ Pη`. High-ramification
vanishing supplies the certificate `1` for `μ` against the test. The
opposite two-block theorem then gives
`X^k * Pfull = Q * Pη`, hence `Ptail ∣ X^k * Pfull`.
The tail certificate implies `Ptail(0)=1`; the assembly constructs a Bezout
identity with `X` and removes the power of `X`. This yields ordinary
polynomial divisibility `Ptail ∣ Pfull`, including at equality with the full
rank. Existence of both factors is proved within the assembly from the
closed existence and full-type inputs.

Provenance is internal composition of the named Library results. Its source
interpretation is the derived Whittaker-type extension of Jacquet,
Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions* (1983),
Lemma (9.3), printed pp.455–457, with the extension/localization constructions
of §§9.1–9.2, printed pp.452–455. The literal lemma's generic test
representation and the derived full Whittaker-type scope are distinguished
in the published target explanation. The original proof and registered
errata were read during this task. The source is registered as
`jpss-1983-rankin-selberg`, with SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

The opposite-divisibility theorem implements the separate Section 7
descent using its restricted Section 5.5 comparison and a separately proved
equal-rank endpoint. Its imports contain technical Section 9.1 integral
adapters, and do not consume the Section 9.3 tail conclusion. The general
high-ramification proof is independent of L-multiplicativity. Thus supplying
these closed theorems preserves the required dependency direction. This
module adds only the final closed theorem; its target pair and imported
pairs are unchanged.
