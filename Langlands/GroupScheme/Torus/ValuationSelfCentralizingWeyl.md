# Arbitrary-base finite Weyl models from valuation affineness

Author: Worker 640.

`Langlands.GroupScheme.SelfCentralizingWeyl.valuationFiniteWeylModel`
constructs the actual `FiniteWeylModel t` over every scheme `S` and every universe
`u`, with two explicit proof inputs:

- `SelfCentralizingTorusWeylAffinenessStatement.{u}`;
- affineness of every quasi-compact separated etale scheme over every valuation
  subring `A` of every algebraically closed field `K : Type u`.

It assumes smoothness, separatedness and quasi-compactness of the ambient group,
connected reductivity of its actual residue fibres, and a supplied closed
self-centralizing fibrewise-maximal relative torus. It returns actual normalizer
and Weyl quotient group schemes with the closed represented inclusion, smooth
normalizer, finite etale quotient, flat surjective locally finitely presented
projection, all-test kernel equality with the torus, and affineness of the
ambient group. Selection of the supplied criterion's witnesses uses classical
choice. Neither proof input is proved by this constructor.

## Implemented proof

`HasAlgClosedValuationLifts.baseChange` proves stability of the restricted
valuative existence condition under arbitrary base change. Compose the square
with the original pullback projection, use its lift, and reconstruct a lift
into the pullback; the pullback property proves both triangle identities.

`hasAlgClosedValuationLifts_of_finite_pullbacks` proves the condition whenever
every algebraically closed valuation pullback is finite: the pullback is
universally closed and therefore has valuative lifts. Compose such a lift with
the projection to the original source.

`isFinite_etale_of_algClosed_valuation_pullbacks` proves finiteness of a
quasi-compact separated etale morphism over an arbitrary base from these finite
pullbacks. The preceding lift condition is stable under every base change;
`specializingMap_of_algClosed_valuation_lifts` makes each pullback a specializing
map. The published `EtaleLocalCardinality.finite_of_specializing_pullbacks`
then proves universal closedness and hence proper quasi-finite finiteness.
This uses no Noetherian condition and no assumption that DVR tests suffice.

`isAffineHom_over_algClosed_valuation` applies the supplied structural criterion
to obtain a quasi-compact separated etale quotient over `Spec A`. The supplied
valuation affineness hypothesis makes that quotient affine, and the criterion
makes the original group affine.

`isFinite_suppliedWeyl_of_valuation_affineness` applies the finite-pullback test
to an arbitrary supplied actual Weyl quotient. After valuation base change,
residue reductivity and fibrewise torus maximality persist, the full centralizer
is still represented by the torus, and the preceding step makes the ambient
group affine. It is then reductive, so the existing reductive Weyl finiteness
reduction applies to the supplied pulled-back quotient. The normalizer and
all-test kernel conditions are transported by their actual base-change lemmas.
The final constructor selects criterion data, proves this quotient finite,
and uses the criterion's affineness equivalence for its last field.

## Provenance and remaining obligations

This is an internal composition of Library and Mathlib primitives. It reuses the
Noetherian module's actual `FiniteWeylModel` structure and its maximal-torus
transport lemmas. Its proof does not use the Noetherian DVR test. No new source
text is transcribed.

The valuation-subring etale-affineness hypothesis is a separate mathematical
input under investigation. This module does not assert it unconditionally,
prove the Weyl-affineness criterion, construct the torus, or prove Task 7526's
unchanged target. It supplies the arbitrary-base assembly once those inputs
are available.
