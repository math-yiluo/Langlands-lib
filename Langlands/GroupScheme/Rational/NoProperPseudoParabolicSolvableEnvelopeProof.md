# Common solvable envelope without proper pseudo-parabolic subgroups

Author: Worker 1413.

`Langlands.GroupScheme.noProperPseudoParabolicSolvableEnvelope` proves the exact
published proposition
`Langlands.GroupScheme.NoProperPseudoParabolicSolvableEnvelopeStatement.{u}`
(module `Langlands.GroupScheme.Rational.NoProperPseudoParabolicSolvableEnvelopeStatement`)
at arbitrary universe `u`. For every field `k : Type u` and every smooth,
connected, affine group scheme `G` over `Spec k` with no proper
pseudo-parabolic subgroup, it gives one closed subgroup `j : H ⟶ G` with `H`
smooth, connected, affine and solvable, through which every split subtorus
`i : S.toGrp ⟶ G` factors as `f ≫ j = i`. No perfectness, characteristic,
splitting or reductivity hypothesis is added.

## Mathematical route

This is the first branch of the proof of Theorem C.2.3 in
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
printed pp.593–594, using Lemma 2.2.3(1), printed pp.62–63 (registered source
`conrad-gabber-prasad-2015-pseudo-reductive`). Let `U` be the ground-field
unipotent radical of `G` and `q : G → Q` the quotient by it. Without a proper
pseudo-parabolic subgroup, every split subtorus of `G` becomes central in `Q`,
so it maps into the largest central split torus `B` of `Q`. The preimage of
`B` in `G` is the envelope `H`.

## Implemented proof

The theorem is a term combining published results; it introduces no new
hypothesis.

- `noProperPseudoParabolicSolvableEnvelope_of_statements`
  (module `Rational.NoProperPseudoParabolicSolvableEnvelopeReduction`)
  derives the target from four propositions. It takes `U, r` from radical
  existence and `Q, q` from the quotient proposition. It takes `B` from
  `exists_largestCentralSplitTorus Q` and `H, j` from the preimage
  proposition. For a split subtorus `i`, the centrality proposition makes
  `i ≫ q` central. Then `i ≫ q` factors through `B`, and the preimage
  property factors `i` through `j`.
- Radical existence is `unipotentRadicalExistence`
  (module `Reductive.UnipotentRadicalExistenceProof`), proving
  `UnipotentRadicalExistenceStatement`.
- The quotient is `unipotentRadicalQuotient`
  (module `Reductive.UnipotentRadicalQuotientProof`), proving
  `UnipotentRadicalQuotientStatement`: an actual fppf quotient `Q` by the
  radical, which is pseudo-reductive.
- The preimage construction is `unipotentQuotientSplitTorusPreimageStatement`
  (module `Rational.UnipotentQuotientSplitTorusPreimageProof`). For a central
  split torus of `Q`, it gives a closed preimage subgroup of `G` that is smooth,
  connected, affine and solvable. A homomorphism to `G` factors through that
  preimage when its composite with `q` factors through the torus.
- Centrality of split subtori modulo the radical,
  `NoProperPseudoParabolicSplitTorusCentralStatement`, is obtained from
  `noProperPseudoParabolicSplitTorusCentral_of_smooth_statements`
  (module `Rational.NoProperPseudoParabolicSplitTorusCentralSmoothReduction`),
  applied to two proved propositions:
  - `smoothConnectedNormalFactorFppfProductExistence`
    (module `SubgroupFunctor.SmoothConnectedNormalFactorProduct`):
    represented smooth connected products of a smooth connected closed
    subgroup with a smooth connected normal one;
  - `DynamicUnipotentUnipotenceStatement`, unipotence of `U_G(χ)`, from
    `dynamicUnipotentUnipotenceReduction`
    (module `Dynamic.UnipotentUnipotenceReduction`) applied to
    `unitriangularUnipotent` (module `UnitriangularUnipotentProof`) and
    `unipotentClosedSubgroup` (module `UnipotentClosedSubgroupProof`).

Each component is the published proof of the proposition named above; the
Lean term only instantiates the reductions with them.
