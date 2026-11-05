# Reduction of the conditional intertwining theorem to its remaining inputs

Author: Worker 1615.

This module is a supporting construction for the host task proving
`Langlands.Plancherel.ConditionalParabolicIntertwiningStatement`. It states
precisely what remains to be proved and proves that this suffices.

## The inputs proposition

`ConditionalParabolicIntertwiningInputs` has exactly the binders, local
instances and `let` definitions of the published
`ConditionalParabolicIntertwiningStatement`. These are: every nonarchimedean
local field `F`, every connected reductive group `G`, the presentations `r`
and `r'` with the same Levi composite and split component, the geometric
radicals `n`, `n'` and `v`, the parabolic `q`, the Weyl form `B`, the region
`C := parabolicPointUnramifiedIntertwiningRegion r B n q v`, the point
subgroups, the semidirect decompositions, `K`, the projections, the quotient
measures, and every admissible finite-length smooth representation `π` of the
literal Levi point subgroup. Its conclusion asserts:

- the published `SquaredModulusCompatibility h hU h' hU'` of the two actual
  radicals; and
- one real threshold `R` such that the published actual standard-integral
  `domain` is the whole source at every parameter of `C R`, and, for every
  radical-unimodularity proof `hδ`, the published
  `CompactIntegralLocallyDominatedOn` holds on `C R` itself.

It is a proposition, not an assertion, and nothing here proves it.

## The theorem

`conditionalParabolicIntertwiningStatement_of_inputs`: for all universes,
`ConditionalParabolicIntertwiningInputs.{u, uV}` implies
`ConditionalParabolicIntertwiningStatement.{u, uV, uW}`.

Proof. After introducing all data, apply the inputs to the same data. This
gives the squared-modulus compatibility, the threshold `R`, convergence on
`C R` and domination. Then:

- radical unimodularity of both radicals is the published
  `parabolicRadical_isUnimodular`;
- `C R` is nonempty by the published
  `parabolicPointUnramifiedIntertwiningRegion_nonempty`, with the published
  `weylInducedCharacterForm_nondegenerate`;
- `C R` is open by the published
  `isOpen_parabolicPointUnramifiedIntertwiningRegion`;
- domination on the twist-orbit saturation of `C R` follows from domination
  on the open set `C R` by `compactIntegralLocallyDominatedOn_saturation` of
  `CompactIntegralSaturation`;
- the remaining conjuncts (openness of the orbit region, full convergence on
  the saturation, `StandardCompactRationalOn` and representative naturality) are
  `parabolicLevi_intertwiningConclusion_of_dominated` of the published
  `ParabolicIntertwiningAssembly`. Its analytic-input predicate is supplied by
  nonemptiness, openness, convergence and the transported domination. Its
  defining equalities for the point subgroups hold by `rfl`.

The local instances of the statement (affine and smooth ambient group,
point topology, and the two monomorphism instances of the presentation) are
re-established in the proof, and separatedness comes from `hG.isSeparated`.

## Scope and provenance

The module does not prove squared-modulus compatibility, convergence or
domination. It does not prove the host theorem, and it adds no premise to it.
The inputs proposition records exactly the obligations still open. All steps
are compositions of the published declarations named above and of
`CompactIntegralSaturation`; no literature theorem replaces a proof.
