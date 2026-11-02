# Canonical topology and evaluation of actual rational characters

Author: Worker 200.

This derived adapter identifies the two published evaluation topologies on
actual base-valued points of an affine group scheme. It then bundles the
existing actual rational-character evaluation as a continuous homomorphism
for the published named rational-point topology.

## Source and provenance

Waldspurger 2003, I.1, printed pp.238–240 (PDF pp.4–6), registered as
`waldspurger-2003-plancherel`, defines the actual rational characters and
their normalized absolute values on rational points. In particular, printed
p.239 treats these absolute-value characters as continuous characters.
Renard, 9 July 2026 edition, V.1–V.2.3, printed pp.103–106 (PDF pp.109–112),
registered as `renard-2026-representations-groupes-reductifs-padiques`,
uses the usual rational-point topology and actual character evaluations
in the definition of the integer valuation map.

The present content is a host comparison and an intrinsic continuity
construction from already published definitions, rather than a new
structural assumption from either source. It uses
`PointTopology.rationalPointTopology`, `rationalPointEquiv`,
`GroupScheme.affinePointEvaluation`, and
`Gm.continuous_affineUnitsEquiv`. It preserves the actual scheme morphisms,
regular functions, units topology and evaluation maps of those modules.

## Inputs

Let `R : Type u` be a commutative ring with an arbitrary topology, and let
`G : Langlands.GroupScheme (Spec (CommRingCat.of R))` have affine underlying
scheme. The universe is arbitrary. No field, characteristic, reductivity,
connectedness, finiteness or continuity-of-ring-operations assumption is
needed for this construction.

The rational points are the existing `GroupScheme.rationalPoints G`, tested
by the identity map of `Spec R`. Their topology is explicitly the existing
`PointTopology.rationalPointTopology R G.X`. The affine points are the
existing `G.affinePoints (CommAlgCat.of (CommRingCat.of R) R)`, with their
regular-function evaluation topology. The module declares no global
topology instance on rational points.

## Constructions and implemented argument

All new declarations lie in `Langlands.GroupScheme`.

`affineSchemePointEquiv_apply_eq_evaluation` proves that the published
affine-scheme point equivalence evaluates a global section exactly as
`G.affinePointEvaluation` does. The two formulas are respectively spectrum
preimage and pullback of global sections followed by `Scheme.ΓSpecIso`.
Faithfulness of `Spec`, the spectrum/global-sections identification, and
naturality of the canonical affine isomorphism prove their equality.
This identity does not use the topology of `R`.

`ringPointTopology_eq_affinePoints` identifies the existing topology on
`RingPoint R G.X R` with `G.affinePointsTopologicalSpace` on the same
carrier. The first topology is induced through the affine point equivalence
and then through algebra-point evaluation. Composition of induced
topologies and the preceding evaluation identity give the second topology.

`rationalPointsAffineHomeomorph` upgrades the existing carrier equivalence
`rationalPointEquiv R G.X` to a homeomorphism with the affine points. Its
source topology is explicitly `rationalPointTopology R G.X`, and its target
topology is explicitly `G.affinePointsTopologicalSpace`.
`rationalPointsAffineHomeomorph_left` proves that it preserves the
underlying scheme morphism.

`rationalCharacterEval_eq_affineUnitsEquiv` identifies the existing
`rationalCharacterEval chi` with transport to affine points, postcomposition
by the actual algebraic character, and the existing
`Gm.affineUnitsEquiv`. Naturality of represented units under the canonical
identity-test isomorphism proves this identity. It requires neither
affineness nor a topology.

`continuous_rationalCharacterEval` composes the preceding homeomorphism,
the published continuity of postcomposition on affine points, and
`Gm.continuous_affineUnitsEquiv`. The evaluation identity identifies this
continuous composite with the actual rational-character evaluation.
`rationalCharacterContinuousEval` bundles that same monoid homomorphism
as a continuous monoid homomorphism to `Rˣ`, using only a local binding of
the named source topology. Its `_apply` lemma is the original evaluation
formula without a change to the underlying map.

## Scope

This supplies actual character-evaluation continuity on the canonical
rational-point topology. Continuity and local constancy of normalized
local-field norms require their separate field results. Openness of the
common kernel, continuity of the projection to the explicitly discrete
valuation image, local compactness, compact-open subgroups, finite-rank
image lattices, finite-dimensional character tori, split-center comparison
and Haar measures are separate obligations.
