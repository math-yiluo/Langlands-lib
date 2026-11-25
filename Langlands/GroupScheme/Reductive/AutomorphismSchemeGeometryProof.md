# Full relative reductive automorphism-scheme geometry

The proof composes the complete local classification and global
descent constructions.

`Langlands.GroupScheme.reductiveAutomorphismSchemeGeometry.{u}` proves
exactly the unchanged Library proposition
`Langlands.GroupScheme.ReductiveAutomorphismSchemeGeometryStatement.{u}`.
The theorem has no extra arguments or hypotheses. It applies to every base
scheme and every reductive group scheme in the universe `u`, with the full
all-test automorphism functor, including nonaffine, disconnected and
nonreduced tests.

The proof applies
`reductiveAutomorphismSchemeGeometry_of_pinnedLocalRepresentatives`
to three established inputs. The independently proved
`pinnedOuterIsomorphismChart` supplies the charts for full Isom
representatives, and `relativeAdjointQuotientExistence` supplies the
full-centre quotient. For the local Aut schemes,
`affinePinnedAutomorphismRepresentatives_of_pinnedClassification` applies
the representation-free construction using `affinePinnedIsomorphismTheorem`.
That construction uses the existing local label completeness and natural
local pinned normalization theorems.

The local Aut construction assembles canonical full-character-lattice pinned
comparisons into an actual family over a possibly infinite constant scheme.
Original-test label descent and unique adjoint discrepancy give a
representation-free bijective inverse-precomposition decomposition on every
test. The normalized-family constructor builds the full local Aut scheme
as adjoint group times that constant scheme, with smooth separated structure
map.

For the global construction, an actual affine pinned étale atlas identifies
the group pullbacks with those models. Their full Aut representatives glue
on the canonical open cover of the atlas disjoint union. Independent
full-centre quotient existence supplies a faithful inner action over the
original base. The supplied-Isom pinned chart construction provides the
local separated étale outer quotient with affine class map. Affine
single-cover effectivity then constructs the full original-base Aut scheme.
All-test parameter uniqueness identifies its pullbacks with the local
models; fppf target descent proves smoothness and separatedness.

For every independently supplied relative adjoint quotient, the pinned
charts give the representation of the canonical action quotient.
The local finite presentation and affineness proofs apply the published
represented-quotient theorems to its class map. Complete normalized families
identify the outer parameter pulled back to each pinned chart with the
actual constant parameter. This gives a separated étale outer parameter
and the slice isomorphisms that witness local constancy. The published closed-orbit
theorem gives a closed immersion for the orbit through the identity.
Precomposition with group inversion gives the positive
inner-automorphism map required by the target.

This is an internal composite proof of the selected geometry of Conrad,
*Reductive group schemes* (2014), Theorem 7.1.9(1), pp. 245–247. The
affine-quotient descent follows the argument on p. 246. The formalization
retains the target's arbitrary base and test schemes, all universes, and
possibly infinite outer parameters.
