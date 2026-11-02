# Smooth sheaf cohomology on actual induced rational spectra

This is an internal specialization of the full locally constant smooth sheaf,
its compact-section comparison, and the existing smooth Godement and injective
derived compact-section constructions. The space is the actual balanced
quotient `X.InducedSpectrum` of the rational quotient spectrum associated to an
open-subgroup transport object `X`; it is not supplied as an unspecified input
space.

The valued field, operator group, coefficient ring and module carriers share
universe `u`, as required by the existing smooth Godement and derived APIs.
The field is complete and nonarchimedean, the coefficients form a commutative
ring, and the operator group is a topological group. The induced action already
has joint continuity. `HasStableNeighbourhoods G X.InducedSpectrum` remains an
explicit spatial hypothesis. Each coefficient object is an arbitrary smooth
module representation; no topology on its carrier is used.

`sheafFunctor` constructs the full ordinary-open locally constant sheaf on
this spectrum and retains every pointwise coefficient map. Its smoothness is
the previously proved local fixedness of every original section. The natural
isomorphism `compactSectionsIso` identifies its full compact-section functor
with the existing `CompactSections.coefficientFunctor X`. In particular the
functions and the action `g.f(z) = rho(g)(f(g inverse acting on z))` are the
original ones. No smooth-vector submodule replaces the full functions.

`godementCompactComplex` applies the actual smooth Godement complex functor
to this sheaf and takes compact sections term by term in smooth
representations. `godementCompactCohomology q` takes its categorical homology.
`godementCompactCohomologyZeroIso` composes the general degree-zero theorem
with the inverse of `compactSectionsIso`, so it recovers the actual full
compact functions naturally in all coefficient intertwiners.

`compactDerived q` evaluates the right derived compact-section functor of
the smooth sheaf category on the same constructed sheaf. This is not an
assertion that it is the right derived functor of the composite coefficient
functor. `compactDerivedIso` identifies its value with compact-section
homology of any injective resolution of that sheaf, using the existing
resolution comparison. `compactDerivedZeroIso` recovers the same full compact
functions in degree zero. Composing the two identifications gives
`godementDerivedZeroIso`; its proved compatibility equation states that
composing its forward map with the derived compact-function identification
equals the Godement compact-function identification.

The provenance is internal: all complexes, cohomology functors and natural
isomorphisms are the indicated compositions of existing constructions. This
module concerns ordinary opens on an actual rational induced spectrum.
It asserts no analytic or etale site identification, no higher Godement versus
derived comparison or acyclicity, and no arithmetic tower, uniformization or
Harris specialization.
