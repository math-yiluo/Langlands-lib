# Actual normalized rational geometric terms

This internal adapter packages the source Jacquet and target induction
preservation derived by `RationalSourceJacquet` and
`RationalTargetInductionComparison` for every minimum point Weyl
representative and every normalizer lift. It retains their structural
inputs and the canonical evaluation topology `pointTopology`.

`pointGeometricTermFiniteLength` derives all four conjuncts of
`GeometricTermFiniteLength` from literal restricted induction preservation
inside the target coarse Levi, literal restricted Jacquet preservation
inside the source coarse Levi, and their topological exactness results.
The actual source and target decompositions are derived by the named
rational intersection adapters. Neither decomposition nor preservation
of the actual geometric factors is an extra input.

`pointGeometricTermK0` specializes the existing actual geometric-term map
using those derived witnesses. Its three factors are actual source
Jacquet restriction, actual inverse-conjugation pullback for the supplied
normalizer lift, and actual target normalized induction. The composite
identity `pointGeometricTermK0_eq_composite` unfolds this construction to
the previously constructed source and target exact K0 maps. All carriers
have independent-universe scope `max (u + 1) v`, and the maps are defined
on the full exact finite-length Grothendieck groups with the existing
Haar normalization.

The provenance is internal composition of the named rational adapters and
`geometricTermK0`. The point normalizer/full-centralizer comparisons,
standard Levi intersection statement and both all-test twisted-intersection
properties remain structural inputs. The geometric expansion, normalized
stages, comparison with literal standard terms and final Aubert induction
equation remain separate obligations; the final target is unchanged.
