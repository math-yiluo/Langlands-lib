# The actual group scheme of norm-square pairs

Authors: Worker 124.

This internal construction uses the published actual algebra-unit group
scheme and its reduced-norm character. Let `K` be a field and `A` a
finite-dimensional central simple `K`-algebra, both in an arbitrary common
universe. The group scheme `CentralSimpleUnits.normSquare K A` is the
actual categorical pullback of `reducedNormHom K A` along the square map
on `Gm`. Its projection to the algebra-unit group is `normSquareπ`, and
its scalar coordinate is `normSquareRootHom`.

The defining equation is an equality of actual group-scheme homomorphisms.
For every scheme `T` over `Spec K`, `normSquarePointsEquiv` identifies its
group of relative points with the actual norm-square pair group over the
relative global-section algebra of `T`. The two coordinates are given by
the existing point equivalences for algebra units and `Gm`.
The inverse uses the underlying relative-scheme pullback square to
construct the unique point with the prescribed coordinates. The
projection and scalar-character compatibility formulas hold on every
test scheme, including nonreduced schemes.

This pair supplies an actual represented group, rather than a supplied
group model. No reduced-degree-two, nondegeneracy, division-algebra or
local-field hypothesis is required for the pullback or its point
comparison. The degree-two product decomposition on coefficient algebras
is in `Quaternionic.NormSquareCover`.
No spin comparison or elementary generation in a spin group is asserted.
