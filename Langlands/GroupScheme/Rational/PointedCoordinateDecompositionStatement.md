# Split-torus decomposition on actual pointed affine schemes

`PointedCoordinateWeights.PointedCoordinateDecompositionStatement` is an
unproved proposition, uniform in every universe `u` and every field `k`.
For an actual split-torus action on a pointed affine scheme with fixed
rational point, it asserts internal direct-sum decompositions of the
actual coordinate algebra and its fixed-point augmentation ideal into
their character eigenspaces. Internal direct sum asserts both spanning
by finite sums and independence. The scheme need not have a group law,
be reduced, or be of finite type. No characteristic restriction or
finite-dimensionality hypothesis is imposed.

This is the general pointed-scheme decomposition behind the augmentation
weights used in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second
edition (2015), §3.3, printed pp.107–108 (PDF pp.133–134), registered source
`conrad-gabber-prasad-2015-pseudo-reductive`. The book considers
geometrically integral stable pointed closed subschemes, including
commutator-image closures. The broader target here is derived from the
split-torus action on actual affine coordinates. Its eigencondition is
`f(s.v) = χ(s) f(v)` after every commutative coefficient algebra change,
using the actual morphism and the existing character lattice.

This file defines the precise target and does not prove it. In
particular, it supplies no assumed grading as input. Its focused proof
successor must construct the decomposition from the given split torus
and actual action and identify its character spaces with these
all-algebra eigenconditions. Cotangent decomposition and the
cotangent/Lie comparison remain separate targets in the group-specific
`CoordinateWeightDecompositionStatement` and
`CoordinateLieComparisonStatement` modules.
