# Root-subgroup images and coordinates for a split isogeny

`isogenyRootSubgroup` proves the unchanged published
`IsogenyRootSubgroupStatement` in every universe over an arbitrary field. It
uses the supplied actual split maximal tori, finite-flat-surjective ambient
isogeny, commuting torus square, reduced root data on the actual lattices, and
the supplied compatible root-datum isogeny. It retains arbitrary whole-root
equivariant additive parametrizations and every test scheme.

For each target root, the root-restriction theorem proves that the corresponding
source root has that whole target root subgroup as its actual fppf image.
Conversely, fppf-image minimality and distinct-root incomparability force any
source root with this image to have the prescribed index. These are statements
of actual subgroup functors and fppf-local lifting, with no assertion of point
surjectivity on the original test scheme.

For the coordinate assertion, the represented-subgroup restriction constructs
the actual homomorphism between the two supplied additive lines. It is an
isogeny by the finite equal-Lie-dimension argument; its flatness and surjectivity
make the underlying relative morphism an epimorphism. Its inclusion square is
the given ambient map evaluated in those parametrizations.

The helper `RelativeRoot.scalarPoint_comp_of_rootDatumIsogeny` uses the supplied
root-datum isogeny's root equation and its compatibility with the actual torus
map. The integer multiple in that equation is the same natural-number multiple
used by the polynomial theorem. The target representative is monic because it
represents the whole root subgroup, so the ambient commuting square and the
two conjugation laws imply equivariance of the actual restriction.

The prescribed-degree vector-line theorem gives one unit over the original
field before any test scheme is chosen. Its proof compares the polynomial's
weight equation with the supplied one in the rational span of the character
lattice; the nonzero source root forces the degree to equal the supplied root
factor. The all-test transfer gives the formula on every scheme test with the
coefficient pulled back along its structure morphism. Composing with the target
representative gives the required ambient-group equality. No test-affineness,
reducedness, perfection, separability or smooth-kernel premise is introduced.

This is an internal derived assembly of the actual-root restriction, fppf-image
and prescribed-coordinate results. It proves the published target associated
with Milne (2017), Proposition 23.5, formulas (144)–(146), while using the
implemented finite-dimension and natural-coordinate proof routes described
above. Existence of the compatible lattice map is supplied by the target's
hypotheses, as are both lattice compatibility equations.
