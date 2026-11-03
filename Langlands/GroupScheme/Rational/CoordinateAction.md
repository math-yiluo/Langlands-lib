# Actual coordinate actions and augmentation eigenspaces

This derived construction implements the coordinate convention of Conrad–Gabber–Prasad,
*Pseudo-reductive Groups*, second edition (2015), §3.3, printed pp.107–108
(PDF pp.133–134), registered source `conrad-gabber-prasad-2015-pseudo-reductive`.
It uses the existing actual affine coordinates, points and automorphic action.
The arbitrary universe and all commutative test algebras are retained, in every
field characteristic. No splitness, smoothness or finite type is needed here.

The module reuses `CharacterUnits.Coord`, which is precisely
`Lie.coordinateAlgebra`, and `CharacterUnits.universalPoint`. `pullback` is the coordinate map of
an actual morphism over the base, obtained from its value at the universal point.
Its evaluation formula, identity and composition laws follow from naturality of
`Lie.pointCoordinates`. `evaluate` is the algebra map from `A ⊗ O(G)` to `A`
specified by an actual `A`-point.

`actionCoordinates` applies the actual action to the two points over
`A ⊗ O(G)`: the extended acting point and the universal target point.
`actionPullback` extends this to an `A`-algebra endomorphism. The two evaluation
lemmas prove the exact convention `(s.f)(g) = f(b.act s g)` for every test
algebra, point of the torus and point of the target. Algebra compatibility is
intrinsic in these bundled algebra maps. `action_preserves_origin` follows
from the actual action fixing the identity and expresses augmentation stability.

`weightSpace` consists directly of functions satisfying this all-algebra
eigencondition. `augmentationIdeal` and its scalar restriction `augmentation`
are the kernels of the actual identity augmentation. `augmentationWeightSpace`
is its eigenspace. `support` means existence of a nonzero eigenfunction in the
augmentation ideal; it does not exclude the zero character. The empty support
in the trivial case remains possible.

`IsEquivariant` tests actual scheme maps on all schemes. Equivariant pullback
preserves eigenfunctions by the coordinate evaluation formula.
Group homomorphisms preserve augmentation and give `augmentationPullback`.
The existing `onRepresentedSubgroup` inclusion is proved equivariant, so these
constructions apply to represented stable subgroups without choosing an
unrelated grading. Decomposition, quotient weight lifting and comparison with
Lie support are subsequent proposition targets, not consequences asserted here.

`actionPullback_one` and `actionPullback_mul` prove the action laws, with
composition reversed as for pullbacks. Commutativity of the acting group makes
this also an ordinary left action. `actionAut` uses the inverse acting point
to obtain an actual `A`-algebra automorphism. The proofs use the action on the
universal point, its naturality under algebra maps, and the fact that coefficient
scalars are fixed; they impose no rational-point density assumption.

`pullback_weightSpace_iso` proves preservation and reflection of coordinate
weights under every equivariant isomorphism of underlying schemes. Its inverse
is equivariant by cancellation. `augmentationPullback_mem` gives the corresponding
preservation on augmentation eigenspaces for group homomorphisms, and
`support_subset_of_injective` transfers nonzero support along injective pullback.
These lemmas do not assert that dominance implies injectivity or that closed
immersions lift eigenfunctions. Those geometric and decomposition results remain
explicit successor targets. For a pointed stable subvariety which is not a group,
the present objects do not define its coordinate support; a stable augmented
quotient-algebra extension is needed to apply the commutator-image argument.
