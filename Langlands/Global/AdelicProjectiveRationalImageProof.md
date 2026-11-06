# The proper, nonclosed and nondiscrete rational projective image

`adelicProjectiveRationalImage` proves the unchanged
`AdelicProjectiveRationalImageStatement`, by proving its function-field and
number-field clauses separately. The source is Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.10,
the paragraph preceding Example 4.3 and Example 4.3, registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The implemented proof uses the previously proved rational density and
full-product comparison, together with the absence of isolated points in the
actual local projective spaces.

The points are actual morphisms over the spectrum of the original global
field into polynomial-Proj projective n-space. The principal map is scalar
extension along the original field diagonal into its full adele ring. Its
target carries the independently constructed arithmetic model topology, and
the previously proved projective comparison identifies this topology with
the product of all actual local point topologies. The number-field product
includes every infinite factor as well as every finite factor.

Scalar extension on actual scheme points along any field extension is
injective. The proof uses faithful flatness of the field algebra map and the
flat-surjective characterization of its spectrum map, which makes that
spectrum map an epimorphism. Cancellation on the underlying scheme morphisms
then gives equality of the original relative points. The affine chart point
map is also injective: cancel its open immersion and use faithfulness of
spectrum followed by evaluation on the polynomial generators. In positive
dimension the affine coordinate index is nonempty, so this chart injects a
nontrivial function space into the rational projective point set.

A family of injective maps from a nontrivial set to factors indexed by at
least two indices cannot give a surjective diagonal map. Choose distinct
rational points and distinct indices, and form a family using the first
point at the first index and the second point elsewhere. A rational preimage
would have to equal both chosen rational points. The proved infinitude of
actual curve places and of actual number-field finite places supplies these
indices. Composition of the principal map with each actual adelic projection
is precisely direct scalar extension to that completion: this is checked by
the contravariant composition law for spectrum maps and the identity for an
algebra homomorphism composed with the base algebra map. The projective
comparison is surjective, so the obstruction in the local product proves
nonsurjectivity of the adelic principal map. For number fields it suffices to
project to the finite component; an infinite-component family exists by
scalar extending a rational projective point.

Every actual curve-place or finite number-field completion has no isolated
points. This follows from its existing nontrivial rank-one valuation and its
associated nontrivially normed field structure, with the original topology.
The image of a continuous injection from a space without isolated points is
preperfect: pull a neighborhood back and choose another source point in it.
A function-space product has no isolated points whenever one factor has none,
as shown by varying that factor with the continuous injective update map.
In positive dimension, every standard projective chart has a nonempty
coordinate index, so its coordinate space has no isolated points. Chart
coverage, chart continuity and chart injectivity show the same for every
point in the actual local projective space. A curve-place product therefore
has no isolated points. In the number-field case a finite-place projective
factor suffices for the finite product, and varying that component also proves
the assertion for the full product with all infinite factors fixed. The
comparison homeomorphism transfers this property to the arithmetic adelic
point space. Its Hausdorff property is supplied by the same previously
proved comparison theorem.

Rational density now implies that the range cannot be closed: a closed dense
range would be the whole target, contradicting nonsurjectivity. For
nondiscreteness, a dense subset of this perfect T1 space is preperfect because
its closure is the perfect whole space. Every range point is consequently an
accumulation point of the range. A discrete subset has no such accumulation
point at any of its own elements. The rational point set is nonempty, giving
the contradiction. The no-isolated-points argument is essential here;
density and a proper image alone do not imply nondiscreteness in an arbitrary
compact Hausdorff space.

Both branches retain arbitrary common universe `u`, every finite initial
arithmetic set including the empty set, and every positive projective
dimension. The function-field branch retains finite constants, the specified
rational-function algebra action, its compatible scalar tower, and possibly
inseparable finite extensions. Dimension zero is excluded exactly as in the
target. This proof establishes the three specified image properties; the
other four sections and remaining assertions of the parent program retain
their separate obligations.

Worker 208 authored the reused proof and its argument description. Worker 1557
checked the published dependencies and original source and prepared this focused
proof pair for submission. All dependencies are imported from the published
Library; this contribution supplies only the rational-image proof.
