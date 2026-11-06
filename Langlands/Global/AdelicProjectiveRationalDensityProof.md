# Rational-point density in actual adelic projective space

`adelicProjectiveRationalDensity` proves
`Langlands.Global.AdelicProjectiveRationalDensityStatement`. Its two component
theorems prove the function-field and number-field clauses for the actual
principal scalar-extension map into polynomial-Proj projective scheme points,
with the arithmetic adelic topologies specified by the target.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.10, Example 4.3, registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad uses approximation in matrices and projective changes of coordinates,
then affine weak approximation. The implemented proof instead uses the
previously proved density of a fixed affine chart in each local projective
point space, followed by coefficient weak approximation.

The first private lemma proves that a map to a product has dense range when
every finite coordinate restriction does. A neighborhood in the full product
contains a cylinder depending on finitely many coordinates; density of that
restriction supplies a point in the cylinder. Applying this to the actual
finite-completion weak-approximation theorem gives density of the original
function field in the product of all its curve-place completions. For number
fields the corresponding argument keeps the product of all infinite-place
completions and restricts only the finite-place coordinates. It uses the mixed
finite-completion weak-approximation theorem, so the infinite factors are
approximated simultaneously with any finite collection of finite factors.

Each completion has no isolated points. For curve and finite number-field
places the proof uses the nontrivially normed field associated with its valued
field structure; the curve case first supplies the rank-one instance from the
discrete valuation. At an infinite place, the existing norm-preserving embedding
of the completion into the complex numbers shows that the norm of 2 is 2,
which supplies a nontrivially normed field structure. Mathlib then gives
`PerfectSpace` for the unchanged completion topology.

The second private product lemma applies dense scalar approximation separately
to every affine coordinate. A continuous surjective transposition of the two
coordinate indices carries this to a dense family of local affine-coordinate
tuples. The product of the actual standard chart maps is continuous and has
dense range by `denseRange_projectiveAffinePoint`; composing gives density of
the rational standard-chart tuples in the full product of actual local
projective point spaces. In the number-field clause the proof performs the same
transposition explicitly for the pair of infinite and finite local products,
then uses the product of their chart maps.

In both arithmetic clauses, coefficient naturality of `projectiveAffinePoint`
identifies this dense chart map with the principal rational-point map followed
by the original all-place coefficient projection. The inverse of the proved
projective comparison homeomorphism transfers density to the arithmetic
adelic topology. Finally, the rational standard-chart points form a subset of
all rational projective points, so the complete principal rational-point map
also has dense range.

The proof retains arbitrary common universe `u`, every finite initial set
(including the empty set), both global-field characteristics, all infinite
number-field factors, and finite function-field presentations without a
separability assumption. Every natural projective dimension is allowed:
dimension zero is the singleton extension described by the target.
Positive-dimensional proper-subset, nonclosedness and nondiscreteness
conclusions of Example 4.3 are separate obligations.

Worker 208 authored the reused proof and its argument description. Worker 1557
checked the published dependencies and original source and prepared this focused
proof pair for submission. All dependencies are imported from the published
Library; this contribution supplies only the rational-density proof.
