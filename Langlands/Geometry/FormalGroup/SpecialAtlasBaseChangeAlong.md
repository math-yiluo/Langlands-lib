# Supplied scalar extension of actual special formal atlases

This internal construction extends an actual special formal atlas along a map
`f : R →ₐ[O_K] S`, using the independently supplied O_K-algebra structure on S.
It retains the exact underlying supplied-target atlas and full division-order
action, extends the special tangent data, and preserves actual height d².

## Parameters and provenance

K is a nonarchimedean local field, D is a finite-dimensional central division
K-algebra, and `iota : L →ₐ[K] D` is a supplied embedding of a field L. Write
`d = CentralSimple.reducedDegree K D`. These are the parameters of
`SpecialAtlas`: the actual order is `IntegerRing K D`, the coordinate type is
`Fin d`, and the atlas supplies the full-degree unramified integer-subfield
condition and distinct geometric tangent characters. Existence of that
subfield and specialization to invariant 1/d are not proved here.

R and S are arbitrary commutative O_K-algebras in the same universe v;
no flatness or injectivity is required of f. Principal covers may be infinite.
Coefficient tests have universe v and complete compatible families have
universe v+1. The geometric tangent condition has exactly the algebraically
closed test-field universe `max u v` of `SpecialAtlas`; L has its independent
universe s. Formal maps in this module use equal principal-generator sets.

The module derives its constructions from `SpecialAtlasBaseChange`,
`AtlasAlgebraTransport`, `AtlasBaseChangeAlong` and
`AtlasOrderBaseChangeAlong`. The specialness and height notions are the
existing ones; this module makes no new translation of an original-literature
assertion. Equality elimination and the previously constructed coefficient
extension give all the results below.

## Transport of the actual special data

`reAlgebra X beta e` retypes a special atlas when two O_K-algebra structures
alpha and beta on the same ring R are equal. Its fields are explicitly the
existing `X.atlas.reAlgebra beta e` and `X.order.reAlgebra beta e`.
The unramified-subfield certificate is retained, and equality elimination
transports every geometric tangent-character certificate. The projection
lemmas `reAlgebra_atlas` and `reAlgebra_order` are definitional equalities.
Thus the original formal group and scalar-action series, transitions and
every division-order action series are precisely those of the underlying
transport constructions.

`reAlgebra_refl` returns X. `reAlgebra_trans` identifies successive scalar
retypings with transport along the composed equality, by eliminating both
equalities.

`reAlgebra_height_iff` preserves the entire `HasHeightSquared pi` predicate.
That predicate requires irreducibility of pi in O_K, nilpotence of its actual
image in R, and `HasPiHeight pi q (d^2)` on every original localization chart,
with q the actual residue-field cardinality of K. Each chart-height
certificate concerns the existing scalar kernels, including fppf scalar
lifting, pi-power torsion, finite projective representing algebras and
their stalk ranks. Equality elimination proves the stated equivalence.

`reAlgebraPointEquiv` is exactly the underlying order action's linear
equivalence on entire compatible-family modules. It is linear over
`IntegerRing K D`. `reAlgebraPointEquiv_natural` retains its naturality for
every coefficient-test map.

## Supplied-target coefficient extension

`baseChangeAlong X f` first uses `X.baseChange (coefficientTest f)`.
That existing construction extends all the actual chart laws and order
actions, retains the unramified-subfield data, and extends the tangent
characters along the localization coefficient maps. Its O_K-algebra
structure on S is initially the composite through R.

`coefficientAlgebraAlong_eq f`, proved from `f.commutes`, identifies that
composite with the supplied structure on S. Applying `reAlgebra` gives the
claimed supplied-target special atlas. The lemmas `baseChangeAlong_atlas`
and `baseChangeAlong_order` identify its fields exactly with
`X.atlas.baseChangeAlong f` and `X.order.baseChangeAlong f`.
`baseChangeAlong_opens` identifies its principal-generator set with
`f '' X.atlas.opens`.

`baseChangeAlong_height` first applies the existing actual height
preservation theorem and then `reAlgebra_height_iff`. This retains
irreducibility, maps the nilpotent uniformizer image to S, and extends all
chart scalar-kernel certificates. It does not infer height from specialness.

## Complete families and actual formal maps

`baseChangeAlongPointEquiv X f A` is the exact order-linear equivalence
between X's entire compatible families on the restricted R-test and the
extended special atlas's families on the S-test A. By
`baseChangeAlongPointEquiv_eq`, its underlying function is exactly the basic
atlas's supplied-target family comparison.
`baseChangeAlongPointEquiv_natural` reuses the full-order naturality equation.
`baseChangeAlongPointFunctorIso` is the corresponding natural isomorphism
from restriction followed by X's point functor to the extended point functor,
with values in division-order modules of universe v+1.

`baseChangeAlongHom` extends an actual same-cover order-linear formal map
using exactly the underlying full-order operation. `baseChangeAlongIso`
does the same for both formal maps and their two formal inverse equations.
The new equal-cover witness is the image-cover equality.
`baseChangeAlongHom_onPoints` proves the square on entire families: extending
a family and then applying the extended formal map agrees with applying the
original map on the restricted test and then extending. The
`baseChangeAlongHom_fromPoints` equation proves the reverse square for the
same formal map using the inverse family comparisons. Both are precisely
the existing full-order equations.

Transport of refined comparisons and quotient classes, identity and
successive-map comparisons, a varying-base moduli-class functor, framing,
polarizations, level structures and representability remain separate.
