# Actual quotient actions form a fibered category over topological groups

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (1996
unfinished manuscript), section 1.1, printed/PDF page 3, observes that the
category of analytic spaces with operators is fibered over the category of
topological groups. This module constructs the corresponding fibration for
the published concrete category `VariableActionSpace K`.

`groupForget` bundles the topological group already retained by each object.
It sends a genuine geometric arrow to its existing continuous group
homomorphism. Group maps therefore have the same source-to-target direction
as the geometric arrows.

For an object `X`, a bundled topological group `H`, and any continuous
homomorphism `f : H → groupForget.obj X`, the Cartesian lift is the existing
arrow `restrictionMap X f : restrict X f → X`. Its domain has the same
actual quotient algebra and norm as `X`; only the action is restricted along
`f`. The arrow's bounded algebra pullback is the identity.

`restrictionMap_isStronglyCartesian` proves the full universal property.
Given a geometric arrow `h : Z → X` lying over the composite of a group map
`k : groupForget.obj Z → H` with `f`, the published
`restrictionLift_existsUnique` constructs the unique arrow
`l : Z → restrict X f` whose group component is `k` and whose composite with
`restrictionMap X f` is `h`. The proof converts Mathlib's `IsHomLift`
condition to equality of the actual continuous group homomorphisms and
back again. Thus the factorization holds for the complete arrows, including
their bounded algebra maps.

`groupForget_isFibered` applies Mathlib's constructor from the existence
of strongly Cartesian lifts. This also supplies Cartesian lifts and
closure of Cartesian arrows under composition in Mathlib's definition.
Neither the fibration nor its universal property is assumed as a field.

The fibration is an internal consequence of the previously constructed
restriction and unique-lift API. The original source supplies the
operator-group convention and the motivating fibration assertion; this
module realizes it for actual finite positive-polyradius Tate-algebra
quotients by closed ideals with norm-continuous algebra actions.

The coefficient field is any ultrametric normed field in universe `u`.
Operator groups have independent universe `v`. There is no injectivity,
openness, or surjectivity requirement on `f`. This local quotient
construction does not assert that these objects constitute the full
analytic category of the source, or construct analytic atlases, the
analytic automorphism topology, or étale sites.
