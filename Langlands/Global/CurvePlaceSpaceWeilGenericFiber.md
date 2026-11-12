# Original generic-fibre comparison of a curve-place space Weil model

This internal unit identifies an original principal integral Weil model's generic
fibre, proves compatibility with the canonical full curve adelic tensor map, and
constructs the field-valued homeomorphism for these specified models. Algebraicity
and separated finite-type geometry of the integral Weil model remain explicit
inputs. This unit does not compare arbitrary independent models.

Let `k` be finite, let `K` be a function field over `k`, and let `L/K` be finite,
with its supplied function-field structure. Fix a principal integral presentation
given by `s`, finite dimensionality of `K` over `k(s)`, and a nonzero chart
element `t`. The lower support is the original principal exceptional set `S`,
and the upper support is its full preimage. Let `X` be an algebraic space over
the original upper integral base whose actual Weil restriction to the lower
base is algebraic. No separability hypothesis on `L/K` is used.

`genericWeilAlgebraic` applies the published cartesian Weil base-change result to
the original principal S-integer fraction-field tensor equivalence. The right
pure-tensor law is the original upper integral-coefficient inclusion into `L`.
`genericFiberIso` is that actual cartesian isomorphism between the generic fibre
of the original integral Weil space and the field Weil space of `X`'s generic
fibre. The construction retains both original coefficient maps.

`adeleInclusion_compatible` proves the original full curve adele inclusion law
on diagonal field coefficients. `adelicEvaluation_model` identifies the canonical
field Weil point equivalence after the lower generic-fibre spread equivalence
with the original integral counit followed by the upper generic-fibre equivalence.
The proof explicitly keeps the original integral and field coefficient actions
and their scalar towers, using the published adele diagonal equality. It applies
injectivity of the upper base-change point equivalence, replaces the canonical
tensor map by its original counit evaluation formula, and applies the general
cartesian counit evaluation comparison. Inverse identities of the generic-fibre
point equivalences complete the square.

For a specified isomorphism `e` from the upper model's generic fibre to a space
`Y` over `L`, and an algebraicity proof for its Weil sheaf, `genericFiberIsoOfIso`
composes `genericFiberIso` with the actual Weil restriction of `e`.
`adelicEvaluation_modelOfIso` proves the resulting original counit square from
naturality of the canonical tensor point equivalence in the upper space.

Assume further that `X` and its original integral Weil space are separated and
of finite type, and that `S` is nonempty. `adelicPointHomeomorphOfIso` composes
the inverse lower spread homeomorphism, the full original integral-model Weil
homeomorphism, and the upper spread homeomorphism. It uses exactly the spread
topology attached to the integral Weil model and `genericFiberIsoOfIso` on the
source and to `X` and `e` on the target. `adelicPointHomeomorphOfIso_apply` proves
its forward map is precisely `curvePlaceSpaceWeilRestrictionPointsEquiv`, the
canonical tensor map of the adelic statement. Its proof represents any source
point by the lower spread equivalence, cancels that equivalence and its inverse,
and uses `adelicEvaluation_modelOfIso`.

The provenance is internal composition of the original integral-closure fraction
tensor equivalence, cartesian Weil base change and counit compatibility, canonical
full curve adelic tensor comparison, and the actual integral-model and spread
homeomorphisms. Finite inseparable extensions and the original completion
topologies are retained by the constructions being composed.
