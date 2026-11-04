# Existence of actual arithmetic spreads for finite-type field schemes

`Langlands.Global.AdelicSpreadExistenceStatement` is the conjunction of
the function-field and number-field forms of arithmetic spread existence.

In the function-field clause, `k` is an arbitrary perfect field and `F`
is a function field over `k`, with the specified compatible
rational-function action and scalar tower. For every finite initial set
`S` of actual curve places and every scheme `Y` of finite type over the
original field `F`, there are a finite set `T` containing `S` and a scheme
`M` of finite type over the actual outside-`T` integer ring such that the
actual generic fiber of `M` is isomorphic to `Y` over `F`.

The number-field clause asserts the same result for an arbitrary number
field `K` and its actual outside-`T` integer ring. Its finite sets index
finite places; adjoining all archimedean places matches Conrad's full
place-set convention. The assertion concerns arithmetic models and
introduces no change to the infinite factors in full adelic points.

Finite type is expressed in both clauses by locally finite type and
quasi-compact structure maps, for both the supplied scheme and the model
whose existence is asserted. `AdelicLevelIndexAbove S` consists of finite
sets containing `S`. The generic fibers are the existing
`curvePlaceModelGenericFiber` and `numberFieldModelGenericFiber`, defined
as categorical pullbacks along the literal inclusions of the actual
integer subrings into the original fields. `Nonempty` asserts existence
of an isomorphism in the over-category of schemes over that original
field.

Neither the field scheme nor its asserted model is required to be affine
or separated. No additional quasi-separatedness, finite-presentation or
chosen-spread premise is imposed. A finite-type scheme over a field is
Noetherian, so it has the quasi-separatedness and finite-presentation
properties needed by general filtered-ring model existence. This unit
does not assert that a separated field scheme has a separated model;
that conclusion additionally uses eventual separatedness. It also makes
no assertion about topological properties of adelic point spaces.

## Source and derived scope

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed p.5, Theorem 3.4(1), existence
clause, and printed p.6, Remark 3.5 and its application to a finite-type
field scheme. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad explicitly includes nonaffine schemes and explains on p.5 that
finite presentation and finite type agree over Noetherian rings.

Apply filtered-ring model existence to the actual integer-ring diagram
over finite sets containing the prescribed `S`, whose cocone has vertex
the original field. The resulting pullback square identifies the model's
actual generic fiber with the supplied field scheme. Forgetting the
initial integer-base algebra structure preserves the filtered colimit.
This is the arithmetic specialization of the source's existence clause;
it does not replace an actual model or its generic fiber by an assumed
auxiliary presentation.

The arbitrary-perfect-constant scope, allowance of an empty initial
`S`, and enlargement of any prescribed initial finite set are derived
scope. The actual integer rings exhaust the original field along these
finite superlevels, including when `S` is empty. The argument needs no
finite-constant, local-compactness or separability assumption on the
specified finite extension of the rational-function field. Restricting
to finite constants and Conrad's nonempty place sets recovers his
function-field case.

This pair states existence. Its proof, the actual integer-colimit proof
and generic filtered-ring model-existence proof retain their own
independent review and publication obligations.
