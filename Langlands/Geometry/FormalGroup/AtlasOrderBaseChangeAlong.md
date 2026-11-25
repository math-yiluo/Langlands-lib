# Supplied scalar extension with the full acting order

This internal construction extends a formal atlas with its actual order action
along an O-algebra map `f : R →ₐ[O] S`, retaining the independently supplied
O-algebra structure on S. It extends actual order-linear formal maps and
isomorphisms and constructs a natural equivalence on complete compatible-family
modules over the entire acting order.

## Scope and provenance

O, R and S are arbitrary commutative rings. R and S have supplied O-algebra
structures and the same universe v. D is a possibly noncommutative ring with
an O-algebra structure, in an independent universe w. Coordinates are finite;
principal-generator covers may be infinite. Test algebras have universe v
and complete compatible families have universe v+1. No injectivity or flatness
of f is required. The formal maps in this module have equal source and target
principal-generator sets, with possibly different finite coordinate types.

This is an internal consequence of the existing actual atlas, formal order
action and coefficient-extension constructions. It combines
`AtlasBaseChangeAlong` with `AtlasOrderBaseChangeMorphism`. Equality elimination
transports the formal order action; the earlier order-linear coefficient
extension then gives extension to supplied scalars. This module claims no
additional theorem from the literature. The localization-gluing convention is
documented in `BasicAtlas.md`, and the formal order action in
`AtlasOrderAction.md`.

Identities and compositions of formal maps are preserved for a fixed f.
Comparisons between successive supplied coefficient maps, an identity-extension
formal comparison, arbitrary-cover comparisons, specialness, height, framing,
varying-base moduli classes and representability remain separate.

## Equality transport of the order action

The declarations are in
`Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction`.

For two O-algebra structures α and β on R and `e : α = β`, `reAlgebra E β e`
is an actual order action on `X.reAlgebra β e`. Eliminating e reduces the
construction to the original E. Thus the order ring, its scalar structure,
all formal endomorphisms and their transition commutations are transported
together. `reAlgebra_chart_coordinates` retains every chart's formal
order-action series; `reAlgebra_testChart_coordinates` also retains the
series after evaluation of coefficients on every invertible-chart test.
`reAlgebra_refl` is reflexivity.

`reAlgebraPointEquiv` is a D-linear equivalence between the complete families
for E and its transported action. It eliminates e and uses the identity
linear equivalence. `reAlgebraPointEquiv_eq` identifies its underlying function
with the existing basic-atlas transport. `reAlgebraPointEquiv_apply` retains
the tuple on every further test algebra, every map to that algebra and every
invertible chart. `reAlgebraPointEquiv_natural` proves naturality for every
coefficient map by equality elimination.

`Hom.reAlgebra` transports an actual formal atlas map together with its
commutation equations for every element of D. `Hom.reAlgebra_val` identifies
its underlying basic formal map with precisely the existing basic transport.
`Hom.reAlgebra_id`, `Hom.reAlgebra_comp` and `Hom.reAlgebra_onPoints` preserve
formal identities, composition and the entire-family square. Each proof
eliminates e and reduces to reflexivity.

`Iso.reAlgebra` transports both actual order-linear formal maps and both
formal inverse equations. Its `reAlgebra_hom` and `reAlgebra_inv` equations
identify those maps with the transported original maps.

## Extension to the supplied scalar structure

`baseChangeAlong E f` first uses `E.baseChange (coefficientTest f)`, then
transports its scalar algebra structure with the existing equality
`coefficientAlgebraAlong_eq f`. Its underlying atlas is exactly
`X.baseChangeAlong f`, whose principal-generator set is `f '' X.opens`.
It therefore retains the given target O-algebra structure rather than
requiring that structure to be definitionally the composite through R.

For each S-test A, generator b of the image cover, invertibility witness for
b in A, and d in D, `baseChangeAlongOrderChart_coordinates` identifies the
extended formal action of d with the action on the selected original source
chart, mapped to the restricted R-test. The proof first removes equality
transport by `reAlgebra_testChart_coordinates`, then applies the original
order-action coefficient comparison. The equality concerns the complete
coordinate series for every d.

`Hom.baseChangeAlong` extends an actual formal atlas map and its full-order
commutation, then transports scalars. `Hom.baseChangeAlong_val` proves that
forgetting the order gives exactly `g.val.baseChangeAlong f`.
`Hom.baseChangeAlong_id` and `Hom.baseChangeAlong_comp` follow from the
coefficient-extension and equality-transport laws for the corresponding
formal maps. `Iso.baseChangeAlong` extends both maps and both formal inverse
equations; `baseChangeAlong_hom` and `baseChangeAlong_inv` identify its maps
with the individual extensions.

## Complete-family comparison and both squares

For every S-test A, `baseChangeAlongPointEquiv E f A` has type

```text
E.Point (restrictCoefficientAlgebra f A)
  ≃ₗ[D] (E.baseChangeAlong f).Point A.
```

It composes the existing order-linear coefficient-extension equivalence with
the order-linear scalar-transport equivalence. Its inverse therefore also
acts on complete compatible families. `baseChangeAlongPointEquiv_eq`
identifies its underlying function with the existing basic-atlas comparison.
`baseChangeAlongPointEquiv_natural` chains the two naturality equations.
`baseChangeAlongPointFunctorIso` packages the components as a natural
isomorphism from `restrictCoefficientFunctor f ⋙ E.pointFunctor` to the
extended full order-module point functor.

For an actual order-linear formal atlas map g from E to E',
`Hom.baseChangeAlong_onPoints` proves

```text
(g.baseChangeAlong f).onPoints (E.baseChangeAlongPointEquiv f x)
  = E'.baseChangeAlongPointEquiv f (g.onPoints x).
```

The original g is evaluated on the restricted test. The proof chains the
coefficient-extension square with the equality-transport square.
`Hom.baseChangeAlong_fromPoints` gives the reverse square with the inverse
family equivalences; applying the target equivalence and its inverse laws
reduces it to the forward square. The Iso namespace provides both squares
for the actual formal isomorphism, using its exact forward map. All these
equations are equalities of complete compatible families on every further
test, and the linear maps retain the action of every element of D.
