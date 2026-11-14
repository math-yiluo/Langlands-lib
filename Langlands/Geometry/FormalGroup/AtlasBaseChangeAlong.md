# Coefficient extension to a supplied scalar algebra structure

This internal construction extends an actual formal O-module atlas along an
O-algebra homomorphism `f : R →ₐ[O] S`, with the independently supplied O-algebra
structure on S as the result's scalar structure. It also extends actual formal
maps and isomorphisms and compares the entire compatible-family point functors.

## Scope and provenance

O, R and S are arbitrary commutative rings with supplied O-algebra structures
on R and S. R and S have the same universe v; coefficient tests have universe v
and compatible families have universe v+1. Coordinates are finite and covers
may be infinite. The map f need not be injective or flat. Formal atlas maps in
this unit have equal source and target principal-generator sets, with possibly
different finite coordinate types.

The construction combines `AtlasAlgebraTransport` with
`AtlasBaseChangeMorphism` and its full compatible-family comparison. These are
internal consequences of the existing definitions. This unit asserts no
additional theorem from the literature; the localization-gluing convention
underlying the atlas is documented in `BasicAtlas.md`.

The supplied-target operation preserves identities and composition of formal
maps for a fixed coefficient map f. Identity and composition comparisons
between different coefficient extensions, arbitrary-cover comparisons,
acting-order transport, specialness, height, framing, a varying-base quotient
moduli functor and representability remain separate.

## Transport along equality of scalar structures

All atlas declarations are in
`Langlands.FormalGroup.ModuleLaw.BasicAtlas`.

Given two O-algebra structures α and β on R and an equality `e : α = β`,
`reAlgebraPointEquiv` identifies the full compatible-family O-modules of X
and `X.reAlgebra β e` on every R-test. It is defined by eliminating e and
using the identity linear equivalence. `reAlgebraPointEquiv_apply` identifies
every corresponding family tuple, and `reAlgebraPointEquiv_natural` proves
commutation with every coefficient-test map by the same equality elimination.

`Hom.reAlgebra` transports an actual formal atlas map. Its coordinate series
are retained, as recorded by `Hom.reAlgebra_coordinates`.
`Hom.reAlgebra_id` and `Hom.reAlgebra_comp` preserve the actual identity and
composition maps. `Hom.reAlgebra_onPoints` gives the square with the full
compatible-family equivalences. All these proofs eliminate e and reduce to
reflexivity. `Iso.reAlgebra` transports both formal maps and both formal
inverse equations; `Iso.reAlgebra_hom` and `Iso.reAlgebra_inv` identify its maps
with the corresponding transported maps.

## Extension along the supplied map

`coefficientTest f` equips S with the R-algebra structure defined by the
underlying ring homomorphism of f. The structural composite O-algebra on that
test is equal to S's supplied O-algebra structure:
`coefficientAlgebraAlong_eq` proves this by algebra extensionality and
`f.commutes`.

`baseChangeAlong X f` first constructs the actual atlas `X.baseChange
(coefficientTest f)`, then transports its scalar structure along this
equality. Its principal-generator set is `f '' X.opens`, as stated by
`baseChangeAlong_opens`. The charts and actual transition isomorphisms come
from coefficient extension; scalar-structure transport retains their formal
coordinate data.

`Hom.baseChangeAlong` similarly extends a formal map and then transports it.
Its cover equality is the image-cover equality from `baseOpens_eq`.
`Hom.baseChangeAlong_id` and `Hom.baseChangeAlong_comp` follow from the
corresponding coefficient-extension and equality-transport laws.
`Iso.baseChangeAlong` extends both maps and both inverse equations of an
actual same-cover formal isomorphism.

## Entire compatible-family comparison

For every S-test A, `baseChangeAlongPointEquiv X f A` is the linear equivalence

```text
X.Point (restrictCoefficientAlgebra f A)
  ≃ₗ[O] (X.baseChangeAlong f).Point A.
```

It is the composite of the existing full coefficient-extension equivalence
with `reAlgebraPointEquiv`. Consequently its inverse is also constructed on
entire compatible families, using the earlier lifted-test inverse followed
by equality transport. `baseChangeAlongPointEquiv_natural` chains the two
naturality equalities. `baseChangeAlongPointFunctorIso` packages these
components as a natural isomorphism from
`restrictCoefficientFunctor f ⋙ X.pointFunctor` to the extended point functor.

For an actual formal atlas map g, `Hom.baseChangeAlong_onPoints` gives

```text
(g.baseChangeAlong f).onPoints (X.baseChangeAlongPointEquiv f x)
  = Y.baseChangeAlongPointEquiv f (g.onPoints x).
```

The original map on the right is evaluated on the restricted test.
The proof chains the actual coefficient-extension square and the
equality-transport square. `Hom.baseChangeAlong_fromPoints` proves the
corresponding inverse square by injectivity of the target equivalence and
its two inverse identities. These equalities apply to every compatible
family component, including further coefficient-extension tests.
