# Base change of actual rational homomorphisms

This module extends the actual pullback functor on bundled abelian schemes
to their rationalized category. It gives a rational-linear map on `Hom0`,
a unital rational algebra map on `End0`, and pullback of invertible
rational homomorphisms.

## Provenance

The construction is derived from `CommGroupScheme.baseChange`,
`AbelianScheme.baseChange`, and `Rationalization.lift`. The first two
use actual scheme pullbacks with their induced group laws. The last
extends an additive functor to rationalized morphisms by scalar extension.
The additional prerequisite proved here is additivity of pullback on
the actual homomorphism groups.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), printed p.18 / PDF p.26, uses rationalized actual
homomorphisms and calls their invertible elements isogenies.
Section III.1, printed p.91 / PDF p.99, uses the algebra of rational
endomorphisms in its pointed PEL problem. These are the conventions
and application motivating this derived functor. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The Library uses `ℚ ⊗[ℤ] Hom(A,B)`; its existing `hom0TensorComm`
identifies this with the opposite tensor order in the source.

## Additivity

`Langlands.CommGroupScheme.baseChange_additive` proves that the existing
pullback functor preserves addition of homomorphisms. Homomorphisms in
this category are actual group-object homomorphisms written with
`Additive`. After removing that type synonym and applying extensionality
for group-object homomorphisms, the assertion is preservation of the
pointwise product by `Over.pullback b`. Mathlib's `Functor.map_mul`
for a product-preserving functor proves it.

`Langlands.AbelianScheme.baseChange_additive` transfers the same equation
to the bundled abelian-scheme functor. This uses the actual pullback
definition and does not equip it with an assumed additive structure.

## Rational extension

The remaining declarations are in `Langlands.AbelianScheme`.
`rationalBaseChange b` applies `Rationalization.lift` to ordinary
base change followed by the canonical inclusion into the rationalized
category over the new base. On objects it is the actual abelian-scheme
pullback. `rationalBaseChangeHom` exposes its map on Hom groups as a
rational-linear map.

`rationalBaseChangeHom_tmul` states the defining formula

```text
q ⊗ f ↦ q ⊗ b*f.
```

The `ofHom` formula recovers the ordinary pullback on integral
homomorphisms. The `identity` and `comp` lemmas state preservation of
identity and categorical composition; they are specializations of the
published lift functor laws. `rationalBaseChange_map` identifies the
functor map with this linear map. `rationalBaseChangeInclusionIso`
bundles recovery of ordinary pullback as the standard natural isomorphism
for the rationalization lift.

`rationalBaseChangeEnd` is the algebra map supplied by
`Rationalization.liftEnd`. Its multiplication is categorical endomorphism
multiplication, with the same order convention on both sides.
The application and `ofEnd` lemmas identify its underlying rational
Hom map and its behavior on integral endomorphisms.

`rationalBaseChangeIso` uses the functor's `mapIso`. Its forward and
inverse components are the actual rational pullbacks of the original
forward and inverse homomorphisms, as exposed by its two component
lemmas. Functoriality preserves the inverse equations; thus these are
invertible actual rational homomorphisms over the new base.

## Scope

The base morphism is arbitrary and the schemes lie in one universe.
The construction requires no invertibility of an integer on the base,
choice of a geometric point, or finite-etaleness hypothesis.
It concerns the rational-isogeny convention. It does not identify that
notion with the narrower integral prime-to-prime isogeny relation.

This module does not prove coherence for identities or composition of
base morphisms; its identity and composition laws concern morphisms of
abelian schemes over a fixed base. Compatibility with Tate modules,
endomorphism tensor-algebra actions, polarizations, Weil pairings,
fundamental groups and level structures is subsequent work.
