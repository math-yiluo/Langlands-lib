# Canonical fixed component extension along the identity field map

This module constructs the comparison induced by the actual self-pullback of a
group scheme and proves the identity law for canonical extension of every
Galois-fixed geometric component. It complements the field-tower composition
law in `GeometricComponentCanonicalTower`.

## Objects and assumptions

Let `k : Type u` be an arbitrary field and let `H` be an actual
`GroupScheme (Spec (CommRingCat.of k))`, using the existing `Grp (Over S)`
architecture. Write `H_k = baseChanged k k H`. This is the actual scheme
pullback along

```text
baseMap k k = Spec.map (algebraMap k k) = identity (Spec k).
```

The self-pullback isomorphism and its coefficient formula require no smoothness
or affineness assumption. The component constructions additionally assume
`Smooth H.X.hom` and `IsAffineHom H.X.hom`. The smoothness and affineness of
the pullback are inherited through the published base-change instances.

`GeometricComponents k H` is the group of connected components of the actual
pullback of `H` to the chosen `AlgebraicClosure k`.
`geometricComponentFixedSubgroup k H` consists of the components fixed by
every element of `Field.absoluteGaloisGroup k`. Neither a rational-point
representative nor connectedness of `H` is assumed. There is no restriction
on the characteristic or perfection of `k`.

## The actual self-pullback comparison

In namespace `Langlands.GroupScheme.GaloisPointComparison`,
`selfBaseChangeIso k H` has type

```text
baseChanged k k H ≅ H.
```

It transports the published `GroupScheme.baseChangeIdIso H` along the equality
`baseMap k k = identity`. It retains the existing pullback group law.
`selfBaseChangeIso_hom_left` identifies its underlying scheme morphism with
`pullback.fst H.X.hom (baseMap k k)`.

For any field extension `M/k` in the same universe,
`selfBaseChangeIso_coefficient` states that the map on `M`-coefficient points
induced by this isomorphism is exactly
`coefficientBaseChangeEquiv k k M H`. Both sides project an actual point to
`H` using that first pullback projection.

## Identity on geometric components and fixed components

In namespace `Langlands.GroupScheme.IdentityComponent`,
`geometricComponentBaseChangeEquivOfEmbedding_id` uses the identity
`k`-algebra embedding of `AlgebraicClosure k` into itself. For every
`c : GeometricComponents k H`, it proves

```text
geometricComponentMap k (selfBaseChangeIso k H).hom
  (geometricComponentBaseChangeEquivOfEmbedding k k H
    (AlgHom.id k (AlgebraicClosure k)) c) = c.
```

The multiplicative equivalence `geometricComponentFixedSelfIso k H` has type

```text
geometricComponentFixedSubgroup k (baseChanged k k H)
  ≃* geometricComponentFixedSubgroup k H.
```

It is the published `geometricComponentFixedIso` applied to the actual
`selfBaseChangeIso`. Thus its forward map is the fixed-component map of that
isomorphism, and its inverse is the fixed-component map of the inverse
isomorphism. The theorem `geometricComponentFixedSelfIso_val` gives its
underlying geometric component as the map of the forward scheme morphism.

For every `c : geometricComponentFixedSubgroup k H`,
`geometricComponentCanonicalBaseChange_id` proves

```text
geometricComponentFixedSelfIso k H
  (geometricComponentCanonicalBaseChange k k H c) = c.
```

Here the canonical extension requires no supplied embedding between chosen
algebraic closures. The theorem
`geometricComponentCanonicalBaseChange_id_hom` expresses this as an equality
of the composite homomorphism with `MonoidHom.id`.

The theorem `geometricComponentCanonicalBaseChange_self_eq` identifies
canonical self-extension with
`(geometricComponentFixedSelfIso k H).symm.toMonoidHom`.
Consequently `geometricComponentCanonicalBaseChange_self_bijective` proves
bijectivity for this self-extension.

## Implemented derivation and provenance

This is a derived construction from the published pullback, coefficient-point
and component APIs, with no new external structural assertion.

The private `baseChangeEqIdIso` transports the existing identity comparison
along an equality of base morphisms. Substitution and the published projection
formula give its underlying morphism. Extensionality of over-morphisms gives
the coefficient formula for `selfBaseChangeIso`.

The private section identity `selfSectionHom` applies the injective
`baseChangeCoeffEquiv` to compare closure-valued sections. Naturality moves
the actual self-pullback morphism to the coefficient side. The new coefficient
formula and the published
`geometricComponentBaseChangeSectionHom_coefficient` reduce the equality to
`Lie.affineMap_id`. Surjectivity of `geometricComponentOfPoint` then proves
the identity on every geometric component.

The published `geometricComponentCanonicalBaseChange_val` computes canonical
extension using any compatible closure embedding, so it can be evaluated at
the identity embedding. Subtype extensionality and the preceding component
identity prove the full-fixed identity law. Homomorphism extensionality gives
its homomorphism form. Injectivity of the actual fixed-component equivalence
identifies the canonical map with its inverse, whose bijectivity supplies
the last result.

The bijectivity conclusion concerns extension from `k` to itself. The module
does not establish surjectivity for extension to an arbitrary different field,
rational-point descent of fixed components, or a sheaf-quotient description.
