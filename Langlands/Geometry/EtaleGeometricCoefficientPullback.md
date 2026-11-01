# Geometric cohomological pullback with target coefficients

This internal construction combines the existing geometric pullback with an
actual target coefficient morphism. It works along every scheme morphism
`f : Z ⟶ X`. The final two comparisons specialize to an étale morphism and
identify the resulting maps with the existing restriction construction.

The namespace is `Langlands.Geometry.EtaleDerivedGlobalPullback`. Schemes,
the commutative ring `R`, and the underlying modules have universe index `u`.
`ModuleSheaf X R` is the actual category of `R`-module sheaves on the small
étale site of `X`, and `sections X R` is its global-section functor. The
coefficient sheaves are arbitrary; there is no field, finiteness, Noetherian,
or local-constancy hypothesis.

For the derived constructions the localization morphism universes `wX`,
`wZ`, and `wR` are independent, through the corresponding
`HasDerivedCategory` instances for the two sheaf categories and `ModuleCat R`.
Composition uses an additional independent `wV`. The ordinary section-map
definition is placed before those assumptions and needs no derived category.
All ordinary cohomology degrees in this module are nonnegative integers.

The coefficient datum is an actual sheaf morphism
`α : (inverseImage f R).obj F ⟶ G`. Here `inverseImage` is the constructed
geometric inverse image, rather than an assumed restriction along an étale map.
Its construction and the construction of the underlying derived pullback are
imported from the existing geometric inverse-image and derived-adjunction
framework.

## The three maps

`sectionsPullbackWithCoefficients f R α` is the composite

```text
Γ(X,F) → Γ(Z,f⁻¹F) → Γ(Z,G),
```

using the actual `sectionsPullback` transformation and `sections Z R` applied
to `α`.

`sheafDerivedPullbackWithCoefficients f R α` is the corresponding morphism
in the bounded-below derived category of coefficient modules:

```text
RΓ(X,F) → RΓ(Z,f⁻¹F) → RΓ(Z,G).
```

The first arrow is `sheafDerivedPullback`, constructed from the actual derived
inverse/direct-image adjunction. The second is `derivedSections Z R` applied
to `α`. These derived-section objects take a coefficient sheaf as input,
embedded in degree zero.

`cohomologyPullbackWithCoefficients f R q α` is the analogous composite on the
existing ordinary right-derived cohomology functors in degree `q`, using
`cohomologyPullback` followed by `cohomology Z R q` applied to `α`.

## Recovery and functoriality

`sheafDerivedPullback_homology` first proves that applying degree-`q` homology
to the geometric sheaf-derived pullback recovers `cohomologyPullback` through
the canonical `homologyNatIso` identifications. This follows by expanding
the existing definition of `cohomologyPullback` and cancelling the inverse
and forward source identification.

`sheafDerivedPullbackWithCoefficients_homology` proves the same square for
the coefficient map `α`. Its proof uses functoriality of homology,
naturality of the target `homologyNatIso` at `α`, and the preceding identity.

`sheafDerivedPullbackWithCoefficients_zero` identifies degree-zero homology
of the constructed derived map with `sectionsPullbackWithCoefficients`
through the existing `homologyZeroIso` isomorphisms. It uses naturality at
`α` and the already proved degree-zero normalization of geometric pullback.
Thus this recovery uses the actual global-section map, not just a chosen
isomorphic module.

`sheafDerivedPullbackWithCoefficients_precomp` expresses naturality in
`a : F' ⟶ F`: replacing `α` by `(inverseImage f R).map a ≫ α` is the same
as first applying derived sections on `X` to `a`.
`sheafDerivedPullbackWithCoefficients_postcomp` expresses naturality in
`a : G ⟶ G'`: replacing `α` by `α ≫ a` is the same as postcomposing by
derived sections on `Z` applied to `a`. The proofs use the underlying
geometric natural transformation and functoriality.

For the identity scheme map, the coefficient map is the component of
`inverseImageId R X`. `sheafDerivedPullbackWithCoefficients_id` proves that
the resulting derived map is the identity by the existing geometric identity
law.

For `g : V ⟶ Z` and `β : (inverseImage g R).obj G ⟶ H`,
`sheafDerivedPullbackWithCoefficients_comp` proves that successive derived
coefficient maps equal the map along `g ≫ f` with coefficient morphism

```text
(inverseImageComp R f g).inv.app F ≫ (inverseImage g R).map α ≫ β.
```

The inverse composition isomorphism has the required direction from
`(g ≫ f)⁻¹F` to `g⁻¹(f⁻¹F)`. The proof substitutes the existing geometric
composition law, cancels the constructed coefficient-comparison isomorphism,
and uses naturality of pullback along `g` at `α`. The desired composition
equation is proved, not included in the coefficient datum.

## Étale restriction comparison and scope

For étale `f` and
`α : (EtalePullback.restriction f (ModuleCat R)).obj F ⟶ G`,
`sheafDerivedPullbackWithCoefficients_restriction` proves exact equality with
`EtalePullback.derivedSectionsMapWithCoefficients f R α` when the geometric
coefficient map is
`(inverseImageIsoRestriction f R).hom.app F ≫ α`.
`cohomologyPullbackWithCoefficients_restriction` proves the analogous equality
with `EtalePullback.cohomologyMapWithCoefficients` in every degree `q`.
Each proof combines functoriality with the existing geometric/restriction
comparison; neither comparison is assumed.

The provenance is internal composition of the published geometric inverse
image, derived sections, geometric identity/composition laws, degree-zero
normalization, and the separately submitted restriction-comparison group.
This pair makes no new external literature assertion. It supplies maps with
arbitrary inverse-image coefficients; compatible coefficient diagrams,
scalar-change coherence, compact support, smooth equivariance, and the
specialization required by Harris remain separate constructions.
