# Inverse image on original-domain sites and sheaf direct image

Every arrow `F : A ⟶ B` in the constructed source-quotient category of
locally saturated affinoid atlas presentations induces inverse image on the
actual original-chart domain categories. This module proves that this functor
preserves quasinet coverings and is a continuous functor of the constructed
sites. It then constructs direct image of sheaves, with its exact section,
restriction and morphism formulas and natural identity and composition laws.

The field `K : Type u` is normed, complete and ultrametric. The point and
chart-index universes `v` and `w` remain independent of `u`. Source and
target presentations use this same triple. The sheaf coefficient category
`D : Type p` has morphisms in `Type q`, independently of these universes;
no limits or other extra structure on `D` are assumed.

## Source and scope

The source is Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), Definition 1.3.1 and the following paragraph, printed
p.23 / PDF p.20, for finite relative neighborhoods and stability of domains
under inverse image; and the G-topology paragraph, printed p.25 / PDF p.22,
for coverings by quasinet families of domains. The registered source is
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

This is a derived site construction from those conventions. The imported
`SaturatedDomainPreimage` proves that the literal continuous inverse-image
subset is an original-chart domain for every quotient arrow. The imported
`OriginalDomainTopology` constructs the covering topology on these domains:
objects are literal subsets with finite relative neighborhood witnesses
from contained original affinoid charts, and arrows are inclusions.
Saturation here means closure under full local affinoid domains of original
charts. The full analytic-domain category and maximal finite-gluing atlas
have not been identified with this model.

## Continuous preimage of finite refinements

`AtlasTopology.LocallyRefines.preimage` is a general topological lemma for
arbitrary spaces `X` and `Y` in independent universes and a continuous map
`f : X → Y`. If a family `υ` locally refines `τ`, their actual inverse-image
families have the same relation:

```text
LocallyRefines υ τ →
  LocallyRefines ((fun U => f ⁻¹' U) '' υ) ((fun U => f ⁻¹' U) '' τ).
```

At `x ∈ f ⁻¹' U`, take the finite witnesses at `f x` in `U` and form their
inverse images. Finiteness, membership in the new family, containment in
`f ⁻¹' U`, and membership of `x` follow directly. The union of these
inverse images equals the inverse image of the original finite union.
Continuity within `f ⁻¹' U`, with its evident mapping property to `U`,
pulls back the relative-neighborhood condition. No injectivity,
surjectivity or openness is assumed.

## Actual inverse image as a site functor

`domainPreimageInfTopHom F` packages the proved intersection and top laws
for `domainPreimage`. Its order functor `domainPreimageFunctor F` has type

```text
OriginalChartDomain B.presentation.atlas ⥤
  OriginalChartDomain A.presentation.atlas.
```

Its value at `S` is definitionally `domainPreimage F S`, the actual subset
`spaceFunctor.map F ⁻¹' S.carrier` with its proved domain structure.
The morphism assigned to an inclusion is induced subset inclusion.
`domainPreimageFunctorId` and `domainPreimageFunctorComp` turn the proved
identity and composition equalities for domain preimages into natural
isomorphisms. Naturality follows from uniqueness of arrows in these
ordered categories.

The `InfTopHom` instance from Mathlib's
`CategoryTheory.Limits.Preserves.Lattice` supplies
`domainPreimageFunctor_preservesFiniteLimits`: these domain categories are
infimum semilattices with top. Mathlib's
`flat_of_preservesFiniteLimits` then supplies
`domainPreimageFunctor_representablyFlat`.

For a covering sieve `R` on `S`,
`domainPreimageFunctor_isCovering` pulls the finite witnesses in
`sieveFamily R` back by the general continuous preimage lemma. The
preimage of each member `V` is the constructed domain
`domainPreimage F V`. Its inclusion in `domainPreimage F S` is the
functor's image of `V ⟶ S`, hence belongs to the full sieve pushforward.
Monotonicity of local refinement gives the covering property for this
pushforward. `domainPreimageFunctor_coverPreserving` packages the result
for the two actual quasinet topologies.

Finally, `domainPreimageFunctor_isContinuous` uses the proved flatness
through Mathlib's `compatiblePreservingOfFlat` and
`Functor.isContinuous_of_coverPreserving`. Thus precomposition with the
opposite of this inverse-image domain functor carries sheaves to sheaves.

## Sheaf direct image

`domainSheafPushforward D F` is a functor

```text
Sheaf (quasinetTopology A.presentation.atlas) D ⥤
  Sheaf (quasinetTopology B.presentation.atlas) D.
```

It is constructed by Mathlib's `sheafPushforwardContinuous` using the
continuity just proved. For a sheaf `M`, its underlying presheaf is exactly
precomposition of `M.obj` by `(domainPreimageFunctor F).op`. In particular,
`domainSheafPushforward_obj_obj` gives the section formula
`(F_* M)(S) = M(domainPreimage F S)`.
`domainSheafPushforward_obj_map` gives restriction along the induced
preimage inclusion. `domainSheafPushforward_map_app` evaluates a sheaf
morphism at the same preimage domain. All three formulas are definitional
equalities in the implementation.

`domainSheafPushforwardId` identifies direct image along an identity
analytic arrow with the identity functor. For `F : A ⟶ B` and
`G : B ⟶ C`, `domainSheafPushforwardComp` gives
`F_* ⋙ G_* ≅ (F ≫ G)_*`. These use the proved inverse-image functor
isomorphisms and Mathlib's identity and composition isomorphisms for
continuous sheaf pushforward. No inverse-image functor on sheaves or
adjunction is asserted.

Full analytic-domain identification, descent and gluing of analytic
arrows, the structural sheaf, etale and quasi-etale morphisms and sites,
equivariant sites, compact and distinguished domains, and the Harris
tower specialization remain obligations of the surrounding task.
