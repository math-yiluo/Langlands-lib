# Canonical deck actions for arbitrary scheme morphisms

This internal construction specializes `EtaleCanonicalDeckTower` to original
scheme morphisms and their supplied deck automorphisms. It constructs actual
cohomological actions and pullback maps, natural in every sheaf on the base.
It does not request cohomology objects, coefficient cocycles, action
compatibilities, or recovery comparisons as input.

## Inputs and scope

Let `p : Y ⟶ X` be any morphism of schemes, let `G` be any abstract group,
and let `τ : G →* (Aut Y)ᵐᵒᵖ`. The existing `EtaleCohomologyAction.aut`
convention reads this as automorphisms with
`aut τ (g * h) = aut τ g ≪≫ aut τ h`. The hypothesis
`hp g : (aut τ g).hom ≫ p = p` is the actual geometric deck triangle.
There is no etaleness assumption on `p`.

Schemes and the commutative coefficient ring `R` share universe `u`, and
module coefficients have universe `u`. The abstract group has its own
universe `t`. The three cohomological consumers use a chosen
`HasDerivedCategory.{wY} (ModuleSheaf Y R)` and a chosen
`HasDerivedCategory.{wR} (ModuleCat.{u} R)`. All three consumers and their
comparisons, including sections, retain these assumptions: the published
section action and level maps are constructed through derived homology.
The ordinary section object itself is the usual global-section module.
For maps from a second scheme `Z`, its module-sheaf derived category uses
the same size `wY`; the module-derived category size `wR` is independent.

The sheaves are the project's actual module sheaves on the small etale
site. The resulting actions are algebraic actions of an abstract group.
No topological group structure, continuity, smoothness, compact support,
finiteness, properness, freeness, covering, or torsor property is asserted.

## Original geometry

`overAction τ p hp` is an action on `(Over X)ᵒᵖ` with underlying object
`op (Over.mk p)` and group maps the opposites of the supplied geometric
automorphisms over `X`. The fields proving the action laws use the original
automorphism homomorphism. The formulas `overAction_V_left`,
`overAction_V_hom`, and `overAction_ρ_left` retain `Y`, `p`, and each original
automorphism literally.

For a second datum `q : Z ⟶ X`, `σ`, and `hq`, a morphism `f : Z ⟶ Y`
with `hf : f ≫ p = q` and

```
he g : f ≫ (aut τ g).hom = (aut σ g).hom ≫ f
```

gives `overHom f hf he : overAction τ p hp ⟶ overAction σ q hq`.
Its underlying map is the opposite of the original map over the base;
`overHom_left` recovers `f`. The equivariance field is precisely `he`.
`overHom_id` and `overHom_comp` prove identity and contravariant composition
for these geometric action morphisms. If `k : W ⟶ Z`, the original
composite is `k ≫ f`, and its action morphism is `overHom f ≫ overHom k`.

`tower` regards one such action as a constant tower indexed by
`SingleObj PUnit.{1}`. `arrowTower` packages one original equivariant map as
a two-level tower indexed by `Fin 2`. Its zero and one vertices are the
original source and target actions, as the two `arrowTower_obj_*` formulas
state.

## Canonical coefficients and consumers

`coefficientIso τ p hp R g` is the actual isomorphism

```
inverseImage p R ⋙ inverseImage (aut τ g).hom R ≅ inverseImage p R.
```

It is `projectionInverseImageIso` applied to the original triangle `hp g`:
the comparison comes from composition of inverse images and transport
along that equality of actual scheme maps.

`sectionsFunctor`, `derivedFunctor`, and `cohomologyFunctor n` evaluate the
parent tower consumers at the sole level. They are functors from every
`ModuleSheaf X R` to `G`-actions, respectively on `ModuleCat R`, the
bounded-below derived category of `ModuleCat R`, and `ModuleCat R`.
Their `*_obj_V` formulas identify the underlying objects with actual
sections, bounded-below derived sections, and ordinary cohomology of
`(inverseImage p R).obj M` on the original scheme `Y`.

The `*_obj_ρ` formulas identify every group action with actual geometric
pullback along `(aut τ g).hom`, followed by the corresponding consumer of
`(coefficientIso τ p hp R g).hom.app M`. The `*_map_hom` formulas say that
every base coefficient morphism acts by the original inverse-image
morphism followed by sections, derived sections, or ordinary cohomology.
The action laws and coefficient naturality come from the actual canonical
tower construction; no desired cohomological action is supplied as data.

## Original-map pullback

For every `f`, `hf`, and `he` as above, `derivedMap`, `cohomologyMap n`, and
`sectionsMap` are natural transformations between the corresponding
single-scheme consumers. Their `*_app_hom` formulas identify their maps
with `sheafDerivedPullbackWithCoefficients`,
`cohomologyPullbackWithCoefficients`, and `sectionsPullbackWithCoefficients`
along the original `f`. In all three formulas the target coefficient map is

```
(projectionInverseImageIso R p q f hf).hom.app M.
```

Thus these are the actual geometric pullbacks with canonically transported
target coefficients. They require no etaleness assumption on `f`.

Their equivariance proofs take the parent two-level tower's equivariant
level map, rewrite its action and map formulas to the original scheme
morphisms, and use that equality as the commutation field of an explicit
`Action.Hom`. This avoids changing the original maps through a bundled
endpoint identification. The derived coefficient naturality proof uses
source and target coefficient naturality together with naturality of
`projectionInverseImageIso`. Ordinary-cohomology and section naturality
use the actual pullback natural transformations, whiskered by inverse
image and composed with this coefficient comparison. The private
`arrowDerivedCategories` selects the two given original-scheme instances;
it adds no independent derived-category existence assumption.

## Specified recovery maps

`homologyFunctorIso n` recovers ordinary degree-`n` cohomology from derived
sections with its full `G`-action, naturally in the base sheaf.
`derivedZeroFunctorIso` recovers the section action from degree-zero
homology. `cohomologyZeroFunctorIso` recovers sections from ordinary
cohomology in degree zero. They are the parent's specified comparisons,
evaluated at the sole level. Their `*_hom_app_hom` formulas give the
original-scheme `homologyNatIso`, `homologyZeroIso`, and, for ordinary
degree zero, `homologyNatIso` inverse followed by `homologyZeroIso`, each
at `(inverseImage p R).obj M`.

`derivedMap_homology`, `derivedMap_zero`, and `cohomologyMap_zero` prove the
three recovery squares as equalities of full equivariant natural
transformations in all base sheaves. The first two proofs use the
published geometric pullback-with-coefficients homology and zero formulas
after natural-transformation and action extensionality. The third projects
the parent's specified ordinary-degree-zero comparison naturality in the
two-level tower, rewriting every map to the original geometry. All three
squares preserve these specified comparisons.

## Provenance and retained obligations

This is a derived internal adapter of `EtaleCanonicalDeckTower`,
`EtaleCanonicalCoefficientDiagram`, the actual inverse-image construction,
and the geometric pullback-with-coefficients comparisons. Mathlib supplies
actions, the over category, functor evaluation, and composable arrows.
No new assertion is attributed to an external source.

This unit removes an etaleness restriction from the input interface for
single-scheme deck actions and supplies arbitrary original-map pullback.
The older restriction-based `EtaleDeckAction` comparison, a bundled category
and consumer functors for all such raw geometric inputs, the analytic-etale
realization, arithmetic tower identifications, and the Harris/Shimura
specializations remain separate construction obligations. It does not
complete the host Harris framework.
