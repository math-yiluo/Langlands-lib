# Smooth direct image and proper compact sections of ℓ-divisible systems

Author: Worker 61. This module builds on the following published modules:

- `Langlands.Cohomology.DivisibleSystem`: `ℓ`-divisible systems (Harris 1999,
  (2.1)) and `SmoothSheafDivisibleSystem R G X ℓ`.
- `Langlands.Cohomology.DivisibleSystem.LeftExact`: `mapLeftExact`,
  `mapLeftExactHom` and `compactSectionsSystem`.
- Worker 13's `Langlands.Sheaf.Equivariant.SmoothDirectImage`: the smooth
  direct image `SmoothDirectImage.functor f hf`, its `inclusion` into the
  ordinary direct image, `idIso`, `compMap` and their laws.
- Worker 13's `Langlands.Sheaf.Equivariant.ProperSmoothCompactSections`: the
  natural transformation `natTrans f hf hp` from compact sections of the
  smooth direct image to compact sections, for proper `f`, with
  `natTrans_id` and `natTrans_comp`.
- `Langlands.Sheaf.Equivariant.Limits`: `toTransportPresheaf` creates limits.

All names below are in the namespace `Langlands.Cohomology.DivisibleSystem`.
Write `T m` for `T.obj m`, `i` for the inclusions `T.inclusion`
and `j` for the projections `T.projection h : T m ⟶ T m'` (`m' ≤ m`), as in the
parent module. For a continuous equivariant map `f`, write `f_*` for
`SmoothDirectImage.functor f hf`.

The module applies `mapLeftExact` from the LeftExact module to smooth direct
image, and to compact sections composed with it. Smooth direct image is only
left exact. So each system below carries an explicit hypothesis that the
relevant functor maps the projections `j` to epimorphisms, and no such
hypothesis is derived here. By `epi_map_projection_of_succ` in the LeftExact
module, it suffices to check the successive projections `T (m + 1) ⟶ T m`.

## Left exactness

`A` is any category. `G` is a group acting on topological spaces `X` and `Y`,
and `f : C(X, Y)` comes with its equivariance equation `hf`.

- `directImageSheaf_preservesLimitsOfShape f hf A J`: if `A` has limits of
  shape `J`, the ordinary equivariant direct image
  `DirectImage.sheaf f hf A` preserves them. Proof: the presheaf direct image
  is precomposition with the inverse-image map on opens, so it preserves
  limits. The square with `toTransportPresheaf` on `X` and on `Y` commutes
  definitionally, and `toTransportPresheaf` on `Y` reflects limits because
  it creates them.
- `directImageSheaf_preservesFiniteLimits f hf A`: the case of finite limits,
  when `A` has finite limits.

From here on, `R` is a commutative ring and `R`, `G` and the spaces lie in one
universe. `G` is a topological group, it acts by continuous translations, and
`HasStableNeighbourhoods G -` holds for the spaces, as in
`SmoothDirectImage`.

- `smoothCoreflector_preservesFiniteLimits`: the smooth part
  `smoothCoreflector R` preserves finite limits. It is the right adjoint of
  the published `smoothAdjunction R`.
- `directImageSheaf_additive f hf`: the ordinary direct image of
  `ModuleCat R`-valued sheaves is additive, because it preserves binary
  products (Mathlib's `Functor.additive_of_preserves_binary_products`).
- `smoothDirectImage_preservesFiniteLimits f hf`: `f_*` preserves finite
  limits. By definition it is the smooth inclusion, followed by the ordinary
  direct image, followed by the smooth part, and each of the three preserves
  finite limits.

## Systems along a single map

`T : SmoothSheafDivisibleSystem R G X ℓ`. The hypothesis `hT` says that
`f_*(j)` is an epimorphism for every projection `j` of `T`.

- `smoothDirectImageSystem f hf T hT : SmoothSheafDivisibleSystem R G Y ℓ` is
  `T.mapLeftExact f_* hT`. `smoothDirectImageSystem_tower` (tower
  `T.tower ⋙ f_*`) and `smoothDirectImageSystem_inclusion` (inclusions
  `f_*(i)`) hold by `rfl`.
- `smoothDirectImageSystemMap f hf a hT hT'`: a morphism `a : T ⟶ T'` of
  systems, both satisfying the hypothesis, gives the morphism with
  components `f_*(a)` (`mapLeftExactHom`). `_tower_app` records the
  components.
- `smoothDirectImageSystemInclusion f hf T hT hT'`: the inclusion of the
  smooth direct image into the full ordinary direct image, as a morphism of
  `ℓ`-divisible systems of ordinary equivariant sheaves on `Y`. The source is
  `smoothDirectImageSystem f hf T hT` mapped along the exact smooth inclusion
  (the parent module's `DivisibleSystem.map`). The target is `T.mapLeftExact`
  of the smooth inclusion followed by the ordinary direct image. It needs its
  own hypothesis `hT'` that this composite maps the projections to
  epimorphisms. The components are those of `SmoothDirectImage.inclusion`
  (`_tower_app`), and each is a monomorphism
  (`mono_smoothDirectImageSystemInclusion_tower_app`).

## Identity and composition

- `smoothSpatial_id_equivariant` and `smoothSpatial_comp_equivariant f hf g
  hg` are the equivariance equations of the identity and of `g ∘ f`.
- `epi_smoothDirectImage_id_map_projection T h`: along the identity, the
  hypothesis holds for every system. The functor `id_*` is isomorphic to the
  identity functor (`SmoothDirectImage.idIso`), so it preserves
  epimorphisms, and the projections of `T` are epimorphisms.
- `smoothDirectImageSystemIdIso T : T ≅ smoothDirectImageSystem id _ T _`, with
  components `SmoothDirectImage.idIso` (`_hom_tower_app`). It commutes with
  the inclusions by naturality.
- `smoothDirectImageSystemCompMap f hf g hg T hT hT' hT''`: for
  `g : C(Y, Z)`, the morphism from `g_*(f_* T)` to `(g ∘ f)_* T`, with
  components `SmoothDirectImage.compMap` (`_tower_app`). Each of the three
  systems carries its own hypothesis (`hT` for `f_*` on `T`, `hT'` for `g_*`
  on `f_* T`, `hT''` for `(g ∘ f)_*` on `T`).
- `smoothDirectImageSystemCompMap_id_left`: `f_*` of
  `(smoothDirectImageSystemIdIso T).hom`, followed by the comparison for
  `id` then `f`, is the identity of `f_* T`.
- `smoothDirectImageSystemCompMap_id_right`:
  `(smoothDirectImageSystemIdIso (f_* T)).hom`, followed by the comparison
  for `f` then `id`, is the identity of `f_* T`.
- `smoothDirectImageSystemCompMap_assoc`: for `e : C(Z, W)`, the two
  morphisms from `e_*(g_*(f_* T))` to `((e ∘ g) ∘ f)_* T` agree. The first is
  `e_*` of the comparison for `f`, `g` followed by the comparison for
  `g ∘ f`, `e`. The second is the comparison for `g`, `e` at `f_* T` followed
  by the comparison for `f`, `e ∘ g`. Each of the systems involved carries
  its own hypothesis (`hT`, `hT₁`, …, `hT₆`).

The three laws are proved levelwise from `SmoothDirectImage.compMap_id_left`,
`compMap_id_right` and `compMap_assoc`, with `hom_ext` of the parent module.
The comparison maps of systems are not claimed to be isomorphisms.

## Proper pullback on compact sections

`hp : IsProperMap f`. `compactSectionsSystem S hS` is the LeftExact module's
system of compactly supported sections of a system `S` of smooth sheaves,
`S.mapLeftExact (smoothSheafCompactSections R G -) hS`.

- `properCompactSectionsSystemMap f hf hp T hT hc hc'`: the morphism
  `compactSectionsSystem (f_* T) hc ⟶ compactSectionsSystem T hc'` with
  components `(ProperSmoothCompactSections.natTrans f hf hp).app (T m)`
  (`_tower_app`). Here `hc` says that compact sections of the projections of
  `f_* T` are epimorphisms, and `hc'` says the same for `T`.
- `properCompactSectionsSystemMap_id T hc hc'`: compact sections of
  `(smoothDirectImageSystemIdIso T).hom` (by `mapLeftExactHom`), followed by
  the morphism along the identity, is the identity. This is
  `ProperSmoothCompactSections.natTrans_id` at each level.
- `properCompactSectionsSystemMap_comp f hf g hg hp hq T …`: for proper `f`
  and `g`, compact sections of `smoothDirectImageSystemCompMap`, followed by
  the morphism along `g ∘ f`, equals the morphism along `g` (for the system
  `f_* T`) followed by the morphism along `f`. This is
  `ProperSmoothCompactSections.natTrans_comp` at each level.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.304–306 (one-based
PDF pages 6–8). Worker 61 read p.304 in the rendered scan and pp.305–306 in
the extracted text.

1. What Harris uses. On p.304 Harris defines `ℓ`-divisible systems of étale
   sheaves in smooth `ℤ/ℓ^mℤ[S(ẽ)]`-modules by (2.1). He states that
   Berkovich's acyclic functor `T ↦ F(T)` is exact (Fact 3) and carries
   `ℓ`-divisible systems to `ℓ`-divisible systems (Fact 4). He adds: "The
   functor F(T) is expressed as the composition of two functors, denoted
   𝒞⁰ = ν_*ν^* and b^* by Berkovich, who verifies that both functors are
   exact." In (2.3) (p.305) he computes compactly supported cohomology from
   sections of these systems. On pp.304–306 a direct image appears only
   inside Berkovich's construction, where it is exact. These pages state
   neither a direct image of `ℓ`-divisible systems along a general
   equivariant map nor a pullback of compact sections along a proper map at
   the level of systems.
2. What is formalized. The module is internal framework. It puts Worker 13's
   smooth direct image and proper compact-section pullback at the level of
   `ℓ`-divisible systems, so that constructions on systems can use them. The
   general smooth direct image is only left exact. So the image of a system
   is a system only under the explicit epimorphism hypotheses, by the
   LeftExact module's `mapLeftExact`. This is weaker than Harris's situation,
   where the functors are exact. The hypotheses are not derived from
   exactness of any particular direct image, from acyclicity or from
   properness.
3. Sites. As in the parent module, the Library's sheaves are equivariant
   sheaves on topological spaces with ordinary opens, not étale sheaves on
   rigid analytic spaces. Compactly supported sections are the Library's
   `smoothSheafCompactSections`, the available counterpart of `Γ_c`.
4. The left exactness instances are standard. Direct image preserves limits
   because limits of sheaves are computed on sections, and the smooth part
   preserves limits as a right adjoint.

## Scope

The module does not prove that any direct image is exact, that any
projection maps to an epimorphism, that the comparison maps of systems are
isomorphisms, or any statement about cohomology. It does not construct
Berkovich's functors `ν_*ν^*` and `b^*`, inverse images of systems, or derived
direct images.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
