# Restriction comparison for maps of original deck geometries

This internal construction extends the fixed-geometry comparison of
`EtaleSchemeDeckRestriction` to actual étale maps between two original deck
geometries. It constructs the restriction maps and proves that all three
canonical comparisons commute with them, retaining the specified recovery maps.

## Inputs and conventions

Let `p : Y ⟶ X`, `q : Z ⟶ X`, and `f : Z ⟶ Y` be étale scheme maps, with
`hf : f ≫ p = q`. Let `R` be a commutative ring. Schemes, the ring, and module
coefficients use universe `u`. A group `G : Type t` acts through the original
homomorphisms `τ : G →* (Aut Y)ᵐᵒᵖ` and `σ : G →* (Aut Z)ᵐᵒᵖ`.
The original equations are

```
hp g : (aut τ g).hom ≫ p = p
hq g : (aut σ g).hom ≫ q = q
he g : f ≫ (aut τ g).hom = (aut σ g).hom ≫ f.
```

Here `aut` is the inherited unop convention. The cohomology maps go from `Y`
to `Z`, as required by pullback along the original map `f`. Every map below
is natural in the arbitrary base coefficient sheaf `M : ModuleSheaf X R`
and takes values in the category of `G`-actions.

The coefficient triangle, restriction section and ordinary cohomology maps,
their component formulas, and their ordinary degree-zero square need no
derived-category instances. The derived maps and recovery squares, and all
comparisons with the canonical inverse-image consumers, retain
`HasDerivedCategory.{wY} (ModuleSheaf Y R)`,
`HasDerivedCategory.{wY} (ModuleSheaf Z R)`, and
`HasDerivedCategory.{wR} (ModuleCat.{u} R)`.
The two sheaf categories use a common size `wY`; the module size `wR` and group
universe `t` are independent. No such instance over the base `X` is required.

## The actual restriction triangle

`restrictionTriangleIso` identifies the old deck coefficient functor for `p`
followed by equivariant restriction along `f` with the old deck coefficient
functor for `q`. It is constructed from equivariant restriction composition
and restriction transport along the supplied original equation `hf`.
Equivariance is inherited from those constructions using `hp`, `hq`, and `he`;
it is not a separate cohomological input.

Write `Mp = restriction(p) M`, `Mq = restriction(q) M`, and

```
c_M = (restrictionComp p (ModuleCat R) f).hom.app M ≫
        (restrictionCongr R hf).hom.app M.
```

The theorem `restrictionTriangleIso_hom_app_hom` proves that the underlying
coefficient map is exactly `c_M : restriction(f) Mp ⟶ Mq`.
Its proof expands the actual equivariant composition and equality-transport
components.

## Three restriction maps and their formulas

`restrictionSectionsMap`, `restrictionCohomologyMap n`, and
`restrictionDerivedMap` first apply the inherited equivariant geometric
restriction map along `f` and then apply their corresponding consumer to the
constructed restriction triangle. The degree `n` is any natural number;
derived sections are bounded below.

Their `*_app_hom` theorems identify the underlying maps as

```
sectionsMap(f)_Mp ≫ sections(Z).map c_M
cohomologyMapWithCoefficients f R n c_M
derivedSectionsMapWithCoefficients f R c_M.
```

Thus each map uses the original geometric pullback and the specified original
triangle coefficient. The proofs expand the defining whiskerings and their
components, then use the inherited equivariant pullback formulas.

`restrictionCohomologyMap_zero` proves the full equivariant natural square
between ordinary degree-zero cohomology and sections, using the inherited
`restrictionCohomologyZeroIso` at each geometry. On underlying maps the proof
is naturality of the canonical `cohomologyZeroIso` at `c_M`, followed by the
existing geometric degree-zero restriction square.

## Recovery and comparison squares

`restrictionDerivedMap_homology n` states that applying homology to the new
restriction-derived map and then using `deckDerivedHomologyIso` at `Z`
equals using `deckDerivedHomologyIso` at `Y` and then the new ordinary
restriction map. The proof exposes the underlying homology map, expands the
specified recovery components, and applies
`derivedSectionsMapWithCoefficients_homology` at `c_M`.

`restrictionDerivedMap_zero` is the corresponding square with
`deckDerivedZeroIso` and the new section map. Its proof identifies the inherited
recovery component with the original `homologyZeroIso`. Naturality at `c_M`
and the existing geometric `derivedSectionsMap_zero` prove the square.
These are equalities of entire coefficient-natural transformations in
`Action`, retaining all group commutation laws.

The three comparison theorems are

```
derivedMap f ≫ derivedRestrictionIso(Z) =
  derivedRestrictionIso(Y) ≫ restrictionDerivedMap f
cohomologyMap f n ≫ cohomologyRestrictionIso(Z,n) =
  cohomologyRestrictionIso(Y,n) ≫ restrictionCohomologyMap f n
sectionsMap f ≫ sectionsRestrictionIso(Z) =
  sectionsRestrictionIso(Y) ≫ restrictionSectionsMap f.
```

The names in Lean are `derivedMap_restriction`, `cohomologyMap_restriction`,
and `sectionsMap_restriction`. All three preserve the exact original map `f`,
equations `hf` and `he`, and every base coefficient sheaf.

The derived proof applies the previously proved
`projectionInverseImageIso_restriction` coefficient square, the precomposition
and postcomposition laws for actual geometric pullback with coefficients,
and its existing comparison with étale restriction. The ordinary and section
proofs transport this derived square through the specified invertible recovery
maps on both sides and cancel the source recovery. They do not infer equality
of derived maps from equality on homology.

## Provenance and remaining scope

This is an internal coherence construction from the existing actual inverse
image, equivariant étale restriction, and geometric pullback consumers.
It uses the proved coefficient square in `EtaleSchemeDeckRestriction`;
no additional external source theorem or cohomology compatibility is assumed.

The unit compares individual actual étale maps and is natural in all base
coefficients. It does not assemble a category of all étale deck geometries or
a comparison of consumer functors on that category. The structure maps and
the geometric map are required to be étale, although the canonical
inverse-image construction itself allows arbitrary scheme maps.
No covering, torsor, freeness, topological continuity, smoothness,
compact-support, properness, or finiteness result is asserted. Analytic
realization, arithmetic level towers, and Harris/Shimura specialization remain
obligations of the broader framework.
