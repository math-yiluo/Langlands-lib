# Restriction `F|_Y` of a complex vector sheaf to a subset

Module `Langlands.Sheaf.Renard.LocallyClosedRestriction`, namespace
`Langlands.Sheaf.Renard.LocallyClosedRestriction`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This file covers the paragraph of II.2.5 that defines the restriction of a sheaf, printed p.42 /
PDF p.48:

> Si `F` est un faisceau sur l'espace t.d. `X` et que `Y` est une partie localement fermée de
> `X`, alors on définit un faisceau `F|_Y` sur `Y`, que l'on appelle restriction de `F` à `Y`. La
> fibre de `F|_Y` en un point `y ∈ Y` est égale à la fibre `F_y`, et les sections au-dessus d'un
> ouvert `U` de `Y` sont celles qui coïncident au voisinage de chaque point de `U` avec la
> restriction d'une section de `F`. Lorsqu'on identifie `F` au faisceau des sections de `F̂`,
> `F|_Y` s'identifie au faisceau des sections au-dessus des ouverts de `Y`.

The same page uses `F|_Z` for a closed `Z` in the Proposition `0 → F_c(U) → F_c(X) → F_c(Z) → 0`,
with `F_c(Z) = (F|_Z)_c(Z)`. The published statement of that Proposition
([ClosedRestrictionExactStatements](ClosedRestrictionExactStatements.md), proof Task 5960)
works with families of germs over `Z` directly and leaves the sheaf `F|_Y` itself as a
separate obligation. This file constructs that sheaf, proves the source's fibre assertion, and
identifies the published `F_c(Z)` with the compactly supported global sections of `F|_Z`.
It does not modify the published statement or prove it.

Every declaration is a definition or a proved theorem. There is no proposition for a later
proof task.

## Setting

- `F : VectorSheafScalars.VectorSheaf X` (published, [VectorSheafScalars](VectorSheafScalars.md)):
  Mathlib's sheaf of complex vector spaces on all opens of `X`, with `X : Type u` any
  topological space. Renard's sheaves are of base `T_c`; by the final paragraph of II.2.1 these
  are the same as sheaves on all opens, which is the Library's convention.
- `Y : Set X` is an **arbitrary** subset with the subspace topology. Renard asks `Y` to be
  locally closed. That hypothesis is what makes `Y` a t.d. space (locally compact), so that
  the later theory applies to `F|_Y`. The construction and every result here hold for any
  subset, so the file does not assume it.
- `F_y` is Mathlib's stalk `F.presheaf.stalk y` (a colimit over the open neighbourhoods of
  `y`), and `F.presheaf.germ W y` is the germ map. The étalé space `F̂` of the source (printed
  with a hat) is the disjoint union of these stalks. A section of `F̂` over a set is a family of
  germs, which is how sections of `F|_Y` are represented below.

## The sheaf `F|_Y`

- `Fiber F Y y` is the stalk `F_y`, for `y ∈ Y`.
- `isRestrictedGerm F Y` is a Mathlib prelocal predicate on families
  `f : ∀ y ∈ V, F_y` over an open `V` of `Y`. It says that there are an open `W` of `X`
  containing `V` and a section `t ∈ F(W)` whose germ at every `y ∈ V` is `f(y)`. This is "the
  restriction of a section of `F`".
- `isLocallyRestrictedGerm F Y` is its sheafification as a local predicate (Mathlib's
  `PrelocalPredicate.sheafify`): every point of `V` has an open neighbourhood in `V` on which
  `f` is a restricted germ. This is exactly the source's condition "coïncident au voisinage de
  chaque point de `U` avec la restriction d'une section de `F`".
- `sections F Y V` is the complex subspace of `∀ y ∈ V, F_y` cut out by this condition. Closure
  under `0`, `+` and scalars is `isRestrictedGerm_zero`, `isLocallyRestrictedGerm_add` and
  `isLocallyRestrictedGerm_smul`. The proofs restrict representing sections to intersections
  and use Mathlib's `germ_res_apply`. `mem_sections_iff` restates membership.
- `restrictLinear` is restriction of families to a smaller open, and `presheaf F Y` is the
  presheaf of complex vector spaces on `Y`.
- `underlyingIso F Y` identifies its underlying presheaf of sets with Mathlib's
  `subpresheafToTypes` of the local predicate. `presheaf_isSheaf` then follows from Mathlib's
  `TopCat.subpresheafToTypes.isSheaf`, since the forgetful functor of complex vector spaces
  reflects the sheaf condition (`isSheaf_iff_isSheaf_comp'`).
- `restrict F Y : VectorSheaf Y` is Renard's `F|_Y`. `restrict_map_apply` says restriction
  maps are restriction of families. Being a `VectorSheaf`, `F|_Y` is automatically a sheaf of
  `𝒞^∞_Y`-modules by the published II.2.5 Proposition (`VectorSheafScalars`).

## Restriction of sections of `F`

- `traceOpen Y W` is the open `W ∩ Y` of `Y`, for an open `W` of `X`.
- `restrictSection F Y W : F(W) →ₗ[ℂ] F|_Y(W ∩ Y)` sends a section `t` to its family of germs
  `y ↦ t_y`. This is the source's "restriction d'une section de `F`".
  `restrictSection_apply` is its defining formula.

## Fibres: `(F|_Y)_y = F_y`

- `evalLinear` / `evalCocone`: evaluation `f ↦ f(y)` of families on open neighbourhoods of `y`
  forms a cocone. `stalkToFiber F Y y : (F|_Y)_y ⟶ F_y` is the induced map from Mathlib's
  colimit stalk. `stalkToFiber_germ` says that it sends the germ of `f` to `f(y)`.
  `stalkToFiber_restrictSection` says that it sends the germ of `restrictSection t` to the
  germ `t_y`.
- `stalkToFiber_surjective`: every element of `F_y` is the germ of some `t ∈ F(W)` (Mathlib's
  `exists_germ_eq`, using the published filtered-colimit instances of `VectorSheafScalars`),
  and is the image of the germ of `restrictSection t`.
- `stalkToFiber_injective`: if two families have the same value at `y`, their representing
  sections near `y` have the same germ. So they agree on an open `W` of `X` around `y`
  (Mathlib's `germ_eq`), the two families agree on a neighbourhood of `y` in `Y`, and their
  germs are equal (Mathlib's `germ_ext`).
- `stalkIso F Y y : (F|_Y)_y ≅ F_y` is the resulting isomorphism of complex vector spaces, with
  `stalkIso_hom`. This is the source's "la fibre de `F|_Y` en un point `y ∈ Y` est égale à la
  fibre `F_y`".

## Functoriality

- `mapSections Y φ V` applies the stalk maps of a morphism `φ : F ⟶ G` pointwise:
  `f ↦ (y ↦ φ_y(f(y)))`. Locally restricted germs go to locally restricted germs by Mathlib's
  `stalkFunctor_map_germ_apply`.
- `restrictMap Y φ : F|_Y ⟶ G|_Y` and `restrictFunctor X Y : VectorSheaf X ⥤ VectorSheaf Y`.
  `mapSections_apply` gives the formula.
- `mapSections_restrictSection`: restriction of sections commutes with morphisms.

## Comparison with the published `F_c(Z)`

This section needs `X₀ : Type`, the universe of the published
`ClosedRestrictionExactStatements` and of the published `CompactSupport` for complex
coefficients. `Z : Set X₀` is again arbitrary.

- `isLocalRestriction_iff`: the published predicate `ClosedRestriction.IsLocalRestriction F Z t`
  holds exactly when the family `t` (read on the top open of `Z` by `topFamily`) is a global
  section of `F|_Z`. One direction uses the open `W ∩ Z`. The other writes the neighbourhood
  in `Z` as `O ∩ Z` with `O` open in `X₀` (Mathlib's `isOpen_induced_iff`).
- `Γgerm_eq_zero_iff` and `support_eq`: the published support `CompactSupport.support` of a
  global section of `F|_Z` (the points with nonzero germ) is the set of points where the family
  is nonzero, by `stalkToFiber_germ` and `stalkToFiber_injective`.
- `closedCompactEquiv F Z : ClosedRestriction.closedCompactSections F Z ≃ₗ[ℂ]
  CompactSupport.submodule (restrict F Z).presheaf`. The published `F_c(Z)` is literally
  `(F|_Z)_c(Z)`, as in the source's notation `F_c(Z) = (F|_Z)_c(Z)`. `closedCompactEquiv_apply`
  gives its formula, and `mem_compactSupport_of` is the membership criterion used in it.
- `closedCompactEquiv_restrictToClosed`: through `closedCompactEquiv`, the published
  `p_Z = ClosedRestriction.restrictToClosed` sends `φ` to the restriction of the global section
  `φ` to `F|_Z` (`restrictSection`).

## Provenance

The sheaf, its fibre isomorphism and the functor are the source's definition and its fibre
assertion. The source gives no construction details beyond the quoted paragraph. The
germ-family presentation follows the source's own identification with sections of the étalé
space. It uses Mathlib's local-predicate sheaves, as Mathlib's sheafification of
`Type`-valued presheaves does. The comparison with `closedCompactSections` and the formula for
`restrictToClosed` are internal links to the published statement of the II.2.5 Proposition.
The arbitrary subset `Y` is a harmless generalization of "localement fermée". Worker 4 wrote
this unit for the whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857` (Task 1222), in
agreement with Worker 1222.
