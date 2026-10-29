# The equivariant sheaf of indexed coefficient families

Author: Worker 716.

Module `Langlands.Sheaf.Equivariant.CoinducedFamilies`, namespace
`Langlands.Sheaf.Equivariant.CoinducedFamilies`. It imports Worker 865's
published `Langlands.Sheaf.Equivariant.CoinducedFamilies.Coordinates` and
shares its namespace.

## Provenance

This is an internal, derived construction made for task
`a9be12c4-547d-4816-93e3-db130184646e`, the explicit-coinduction dependency of
task `cc59409b-1c8d-4bff-ab98-6bb68ff786bf`. It does not formalize a numbered
statement from the literature, and it adds no hypothesis. The indexed families
are the elementary description of sections of a right Kan extension along the
inclusion of ordinary opens into the transport category. A section over `U` is
determined by its values on the translated opens `{y | g • y ∈ U}`, one for each
label `g`. The comparison below is an isomorphism with the actual published
`coinduction`. It is obtained from the published coordinates, which come from
Mathlib's pointwise right Kan extension. No new right adjoint is introduced.

## Setting

All types have one universe `u`. `R` is a commutative ring, `G` a group, and `X`
a topological space with a `MulAction G X`. `A : X → ModuleCat.{u} R` is an
arbitrary family of modules, with no compatibility between different points.
The construction of `presheaf A` and `sheaf A`, and the sheaf condition, need
no further hypothesis. The comparison section additionally assumes
`[ContinuousConstSMul G X]`, which the published `coinduction` requires. No
topology on `G`, separation, local compactness, paracompactness or joint
continuity is used.

## Indexed families

For `U : ActionOpens G X`,

```text
FamilySections A U = ∀ (g : G) (y : {y : X // g • y ∈ U.openSet}), A y.1
```

(an `abbrev`). The index is a type-valued subtype, so Mathlib's pointwise `Pi`
instances make it an `R`-module. `families_congr` says that entries with equal
labels agree, whatever the membership proofs: if `e : g = h`, then
`s g ⟨y, hg⟩ = s h ⟨y, hh⟩`.

For a transport arrow `f : U ⟶ V`, `familyPull A f : FamilySections A V →ₗ[R] FamilySections A U`
sends `s` to the family

```text
(g, ⟨y, h⟩) ↦ s (f.label * g) ⟨y, _⟩,
```

with membership `(f.label * g) • y ∈ V.openSet` from `f.mapsTo (g • y) h` and
`mul_smul`. Addition and scalar multiplication are preserved pointwise by `rfl`.

`presheaf A : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R` has objects
`ModuleCat.of R (FamilySections A U.unop)` and maps `ModuleCat.ofHom (familyPull A f.unop)`.
Its identity law is `families_congr` with `one_mul`. Its composition law is
`families_congr` with `mul_assoc`, because the label of a composite is
`(f ≫ k).label = k.label * f.label`.

## Coordinate evaluation

- `presheaf_map_apply A f s g y hy` holds by `rfl`. For any transport arrow
  `f : U ⟶ V`, any `s : FamilySections A V` and any `hy : g • y ∈ U.openSet`,
  `(presheaf A).map f.op s g ⟨y, hy⟩ = s (f.label * g) ⟨y, _⟩`. Transport
  multiplies the group index on the left and keeps the coefficient point `y`.
- `presheaf_map_inclusionHom_apply A h s g y hy` covers a label-one inclusion
  `ActionOpens.inclusionHom h` with `h : U.openSet ≤ V.openSet`:
  `(presheaf A).map (ActionOpens.inclusionHom h).op s g ⟨y, hy⟩ = s g ⟨y, h hy⟩`.
  Ordinary restriction simply drops the entries outside the smaller open.
- `underlying_map_apply A i s g y hy` is the same formula for the underlying
  ordinary presheaf `(underlyingPresheaf G X (ModuleCat.{u} R)).obj (presheaf A)`
  and an inclusion `i : V ⟶ W` of `Opens X`: the result is `s g ⟨y, i.le hy⟩`.

## Sheaf condition

`isSheaf A : sheafProperty G X (ModuleCat.{u} R) (presheaf A)` is the published
equivariant sheaf condition: the underlying ordinary presheaf is a sheaf. The
proof rewrites with Mathlib's `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`,
which applies to `ModuleCat.{u} R` because its forgetful functor preserves limits
and reflects isomorphisms. Let `sf i` be a compatible family over opens `U i`.

1. Evaluating the compatibility equation over `U i ⊓ U j` at an index
   `(g, y)`, and using `underlying_map_apply` on both sides, shows
   `sf i g ⟨y, hi⟩ = sf j g ⟨y, hj⟩` whenever `g • y` lies in both opens.
2. For an index `(g, y)` with `g • y ∈ iSup U`, `Opens.mem_iSup` gives some `i`
   with `g • y ∈ U i`. A choice `idx g y` of such an `i` defines the glued family
   `s g y = sf (idx g y) g ⟨y.1, _⟩`.
3. Restricting `s` to `U i` gives `sf i`, by `underlying_map_apply` and step 1.
4. Any gluing `t` agrees with `s`. Evaluate its gluing equation over
   `U (idx g y)` at `(g, y)`.

`sheaf A : TopologicalSheaf G X (ModuleCat.{u} R)` is `⟨presheaf A, isSheaf A⟩`.
Its sections over `U` are definitionally `ModuleCat.of R (FamilySections A U)`.

## Comparison with the published coinduction

Assume also `[ContinuousConstSMul G X]` and let
`F : TopologicalSheaf G X (ModuleCat.{u} R)`. In the published Coordinates
module, `Coefficients F y` is the stalk at `y` of
`(toSheaf G X (ModuleCat.{u} R)).obj F`. `coinducedZero F` is
`(coinduction G X (ModuleCat.{u} R)).obj ((toSheaf G X (ModuleCat.{u} R)).obj (Godement.zeroSheaf F.obj))`.
`coordinateIso F U` identifies its sections over `U` with
`ModuleCat.of R (Sections F U)`. `Sections F U` is definitionally
`FamilySections (Coefficients F) U`.

- `coinducedZeroPresheafIso F : (coinducedZero F).obj ≅ presheaf (Coefficients F)`
  is `NatIso.ofComponents` of the isomorphisms `coordinateIso F U.unop`.
  Naturality for an arbitrary transport arrow is the published `read_map`
  (`read F U` is `(coordinateIso F U).toLinearEquiv`). It is checked
  coordinatewise after `ext`.
- `coinducedZeroIso F : coinducedZero F ≅ sheaf (Coefficients F)` is an
  isomorphism in the category `TopologicalSheaf G X (ModuleCat.{u} R)` of
  equivariant sheaves. It is `ObjectProperty.isoMk` of the presheaf
  isomorphism above, so it commutes with every transport arrow, not only with
  ordinary restrictions.
- `coinducedZeroIso_hom_apply F U s` gives, by `rfl`,
  `(coinducedZeroIso F).hom.hom.app (op U) s = read F U s`.
- `coinducedZeroIso_inv_apply F U s` gives, by `rfl`,
  `(coinducedZeroIso F).inv.hom.app (op U) s = (read F U).symm s`.

The published `Godement.zeroIso` relates `Godement.zeroSheaf F.obj` to the
ordinary Godement functor. Its use under coinduction already appears in
`Langlands.Cohomology.CompactSoft.SmoothZeroBridge`. This module does not
repeat that connection. It makes no smoothness, compact-support or c-softness
assertion.

The section type is the existing `Langlands.Cohomology.CompactSoft.FamilySections`, imported from [FamilySections](FamilySections.md). The duplicate `Families` abbreviation has been removed; its dependent-product meaning is unchanged.
