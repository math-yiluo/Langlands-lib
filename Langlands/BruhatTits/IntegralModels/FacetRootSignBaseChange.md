# The facet root identity under extension of local coefficients

Module `Langlands.BruhatTits.IntegralModels.FacetRootSignBaseChange`.

## Setting

`R` and `A` are local domains with fraction fields `K` and `L`. The maps
`R → A`, `R → K`, `A → L`, `K → L` and `R → L` form a commuting square
(`IsScalarTower R A L`, `IsScalarTower R K L`), and `R → A` is a local
homomorphism. The residue fields are `κ_R` and `κ_A`, with the induced
extension `κ_R → κ_A`. `G` is a group scheme over `K`.

The Library already changes the coefficients of a KP relative component
model `D` of `G` along this square: `D.baseChange A L` is a relative
component model of the base change of `G` to `L`
(`RelativeComponentFunctoriality`). This module does the same for model
morphisms, integral tori and special-fibre quotient data. It then compares
the special fibres and the reductive images of the base-changed data with
the residue-field base change of the original ones. Finally it descends the
root form of the facet sign formula from `A` to `R`.

## Content

### Residue-field descent of a signed root identity

`roots_eq_nonneg_of_residueBaseChange`. Let `T` be a split torus over `κ_R`
with homomorphisms `t : T ⟶ H` and `a : T ⟶ Q` into affine group schemes
locally of finite type over `κ_R`. Let `t' : T' ⟶ H'` and `a' : T' ⟶ Q'`
be homomorphisms over `κ_A` into affine group schemes. Let `e`, `f`, `g` be isomorphisms from the base
changes to `κ_A` of `T`, `H`, `Q` to `T'`, `H'`, `Q'`, compatible with
`t, t'` and with `a, a'`. Let `s` and `s'` be real functions on the
character lattices of `T` and `T'` with `s' (e(χ_{κ_A})) = s χ` for every
character `χ` of `T`. If

`roots t' = {χ ∈ roots a' | 0 ≤ s' χ}`,

then `roots t = {χ ∈ roots a | 0 ≤ s χ}`. The statement is written with the
ring structure of the residue fields that the Library's special fibres use.

### Coefficient change of the remaining model data

- `RelativeComponentModelHom.baseChange A L φ`: for a morphism
  `φ : D' ⟶ D` of relative component models, the base change of its full
  and neutral homomorphisms along `R → A`. The generic compatibilities come
  from the Library's `baseChangeGenericIso_naturality`. The simp lemmas
  `baseChange_full_hom` and `baseChange_neutral_hom` record the two
  homomorphisms.
- `IntegralTorusData.genericInclusionOf D torus inclusion`: for a
  commutative `R`-group scheme `torus` with a homomorphism `inclusion` into
  the neutral model of `D`, the generic fibre of `inclusion` followed by the
  generic identification of the neutral model.
- `IntegralTorusData.ofInclusion D torus inclusion`: the integral torus of
  `D` with integral torus `torus`, its own generic fibre as generic torus
  (identity generic identification) and generic inclusion
  `genericInclusionOf D torus inclusion`.
- `IntegralTorusData.baseChangeInclusion A L T` and
  `IntegralTorusData.baseChange A L T`: for an integral torus `T` of `D'`,
  the base change of `T.inclusion` along `R → A`, and the integral torus
  `ofInclusion` of `D'.baseChange A L` built from the base change of
  `T.torus` and this inclusion. Its generic torus is the generic fibre of
  the base-changed integral torus. The simp lemmas `ofInclusion_torus`,
  `ofInclusion_inclusion`, `baseChange_torus` and `baseChange_inclusion`
  record the fields.
- `IntegralTorusData.isSplitTorus_baseChange`: if `T.torus` is split, so is
  `(T.baseChange A L).torus`.

### Special fibres

- `IntegralTorusData.specialCharacterEquiv_apply`: the Library's
  `specialCharacterEquiv` is the base change of characters to `κ_R`. This
  holds by definition.
- `residueExtension_comp_residueBaseMap`: the residue maps commute with the
  coefficient change: `Spec κ_A → Spec κ_R → Spec R` equals
  `Spec κ_A → Spec A → Spec R`.
- `specialFibreSquareIso A M`: for a group scheme `M` over `R`, the
  isomorphism between the base change to `κ_A` of the special fibre `M_{κ_R}`
  and the special fibre of `M_A`. Both are base changes of `M` along the
  same composite map `Spec κ_A → Spec R`. The isomorphism is built from
  two Library comparisons `GroupScheme.Descent.pullbackComparison`.
  `specialFibreSquareIso_naturality` says that it is natural in `M`.
- `specialFibreCommSquareIso A C`: the same isomorphism for a commutative
  group scheme `C`, built from `GroupScheme.Descent.commPullbackComparison`.
  `groupHom_specialFibreCommSquareIso_hom` says that its underlying group
  homomorphism is `specialFibreSquareIso A C.toGrp`.
- `congr_specialFibreCommSquareIso_baseChange`: for a character `m` of `C`,
  `specialFibreCommSquareIso A C` carries the base change to `κ_A` of
  `m_{κ_R}` to the special character `(m_A)_{κ_A}` of the base change of `m`.
- `IntegralTorusData.baseChange_specialCharacterEquiv_apply` and
  `IntegralTorusData.baseChange_specialCharacterEquiv_symm_apply`: for a
  split integral torus `T` and an integral character `m` of `T.torus`, the
  special character of `m_A` (for `T.baseChange A L`) is the image under
  `specialFibreCommSquareIso A T.torus` of the `κ_A`-base change of the
  special character of `m`. The second lemma is the same identity for the
  inverse equivalence.

### Quotient data and reductive images

Let `φ : D' ⟶ D` be a morphism of relative component models, `Q` special-fibre
quotient data of `D` (a quotient `π : D_{κ_R} ⟶ Q.quotient` with a
radical) and `T` an integral torus of `D'`.

- `SpecialFibreQuotientData.baseChange A L Q`: quotient data of
  `D.baseChange A L`. Its radical and quotient are the base changes to
  `κ_A` of those of `Q`. Its projection is the inverse of
  `specialFibreSquareIso` followed by the base change of `π`. The simp
  lemmas `baseChange_quotient` and `baseChange_projection` record these
  fields.
- `specialFibreSquareIso_hom_comp_baseChange_quotientMap`: under
  `specialFibreSquareIso`, the map `(φ_A)_s ≫ π_A` of the base-changed data
  is the `κ_A`-base change of `φ_s ≫ π`.
- `groupHom_comp_baseChange_quotientTorusInclusion`: under
  `specialFibreCommSquareIso A T.torus`, the quotient torus inclusion of the
  base-changed data is the `κ_A`-base change of `φ.quotientTorusInclusion Q T`.
- `isSchemeTheoreticallyDominant_baseChange_reductiveImageProjection` and
  `isSchemeTheoreticallyDominant_squareIso_reductiveImageProjection`: the
  `κ_A`-base change of the projection onto the reductive image is
  schematically dominant, because a field extension is flat. The projection
  of the base-changed data, precomposed with `specialFibreSquareIso`, is
  schematically dominant. Both are used as local instances.
- `reductiveImageBaseChangeIso A L Q`: an isomorphism from the
  `κ_A`-base change of the reductive image `φ.reductiveImage Q` to the
  reductive image of the base-changed data. Both are closed subgroups of the
  base-changed quotient. The base-changed quotient map factors through each
  of them by a schematically dominant map. The isomorphism is the Library's
  `SchematicImage.isoOfDominantFactorizations`.
  `reductiveImageBaseChangeIso_hom_comp` says that it commutes with the
  inclusions into the base-changed quotient.
- `baseChange_reductiveImageTorusMap`: it carries the `κ_A`-base change of
  `φ.reductiveImageTorusMap Q T` (from the accepted module
  `FacetLieImageRoots`) to the torus map of the base-changed data, after
  `specialFibreCommSquareIso A T.torus`.

### Descent of the root form of the sign formula

`roots_reductiveImageTorusMap_of_baseChange`. Assume `Q.quotient` is locally
of finite type and `T.torus` is split. Write `φ_A`, `Q_A` and `T_A` for
`φ.baseChange A L`, `Q.baseChange A L` and `T.baseChange A L`. Let `σ` be a
real function on the characters of the base change of `T.torus` to `A`.
Suppose the base-changed data satisfy

`roots (φ_A.reductiveImageTorusMap Q_A T_A) = {χ ∈ roots (φ_A.quotientTorusInclusion Q_A T_A) | 0 ≤ σ(χ^int)}`,

where `χ^int` is the integral character of `T_A` whose special character is
`χ`. Then

`roots (φ.reductiveImageTorusMap Q T) = {χ ∈ roots (φ.quotientTorusInclusion Q T) | 0 ≤ σ((χ^int)_A)}`,

where `χ^int` is the integral character of `T` with special character `χ`
and `(χ^int)_A` is its base change to `A`. This is the form in which the
accepted module `FacetRootSignRestriction` states the sign formula
(`hasApartmentLieWeightSignFormula_iff_roots`).

## Proofs

`roots_eq_nonneg_of_residueBaseChange` compares membership of `χ`. By the
Library's `mem_roots_baseChange_iff`, `χ ∈ roots t` if and only if
`χ_{κ_A}` is a root of the base change of `t`; the same holds for `a`. By
`roots_mem_of_transport_iff`, transport along `e` and `f` (respectively `e`
and `g`) preserves roots. The hypothesis on `t'`, rewritten with
`hs χ`, gives the sign condition.

`RelativeComponentModelHom.baseChange` proves its component compatibility
by functoriality of base change and `φ.component_comm`.
`isSplitTorus_baseChange` is the Library's `IsSplitTorus.baseChange`.

`residueExtension_comp_residueBaseMap` reduces to `Spec.map` of a
composite of ring maps and holds by `congr`. `specialFibreSquareIso_naturality`
follows from `pullbackComparison_naturality` for both comparisons.
`congr_specialFibreCommSquareIso_baseChange` applies the Library's
`Descent.characterBaseChange_tower` to both comparisons and cancels.
`baseChange_specialCharacterEquiv_apply` is the symmetric form of that
lemma, since both special character maps are base changes of characters by
definition. The inverse form follows by `AddEquiv.symm_apply_apply`.

`specialFibreSquareIso_hom_comp_baseChange_quotientMap` unfolds the
base-changed data and uses naturality of `specialFibreSquareIso` for
`φ.neutral.hom`. `groupHom_comp_baseChange_quotientTorusInclusion` then uses
naturality for `T.inclusion`.

The first dominance lemma is the Library's
`isSchemeTheoreticallyDominant_baseChange` with flatness of
`Spec κ_A → Spec κ_R` (`fieldExtension_fpqc`). The second holds because an
isomorphism followed by a schematically dominant map is schematically
dominant. `reductiveImageBaseChangeIso` applies
`SchematicImage.isoOfDominantFactorizations` to these two factorizations.
The inclusions are closed immersions: the base-changed one by
`IsClosedSubgroup.baseChange`. The factorizations agree by
`SchematicImage.projection_inclusion` and the comparison of quotient maps.
`reductiveImageBaseChangeIso_hom_comp` is
`SchematicImage.isoOfDominantFactorizations_hom_comp`.
`baseChange_reductiveImageTorusMap` cancels the monomorphic inclusion of
the base-changed reductive image and uses
`reductiveImageTorusMap_comp_inclusion` on both sides.

`roots_reductiveImageTorusMap_of_baseChange` applies
`roots_eq_nonneg_of_residueBaseChange` with `T := T_{κ_R}`, `T' := (T_A)_{κ_A}`,
`e := specialFibreCommSquareIso A T.torus`, `f := reductiveImageBaseChangeIso`,
`g := 𝟙`, `s χ := σ((χ^int)_A)` and `s' χ := σ(χ^int)`. The compatibility for
`t` is `baseChange_reductiveImageTorusMap`, and the compatibility for `a` is
`groupHom_comp_baseChange_quotientTorusInclusion`. For the sign
compatibility, write `χ` as the special character of an integral character
`m`. Then `baseChange_specialCharacterEquiv_symm_apply` gives
`s' (e(χ_{κ_A})) = σ(m_A) = s χ`.

## Provenance

Internal infrastructure for the proof of
`Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement`
(Kaletha–Prasad, *Bruhat–Tits theory: a new approach*, Axiom 4.1.22(3)).
The descent argument proves the sign formula over the ring of integers of
the maximal unramified extension and descends it to the original ring of
integers. This module supplies the coefficient-change step. It uses only
Library definitions, the accepted modules `FacetLieImageRoots` and
`FacetRootSignRestriction`, and standard base-change functoriality. It makes
no assertion from the literature.
