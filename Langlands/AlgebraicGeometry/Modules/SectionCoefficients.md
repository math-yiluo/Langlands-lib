# Coefficients of sections against a trivializing section

This module proves lemmas about a global section `s` of a module sheaf `M` on a
scheme `X`, over opens inside the whole generation open
`Langlands.SchemeModule.trivializationOpen M s`. On such an open, every section of
`M` is a unique multiple of the restriction of `s`. The module also computes the
basic open of the coefficient of a second global section `t` against `s`. All
declarations are in namespace `Langlands.SchemeModule`. They hold for every
scheme and every module sheaf (no line-bundle, quasi-coherence or finiteness
hypothesis), and they allow zero sections.

## Declarations

- `sectionRes M s V` is the restriction of the global section `s` to the open
  `V`, that is, `M.presheaf.map (homOfLE (V ≤ ⊤)).op s`.
- `sectionRes_res`: restricting `sectionRes M s U` to `V ≤ U` gives
  `sectionRes M s V`.
- The imported `LineBundleDescent.sectionHom_app`: for `a : Γ(X, V)`,
  `(sectionHom M s).app V a = a • sectionRes M s V`. The published
  `sectionHom_app_one` gives the value at `1`, and linearity of
  `(sectionHom M s).app V` over `Γ(X, V)` gives the rest.
- `bijective_sectionHom_app_of_le`: if `V ≤ trivializationOpen M s`, then
  `(sectionHom M s).app V` is bijective. The published
  `maximalTrivialization` shows that `s` trivializes `M` on the whole
  generation open `T`. So the restricted morphism is an isomorphism, and by
  `Scheme.Modules.Hom.isIso_iff_isIso_app` so is each of its components. The
  component at `T.ι ⁻¹ᵁ V` is `(sectionHom M s).app (T.ι ''ᵁ (T.ι ⁻¹ᵁ V))`, and
  `T.ι ''ᵁ (T.ι ⁻¹ᵁ V) = V` because `V ≤ T`.
- `le_trivializationOpen_of_bijective`: conversely, if
  `(sectionHom M s).app V` is bijective for every `V ≤ B`, then
  `B ≤ trivializationOpen M s`. Each component of the restriction to `B` is
  such a map, so the restriction is an isomorphism, and `maximalTrivialization`
  gives the inclusion.
- `smul_sectionRes_injective`: on `V ≤ trivializationOpen M s`,
  `a • sectionRes M s V = b • sectionRes M s V` implies `a = b`.
- `exists_smul_sectionRes_eq`: on `V ≤ trivializationOpen M s`, every
  `σ : Γ(M, V)` equals `a • sectionRes M s V` for some `a : Γ(X, V)`.
- `smul_sectionRes_res`: a relation `c • sectionRes M s U = sectionRes M t U`
  restricts to every `V ≤ U`, with `c` replaced by its restriction. The proof
  uses `Scheme.Modules.map_smul`.
- `coeff_mul`: on `V ≤ trivializationOpen M s`, if `t = a s`, `r = b t` and
  `r = c s` (restricted sections), then `c = b * a`.
- `basicOpen_coeff_eq`: let `U ≤ trivializationOpen M s` and
  `c • sectionRes M s U = sectionRes M t U`. Then
  `X.basicOpen c = U ⊓ trivializationOpen M t`.

## Proof of `basicOpen_coeff_eq`

The inclusion `≤`: the basic open `B` of `c` lies in `U`. Let `V ≤ B`. The
restriction `cV` of `c` to `V` is a unit (`RingedSpace.isUnit_res_basicOpen`,
restricted further), say `cV = u`. Then
`(sectionHom M t).app V a = (sectionHom M s).app V (a * u)` for all `a`, by
`LineBundleDescent.sectionHom_app` and the restricted relation. So
`(sectionHom M t).app V` is the bijection `(sectionHom M s).app V` composed with
multiplication by the unit `u`, and is bijective. By
`le_trivializationOpen_of_bijective`, `B ≤ trivializationOpen M t`.

The inclusion `≥`: let `V = U ⊓ trivializationOpen M t`. Since `V` lies in the
generation open of `t`, `exists_smul_sectionRes_eq` gives `d` with
`d • sectionRes M t V = sectionRes M s V`. Then
`(d * cV) • sectionRes M s V = sectionRes M s V`, and uniqueness of coefficients
(`smul_sectionRes_injective`, using `V ≤ U ≤ trivializationOpen M s`) gives
`d * cV = 1`. So `cV` is a unit, its basic open is all of `V`
(`X.basicOpen_of_isUnit`), and `Scheme.basicOpen_res` rewrites that basic open
as `V ⊓ X.basicOpen c`. Hence `V ≤ X.basicOpen c`.

## Provenance

These are standard facts about an invertible module trivialized by a section,
used in the proof of Stacks Project Lemma 31.18.3 (tag 0BCX, registered source
`stacks-norms-field-ample-descent-2026-10-26`): where `s` trivializes the
module, another section `t` is `f s` for a unique function `f`, and `t` is
nonvanishing exactly where `f` is invertible. Here the source's nonvanishing
locus is represented by the Library's maximal trivialization open
`trivializationOpen`, and "invertible" by Mathlib's `basicOpen`. The lemmas are
internal to the proof of
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionAmpleExistenceDescentStatement`;
the source does not state them separately.
