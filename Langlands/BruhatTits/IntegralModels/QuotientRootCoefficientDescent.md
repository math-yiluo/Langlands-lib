# Descent of a single reductive-quotient root along a coefficient change

Module `Langlands.BruhatTits.IntegralModels.QuotientRootCoefficientDescent`.

Author: Worker 99.

## Setting

The setting is that of the published `FacetRootSignBaseChange`, at arbitrary
universe `u`:

- `R` and `A` are domains with fraction fields `K` and `L`;
- the maps `R → A`, `R → K`, `A → L`, `K → L` and `R → L` commute
  (`IsScalarTower R A L`, `IsScalarTower R K L`);
- `G` is a group scheme over `K`.

`D.baseChange A L` is the Library's coefficient change of relative-component
model data. `T.baseChange A L`, `T.baseChangeInclusion A L` and
`Q.baseChange A L` are the coefficient changes of an integral torus, its
inclusion and special-fibre quotient data (`FacetRootSignBaseChange`).

The published `UnramifiedFacetSignDescent` handles the same comparison only
after a transport of the base-changed model along a generic isomorphism. This
module gives the untransported version and descends one root instead of a sign
formula.

## Generic factorization (no transport)

Let `𝒯 : IntegralTorusData D' S₀ i₀`, let `T' : IntegralTorusData (D'.baseChange A L) S' i'`,
and let `f : (S₀)_L ⟶ S'` be a generic group homomorphism.

- `baseChangeComparisonGenericMap A L 𝒯 T' f` is the generic map from the
  generic fibre of the base change of `𝒯.torus` to the generic fibre of
  `T'.torus`. It composes the coefficient-square comparison
  `Descent.squareComparison`, the base change of `𝒯.genericIso`, `f`, and
  `T'.genericIso.inv`.
- `baseChangeComparisonGenericMap_comp_inclusion`. If
  `f ≫ i' = (i₀)_L`, the comparison map followed by the generic fibre of
  `T'.inclusion` is the generic fibre of `𝒯.baseChangeInclusion A L`.
- `baseChange_genericCharacter_eq_of_baseChangeComparisonGenericMap`. Let
  `ρ : (𝒯.torus)_A ⟶ T'.torus` have generic fibre the comparison map, and let
  the base change of an integral character `m` of `𝒯.torus` be `ρ ≫ ψ`. Then
  the base change to `L` of `𝒯.genericCharacter m` is
  `f ≫ T'.genericCharacter ψ`.
- `exists_torusHom_of_baseChange`. Assume `A` is a Henselian discrete
  valuation ring with separably closed residue field, `𝒯.torus` is split, and
  `A' : IntegralSplitTorusData (D'.baseChange A L).neutral i''` has closed
  inclusion, with `f ≫ i'' = (i₀)_L`. Then there is
  `ρ : (𝒯.torus)_A ⟶ A'.torus` with `ρ ≫ A'.inclusion = 𝒯.baseChangeInclusion A L`
  and generic fibre the comparison map for `A'.toIntegralTorusData`.

The first three are the untransported forms of `comparisonGenericMap`,
`comparisonGenericMap_comp_inclusion` and
`baseChange_genericCharacter_eq_of_comparisonGenericMap` in
`UnramifiedFacetSignDescent`. Their proofs are those proofs with the
transport factor removed. The fourth applies the published
`exists_torusHom_of_generic_factor` (`FacetRootSignDescent`) to the neutral
model of `D'.baseChange A L`.

## Residue level

Assume in addition that `R` and `A` are local and `R → A` is local. Write
`resExt` for the residue-field extension.

- `IntegralTorusData.groupHom_specialFibreCommSquareIso_comp_baseChange_quotient`.
  Under `specialFibreCommSquareIso A T.torus`, the base-changed torus followed
  by the base-changed quotient projection is the `resExt`-base change of
  `T.specialFibreInclusion ≫ Q.projection`. The proof is naturality of
  `specialFibreSquareIso` and cancellation of the square isomorphism.
- `IntegralTorusData.specialCharacter_mem_roots_of_baseChange`. Let `T` be a
  split integral torus of `D`, and let `Q` have a quotient locally of finite
  type. Let `T'` be a split integral torus of `D.baseChange A L`, and let
  `ρ : (T.torus)_A ⟶ T'.torus` satisfy `ρ ≫ T'.inclusion = T.baseChangeInclusion A L`.
  Let `m` be a nonzero integral character of `T.torus` with base change
  `ρ ≫ ψ`. If the special character of `ψ` is a root of
  `T'.specialFibreInclusion ≫ (Q.baseChange A L).projection`, then the special
  character of `m` is a root of `T.specialFibreInclusion ≫ Q.projection`.

The proof of the last statement has four steps.

1. The special fibre of `ρ` factors the special-fibre inclusion of
   `T.baseChange A L` through that of `T'`. It also carries the special
   character of `ψ` to the special character of the base change of `m`
   (`characterLattice.baseChange_precomp`).
2. That character is nonzero, because `m ≠ 0` and both character maps are
   equivalences for split tori. The published `mem_roots_comp_iff` (roots of a
   restricted split-torus action are the nonzero restrictions of roots) makes
   it a root of the base-changed torus in the base-changed quotient.
3. `IntegralTorusData.baseChange_specialCharacterEquiv_apply` rewrites this
   character as the `resExt`-base change of the special character of `m`,
   transported by `specialFibreCommSquareIso`.
4. `roots_mem_of_transport_iff` with the compatibility lemma above, and then
   `mem_roots_baseChange_iff`, descend the root along the residue-field
   extension.

## Provenance

This is internal infrastructure, composed from the named Library results. It
is the coefficient-change step of the residue-root descent in the proof of
`UnramifiedFixedResidueRootModelStatement`, as in the converse half of the
proof of Kaletha–Prasad Proposition 9.4.28. The source is Kaletha and Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. No assertion from the
literature is made here.
