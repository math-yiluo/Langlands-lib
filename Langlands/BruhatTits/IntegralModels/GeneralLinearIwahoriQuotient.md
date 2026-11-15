# The reductive quotient of the special fibre of the `GL_N` Iwahori model

Module `Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriQuotient`.

Let `F` be a nonarchimedean local field with valuation ring `𝒪 = 𝒪[F]` and
residue field `𝓀 = 𝓀[F]`. Let `Λ = iwahoriOrder F N` be the Iwahori order: the
matrices over `𝒪` whose strictly lower entries lie in the maximal ideal. The
published module `Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriModel`
defines its unit group scheme `iwahoriModel F N` and the model data
`iwahoriModelData F N`. That module shows that the integral points are the
standard Iwahori subgroup `I` (`iwahoriModel_integralPoints`).

This module constructs the special-fibre quotient data of `iwahoriModelData F N`
and proves that it is a reductive quotient. The radical is the kernel `1 + J` of
the reduction of `𝓀 ⊗ Λ` to its diagonal `𝓀^N`, and the quotient is the
diagonal split torus. The module then proves that the resulting positive subgroup
`G(F)^{0+}` is the subgroup `I^+` of the published comparison
(`generalLinearIwahoriPositivePoints`): the preimage in `GL_N(𝒪)` of the upper
unipotent group `U(𝓀)`. This is the non-hyperspecial regression example for the
depth-zero layer, next to the published hyperspecial example
`GeneralLinearDepthZero`, where the radical is trivial.

## Section units under algebra maps, isomorphisms and base change

Namespace `Langlands.GroupScheme.FiniteFreeAlgebraUnits`, for the published unit
group schemes `groupScheme b` of finite free `R`-algebras. The published
`sectionTensorEquiv : Γ(Spec R) ⊗[R] A ≃ₐ[R] A` and
`sectionUnitsEquiv b : rationalPoints (groupScheme b) ≃* Aˣ` identify sections
over `Spec R` with units of `A`.

- `sectionTensorEquiv_tmul` (`t ⊗ y ↦ t • y`, after the published identification
  of global sections) and `sectionTensorEquiv_map` (compatibility with `id ⊗ f`).
- `sectionUnitsEquiv_map`: the section units of `x ≫ map b b' f` (the unit-group
  map of an algebra map `f`, from the published module
  `Langlands.GroupScheme.FiniteFreeAlgebraUnitsQuotient`) are the images under
  `f`.
- `sectionUnitsEquiv_congrIso`: the same for the published `congrIso b b' e` of
  an algebra isomorphism `e`.
- `sectionUnitsEquiv_baseChange`: for `R → R'`, the section units of the base
  change `baseChangeSectionHom (WeilGm.baseMap R R') (groupScheme b) x`,
  transported by the published `baseChangeIso b R'`, are the images of those of
  `x` under `a ↦ 1 ⊗ a`. The proof follows the published
  `unitModel_integralPointMap`. It uses the published `baseChangeIso_hom_points`,
  `basePointsEquiv_apply`, `baseChangePointsEquiv_baseChangeSectionHom` and
  `pointsEquiv_naturality`, and `Scheme.ΓSpecIso_naturality` for the global
  sections.
- `baseChange_congr_map_eq_one_iff`: a section that is base changed,
  transported by `congrIso` along `e` and mapped by `map b₁ b' f` is trivial
  exactly when `f (e (1 ⊗ u)) = 1`, where `u` is the unit of the section.
- `orderModelData_integralPointMap_of_eq`: for the published order model data
  `orderModelData R K N φ b hinj hsurj`, the matrix of the generic point of an
  integral section is `φ u` for its unit `u`. This is the published
  `unitModel_integralPointMap` composed with `orderEquiv_tmul`. All data are
  implicit, so that they are read off from the goal. The Iwahori instance then
  reuses the published model terms unchanged. Stating it with explicit
  arguments makes the elaborator compare the published model with a freshly
  elaborated copy, which does not finish.

## The Iwahori order and its special fibre

Namespace `Langlands.BruhatTits.IntegralModels`.

- `residue_mul_diag` and `diagResidue : Λ →ₐ[𝒪] 𝓀^N`, which sends `M` to the
  residues of its diagonal entries. It is multiplicative because the strictly
  lower entries lie in the maximal ideal.
- `iwahoriUniformizer`, a chosen uniformizer of `𝒪`, from Mathlib's
  `IsDiscreteValuationRing.exists_irreducible`, with
  `iwahoriUniformizer_irreducible`. It is an auxiliary choice for the basis
  below, and any uniformizer works.
- `unitScale p` is `ϖ` strictly below the diagonal and `1` otherwise
  (`unitScale_ne_zero`).
  `iwahoriUnit p = unitScale p · E_p` is the scaled matrix unit, an element of
  `Λ`. `iwahoriUnit_coe`, `coe_sum_smul_iwahoriUnit`,
  `iwahoriUnit_linearIndependent` and `iwahoriUnit_span` show that these form
  a basis, `iwahoriUnitBasis`, with `iwahoriUnitBasis_apply` and
  `coe_apply_eq_repr_mul`.
- `iwahoriUnit_mul_coe` gives products of scaled matrix units.
  `lowerCount_eq_of_unitScale` and `isUnit_repr_iwahoriUnit_mul` show that if a
  coordinate of `iwahoriUnit p * iwahoriUnit q` is a unit, then the indices
  compose and the numbers of strictly lower positions add up.
- `offWeight (i, j) = (j - i) mod N` is the weight of an off-diagonal position,
  with `one_le_offWeight` and `offWeight_add` (additivity under composition,
  when the lower counts add up).
- `OffDiag`, `offCount` and `posEquiv : Fin N × Fin N ≃ Fin N ⊕ Fin (offCount N)`
  split positions into diagonal and off-diagonal ones, with `posEquiv_symm_inl`,
  `posEquiv_symm_inr` and `posEquiv_symm_inr_ne`.
- `iwahoriUnitBasisCat` (the same basis over `CommRingCat.of 𝒪`) and
  `specialBasis`, its base change to `𝓀`, reindexed by `posEquiv`. It is a basis
  of `SpecialAlgebra F N = 𝓀 ⊗[𝒪] Λ` with the diagonal units first.
  `specialBasis_apply` and `specialBasis_repr_mul` (structure constants are
  residues of those of `Λ`).
- `specialWeight`, `one_le_specialWeight` and `specialWeight_le`: the weights
  of the kernel basis vectors are at least `1` and adapted to their products.
- `specialDiag : 𝓀 ⊗ Λ →ₐ 𝓀^N` is the base change of `diagResidue`, with
  `specialDiag_one_tmul`, `diagResidue_iwahoriUnit`, `specialDiag_inl` (diagonal
  units go to the standard basis) and `specialDiag_inr` (off-diagonal units go to
  `0`).
- `iwahoriUnit_diag_mul`, `sum_iwahoriUnit_diag`, `specialSectionLinear` and
  `specialSection`: the diagonal section `v ↦ Σ v_i ⊗ E_ii` is an algebra map,
  and `specialDiag_comp_specialSection` shows that it is a section of
  `specialDiag`.

## The reductive quotient

- `diagBasis`, the standard basis of `𝓀^N`, with `specialDiag_basis_inl` and
  `specialWeight_le_of_structureConst`. These restate the facts above in the
  form used by `FiniteFreeAlgebraUnits.UnipotentPart` (module
  `Langlands.GroupScheme.FiniteFreeAlgebraUnipotentUnits`).
- `specialRadical_nilpotent`, from the published
  `isNilpotent_universalRadical_of_weights`.
- `specialRadical`, the unipotent kernel `1 + J` as a group scheme
  (`UnipotentPart.groupScheme`), and `diagTorus`, the unit group of `𝓀^N`.
  `specialRadicalInclusion` is the inclusion into the unit group of `𝓀 ⊗ Λ`, and
  `specialDiagMap` is the unit-group map of `specialDiag`.
- `specialRadical_isUnipotentRadical`: `specialRadicalInclusion` is the
  unipotent radical, and `specialDiagMap` is the fppf quotient by its range. It
  applies the published `UnipotentPart.isUnipotentRadical` with the weights, the
  section `specialSection` and the published `isTorus_pi`.
- `specialFibreIso : (iwahoriModelData F N).neutral.specialFibre ≅ groupScheme
  (flatBasis specialBasis)`. It composes the published `baseChangeIso`, along
  `Spec 𝓀 → Spec 𝒪` (the residue map, definitionally the model's
  `residueBaseMap`), with the published `congrIso` for the identity of
  `𝓀 ⊗ Λ`.
- `iwahoriQuotientData : SpecialFibreQuotientData (iwahoriModelData F N)`. The
  radical is `specialRadical` with inclusion
  `specialRadicalInclusion ≫ specialFibreIso.inv`. The quotient is `diagTorus`
  with projection `specialFibreIso.hom ≫ specialDiagMap`.
- `iwahoriQuotientData_isReductiveQuotient`: this data satisfies the Library's
  `IsReductiveQuotient`. The radical and fppf clauses are transported along
  `specialFibreIso`, as in the Library's
  `isReductiveQuotient_transportSpecialFibreIso`, using
  `IsUnipotentRadical.comp_iso`, `SubgroupFunctor.range_comp_iso` and
  `IsFppfQuotient.comapIso`. The quotient is connected reductive by the
  published `isSplitTorus_pi` and `IsSplitTorus.isConnectedReductive`.

## The positive subgroup is `I^+`

- `SpecialFibreQuotientData.mem_radicalPoints_iff`: for any reductive quotient
  `Q`, a special-fibre point lies in `Q.radicalPoints` exactly when its
  projection is trivial. This uses the kernel clause of `IsFppfQuotient` and the
  Library's `mem_range_kernelι_iff`.
- `sectionUnit F N x`, the unit of `Λ` attached to an integral section `x`
  (published `sectionUnitsEquiv`).
- `reduction_projection_eq_one_iff`: the reduction of `x` has trivial
  projection exactly when every diagonal entry of `sectionUnit F N x` is `1`
  modulo the maximal ideal. It applies `baseChange_congr_map_eq_one_iff` and
  `specialDiag_one_tmul`.
- `iwahoriIntegralPointMap_matrix`: the matrix of the generic point of `x` is
  `sectionUnit F N x` with entries mapped to `F`. It applies
  `orderModelData_integralPointMap_of_eq` and the published
  `iwahoriInclusion_apply`.
- `iwahoriQuotientData_positivePoints`: `(iwahoriQuotientData F N).positivePoints
  = generalLinearIwahoriPositivePoints F N`. For the inclusion `⊆`, the unit of
  `x` is an invertible integral matrix with strictly lower entries in the
  maximal ideal and diagonal entries congruent to `1`. For `⊇`, a point of `I^+`
  lies in `I`, the integral points (published `iwahoriModel_integralPoints`).
  Its integral section has the given matrix as unit, by injectivity of
  `𝒪 → F`, so its diagonal residues are `1`.

## Provenance

This module computes a regression example and formalizes no external statement.
The Iwahori subgroup `I`, the subgroup `I^+` and the comparison with the
hyperspecial pair are those of the published
`Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriComparison`, and the
model is that of the published `GeneralLinearIwahoriModel`. The values computed
here are the ones expected from Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023): for the Iwahori subgroup of `GL_N`, the reductive quotient of
the special fibre is the diagonal torus, and `G(F)^{0+}` is the pro-unipotent
radical `I^+`. Here they are computed from the Library's definitions
(`SpecialFibreQuotientData`, `IsReductiveQuotient`, `positivePoints`), not
assumed. No external code is adapted.

## Not claimed

Nothing here identifies `iwahoriModelData F N` with a KP parahoric model
attached to a facet of a building, and no building is used. Uniqueness of
reductive quotients is not proved, so this is one specified quotient datum. The
radical points are not computed beyond membership through the projection, and
the quotient of `I` by `I^+` is not re-derived here. It is in the published
comparison.
