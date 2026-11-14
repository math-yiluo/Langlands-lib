# Unit group schemes of orders, and an Iwahori model of `GL_N`

This module turns the unit group scheme of an order in `M_N(K)` into an
integral model of `GL_N` and computes its integral points. It then applies
this to the standard Iwahori order over the valuation ring `𝒪[F]` of a
nonarchimedean local field `F`. The result is a smooth affine model of
`GL_N` over `𝒪[F]` with geometrically connected fibres whose integral points
are the published standard Iwahori subgroup `I` (`generalLinearIwahoriPoints`).
Packaged as relative-component model data, it gives a model-level
non-hyperspecial counterpart of the standard model `GL_{N,𝒪[F]}`: for
`N ≥ 2` its neutral points form a proper subgroup of those of the published
`generalLinearModelData`.

## Provenance

The module is derived. The constructions are standard: an order `A` in
`M_N(K)` that is free over `R` has a unit group scheme, and its generic fibre is
`GL_N` because `K ⊗_R A ≅ M_N(K)`. The Lean proofs are written here from Mathlib
and the Library; no external code is adapted. The integral-point computation
follows the published `WeilGm.rationalUnitsEquiv_integralPointMap`
(`Langlands.GroupScheme.Torus.WeilRestrictionIntegralModel`), which does the
same computation for commutative algebras and Weil restrictions of `G_m`.

The module contributes to the task objective's comparison of a hyperspecial
with a non-hyperspecial parahoric (Task 3557). The published
`Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriComparison` compares
the groups `I ⊆ GL_N(𝒪[F])`. This module adds a group scheme over `𝒪[F]` whose
integral points are `I`, in the Library's `IntegralModel` and
`RelativeComponentModelData` interfaces. The comparison values come from
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`
(SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`):

- Example 4.2.16 (printed p. 174 / PDF p. 205): the standard Iwahori subgroup
  is the preimage of the upper triangular Borel subgroup under reduction. The
  published `generalLinearIwahoriPoints` is this construction for `GL_N`, and
  `iwahoriModel_integralPoints` identifies it with the integral points of the
  model built here.
- §15.1.33 (printed p. 524 / PDF p. 555): for `G = GL(X)` and a periodic lattice
  chain with facet `F`, `G(k)^0_F = G(k)^0_x = G(k)^1_x = G(k)^†_x`, and this
  group is the subgroup stabilizing each lattice of the chain. These
  equalities are consistent with `iwahoriModelData` taking the same model as
  full and neutral model. The Iwahori order of this module consists of the integral matrices
  whose strictly lower entries lie in the maximal ideal. It is not proved here
  to be the stabilizer order of the standard lattice chain.

The authors' corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`) do not
amend Example 4.2.16 or Chapter 15.

## Setting

The module imports the published `Langlands.GroupScheme.FiniteFreeAlgebraUnits`
(the unit group scheme `groupScheme b` of a finite free algebra over a
`CommRingCat`, its point equivalences, `baseChangeIso`, `congrIso`,
`generalLinearIso`, smoothness and geometric connectedness),
`Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriComparison`
(`generalLinearIwahoriPoints`, `glResidueMap`, `generalLinearModelData`),
`Langlands.BruhatTits.IntegralModels.RelativeComponentConstruction`
(`isRelativeIdentityComponent_id_of_geometricallyConnected`),
`Langlands.GroupScheme.IntegralModel.SplitIntegralPoints`
(`baseChangePointsEquiv_baseChangeSectionHom`) and
`Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints`
(`GeneralLinear.rationalPointsEquiv`, the matrix of a rational point of
`GL_N`). From Mathlib it imports `Mathlib.RingTheory.Localization.BaseChange`
and `Mathlib.RingTheory.Localization.Integer`.

All rings are in one universe `u`. In the general part, `R` is a domain with
fraction field `K`, `A` is an `R`-algebra (`Ring A`, possibly noncommutative)
and `b : Module.Basis (Fin n) (CommRingCat.of R) A`.

## Declarations

### Namespace `Langlands.GroupScheme.FiniteFreeAlgebraUnits`: the unit model

Let `e : K ⊗[R] A ≃ₐ[K] Matrix (Fin N) (Fin N) K`.

- `unitGenericIso₁`, `unitGenericIso₂`, `unitGenericIso`: the identification of
  the generic fibre of `groupScheme b` with `GeneralLinear.groupScheme (Fin N)`
  over `K`. It is the composite of the published `baseChangeIso`, `congrIso`
  for `e`, and `generalLinearIso`.
- `unitModel R K b N e`: the `IntegralModel R K` of `GL_N` with group
  `groupScheme b` and this generic identification. `unitModel_isSmooth`: it is
  smooth.
- `unitModel_integralPointMap`: for an integral section `x`, the matrix of the
  generic point of `x` is `e (1 ⊗ u)`, where `u = sectionUnitsEquiv b x ∈ Aˣ`.
- `mem_unitModel_integralPoints`: a rational point `g` of `GL_N` is an integral
  point exactly when its matrix is `e (1 ⊗ u)` for some `u : Aˣ`.
- `unitModelData`: the `RelativeComponentModelData R K` whose full and neutral
  models are both `unitModel`, with the identity inclusion. Its fields are
  smoothness (`unitModel_isSmooth`), connected fibres (from the published
  geometric connectedness of `groupScheme b`) and
  `isRelativeIdentityComponent_id_of_geometricallyConnected`.
  `unitModelData_neutralPoints`: its neutral points are the integral points of
  `unitModel`.

### Namespace `Langlands.GroupScheme.FiniteFreeAlgebraUnits`: orders

Let `φ : A →ₐ[R] Matrix (Fin N) (Fin N) K` be injective (`hinj`), with every
`M` satisfying `c • M = φ a` for some `a : A` and nonzero `c ∈ R`
(`hsurj`). This is what "`A` is an `R`-order in `M_N(K)`" means here.

- `isLocalizedModule_of_order`: `φ` is a localization of `R`-modules at the
  nonzero elements of `R`.
- `orderEquiv R K N φ hinj hsurj : K ⊗[R] A ≃ₐ[K] M_N(K)`, sending `k ⊗ a` to
  `k • φ a` (`orderEquiv_tmul`). It is Mathlib's `AlgHom.liftEquiv` of `φ`,
  which is bijective by `IsLocalizedModule.isBaseChange`.
- `orderModel R K N φ b hinj hsurj`: `unitModel` for `orderEquiv`.
- `mem_orderModel_integralPoints`: `g` is an integral point exactly when its
  matrix is `φ u` for some `u : Aˣ`.
- `orderModelData` and `orderModelData_neutralPoints`: the corresponding
  relative-component model data and its neutral points.

### Namespace `Langlands.BruhatTits.IntegralModels`: the Iwahori order

Let `F` be a nonarchimedean local field and `N : ℕ`.

- `iwahoriOrder F N : Subalgebra 𝒪[F] (Matrix (Fin N) (Fin N) 𝒪[F])`: the
  matrices `M` with `M i j` in the maximal ideal whenever `j < i`
  (`mem_iwahoriOrder`). It is closed under multiplication because in each term
  `M i k * M' k j` with `j < i`, either `k < i` or `j < k`.
- Instances `iwahoriOrder_finite`, `iwahoriOrder_free`: it is finite and free
  over `𝒪[F]` (a submodule of a finite free module over a principal ideal
  domain).
- `iwahoriBasis F N`: Mathlib's `Module.finBasis` of the Iwahori order, as a
  basis over `CommRingCat.of 𝒪[F]`. It is a chosen basis; by the published
  `congrIso`, the unit group scheme does not depend on it up to isomorphism.
- `iwahoriInclusion F N`: the `𝒪[F]`-algebra map to `M_N(F)` (`iwahoriInclusion_apply`:
  entrywise `algebraMap`). `iwahoriInclusion_injective`, and
  `iwahoriInclusion_spans`: every `M : M_N(F)` satisfies `c • M = ι a` with
  `c = ϖ b₀ ≠ 0`, where `b₀` clears the denominators of the entries
  (`IsLocalization.exist_integer_multiples_of_finite`) and `ϖ` is an
  irreducible element (`IsDiscreteValuationRing.exists_irreducible`).
- `iwahoriModel F N` (definition, the declared definition of this unit): the
  `IntegralModel 𝒪[F] F` of `GL_N` given by `orderModel` for the Iwahori order.
  `iwahoriModel_isSmooth`: it is smooth.
- `inv_mem_iwahoriOrder`: if `v : GL_N(𝒪[F])` lies in the Iwahori order, so does
  `v⁻¹`. Reduction of `v` is upper triangular, upper triangular matrices form
  the subgroup `(singletons N).parabolic 𝓀[F]`, and reduction is a group
  homomorphism.
- `iwahoriModel_integralPoints`:
  `(iwahoriModel F N).integralPoints = generalLinearIwahoriPoints F N`.
- `iwahoriModelData F N`: the relative-component model data `orderModelData`
  of the Iwahori order (full model = neutral model = `iwahoriModel F N`).
- `iwahoriModelData_neutralPoints`: its neutral points are
  `generalLinearIwahoriPoints F N`.
- `iwahoriModelData_neutralPoints_lt`: for `2 ≤ N`,
  `(iwahoriModelData F N).neutralPoints < (generalLinearModelData F N).neutralPoints`.
- `iwahoriModelData_neutralPoints_of_le_one`: for `N ≤ 1` the two are equal.

## Proof outline

**Integral points of the unit model.** An integral section `x` of
`groupScheme b` is restricted to the generic fibre and then pushed through the
three steps of `unitGenericIso`. On points, the published point lemmas
`generalLinearIso_hom_points`, `congrIso_hom_points`, `baseChangeIso_hom_points`
and `basePointsEquiv_apply`, together with
`baseChangePointsEquiv_baseChangeSectionHom` and `pointsEquiv_naturality`,
express the matrix of the generic point as the image of the unit
`pointsEquiv b x` of `Γ(Spec R) ⊗[R] A` under one additive map. That map is
the composite of the pullback of sections, `baseChangeTensorEquiv`,
`id ⊗ e`, the inverse of `matrixEquivTensor` and `Γ(Spec K) ≅ K` entrywise.
Tensor induction compares it with `z ↦ e (1 ⊗ sectionTensorEquiv z)`. On
`s ⊗ c` both sides are `r • e (1 ⊗ c)`, with `r` the image of `s` in `K`.
This uses the naturality of `Scheme.ΓSpecIso` and the fact that
`WeilGm.selfSectionsAlgEquiv` is an algebra map.

**Orders.** The three conditions of `IsLocalizedModule` are: nonzero elements
of `R` act invertibly on the `K`-vector space `M_N(K)`; `hsurj`; and
injectivity of `φ`. Mathlib's `IsLocalizedModule.isBaseChange` then makes
`k ⊗ a ↦ k • φ a` bijective. This is the underlying map of
`AlgHom.liftEquiv`, so it is an algebra isomorphism.

**The Iwahori points.** By `mem_orderModel_integralPoints` and the published
`mem_generalLinearIwahoriPoints`, the theorem says that the images of units
of the Iwahori order in `GL_N(F)` are the images of the invertible integral
matrices whose strictly lower entries lie in the maximal ideal. A unit of the
order gives such a matrix. Conversely such a matrix `v` lies in the order, and
by `inv_mem_iwahoriOrder` so does `v⁻¹`; together they form a unit of the
order with the same image.

**Model data.** The neutral points of `unitModelData` are the integral points
of `unitModel` by the published `RelativeComponentModelData.neutralPoints_eq`.
The comparison with `generalLinearModelData` is the published
`generalLinearIwahoriPoints_lt_integralPoints` (for `N ≥ 2`) and
`generalLinearIwahoriPoints_of_le_one`, rewritten with `neutralPoints_eq` on
both sides.

## Non-claims

- The module does not identify `iwahoriModel F N` with KP's parahoric group
  scheme of the standard chamber, with a Bruhat–Tits group scheme, or with the
  stabilizer of a lattice chain. It does not compute points over unramified
  extensions of `F`.
- It does not construct special-fibre quotient data (`SpecialFibreQuotientData`)
  for the Iwahori model, its unipotent radical or its maximal reductive
  quotient. It does not prove that the special fibre is not reductive.
- The Iwahori order is defined by entry conditions in the standard basis. It is
  not shown to be hereditary or to be the endomorphism order of a lattice
  chain.
- `iwahoriBasis` is a chosen basis, not the explicit basis
  `ϖ^[i > j] E_ij`.
