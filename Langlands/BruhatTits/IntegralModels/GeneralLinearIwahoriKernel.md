# The special-fibre kernel from the `GL_N` Iwahori model to the hyperspecial model

Module `Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriKernel`.

Let `F` be a nonarchimedean local field with valuation ring `𝒪 = 𝒪[F]`, residue
field `𝓀 = 𝓀[F]` and a chosen uniformizer `ϖ` (the published
`iwahoriUniformizer`). Let `Λ = iwahoriOrder F N` be the Iwahori order: the
matrices over `𝒪` whose strictly lower entries lie in the maximal ideal. The
published module `GeneralLinearIwahoriModel` defines its unit group scheme
`iwahoriModel F N`, and its integral points are the standard Iwahori subgroup.

This module defines the hyperspecial model `matrixOrderModel F N`, the unit
group scheme of the order `M_N(𝒪)`. The inclusion `Λ ⊆ M_N(𝒪)` then gives a
homomorphism of integral models `iwahoriMatrixHom F N` that extends the identity
of `GL_N`. The main result, `iwahoriMatrixHom_specialFibreKernel_properties`,
says that the kernel of its special-fibre map is smooth, connected and
unipotent. This is the `GL_N` instance, for the standard alcove and its
hyperspecial vertex, of the smooth-connected-unipotent assertion of
Kaletha–Prasad, Proposition 8.4.15 and Theorem 8.4.19(1). The root-group
product decompositions in those results are not formalized; see the comparison
section below for a misprinted index in Theorem 8.4.19(1). The kernel is identified
(`specialFibreKernelIso`) with the unipotent group `1 + J_-`, where `J_-` is
spanned by the classes of the scaled matrix units `ϖ E_ij` with `i > j` in
`𝓀 ⊗[𝒪] Λ`.

## Unit-group maps

Namespace `Langlands.GroupScheme.FiniteFreeAlgebraUnits`. Here `groupScheme b`
is the published unit group scheme of a finite free `R`-algebra `A` with basis
`b`, and `map b b' f` is the published unit-group map of an algebra map
`f : A → A'` (module `FiniteFreeAlgebraUnitsQuotient`).

- `congrIso_hom_eq_map`: the published `congrIso b b' e` of an algebra
  isomorphism `e` has underlying map `map b b' e`. Both have the same effect on
  points.
- `mono_map`: if `f` has an `R`-linear retraction `r` (`r (f a) = a`), then
  `map b b' f` is a monomorphism. On `T`-points, `id ⊗ r` is a retraction of
  `id ⊗ f`, so the induced map of unit groups is injective.
- `baseChangeTensorEquiv_map` and `baseChange_map_comp_baseChangeIso`: the
  published base-change identification `baseChangeIso` is natural in the
  algebra. Base change along `R → R'` of `map b b' f`, followed by
  `baseChangeIso b' R'`, equals `baseChangeIso b R'` followed by the unit map of
  `id ⊗ f : R' ⊗ A → R' ⊗ A'`. The proof compares points through the published
  `baseChangeIso_hom_points`, `basePointsEquiv_apply`,
  `baseChangePointsEquiv_comp` and `pointsEquiv_map`.
- `unitModel_algHom_comp` and `unitModelHom`. Take two published unit models
  `unitModel R K b N e` and `unitModel R K b' N e'`, with generic
  identifications `e`, `e'` with `M_N(K)`. Let `f` be an algebra map with
  `e' (1 ⊗ f a) = e (1 ⊗ a)`. Then `map b b' f` is a homomorphism of integral
  models (the published `IntegralModel.Hom`) over the identity of `GL_N`. Its
  generic compatibility follows from `baseChange_map_comp_baseChangeIso`,
  `congrIso_hom_eq_map` and the published `map_comp`.

## The hyperspecial model and the homomorphism

Namespace `Langlands.BruhatTits.IntegralModels`.

- `matrixInclusion : M_N(𝒪) → M_N(F)`, with `matrixInclusion_injective` and
  `matrixInclusion_spans`: for every matrix `M` over `F`, some nonzero `c ∈ 𝒪`
  has `c • M` in the image. This follows from the published
  `iwahoriInclusion_spans`, since `Λ ⊆ M_N(𝒪)`.
- `matrixOrderModel F N`: the published `orderModel` of `M_N(𝒪)` with the
  published `matrixBasis`.
- `iwahoriMatrixHom F N : (iwahoriModel F N).Hom (matrixOrderModel F N) (𝟙 _)`,
  given by `unitModelHom` for the inclusion `Λ → M_N(𝒪)`. `iwahoriMatrixHom_hom`
  records that its map is `map (iwahoriBasis F N) (matrixBasis 𝒪 N) Λ.val`.

## The upper triangular reduction

- `UpperPosition`, `StrictLowerPosition`, their cardinalities `upperCount` and
  `strictLowerCount`, and `upperLowerEquiv`, which splits `Fin N × Fin N` into
  positions on or above the diagonal and strictly below it
  (`upperLowerEquiv_symm_inl`, `upperLowerEquiv_symm_inr`).
- `specialMatrixEquiv : 𝓀 ⊗[𝒪] M_N(𝒪) ≃ M_N(𝓀)` (Mathlib's
  `matrixEquivTensor`), with `specialMatrixEquiv_one_tmul` (reduction of
  entries).
- `specialInclusion : 𝓀 ⊗ Λ → 𝓀 ⊗ M_N(𝒪)`, the base change of the inclusion.
- `upperTriangular`: the upper triangular matrices over `𝓀`, as Mathlib's
  `Matrix.blockTriangularSubalgebra` for the identity of `Fin N`.
- `specialMatrix_mem_upperTriangular`: the image of `𝓀 ⊗ Λ` in `M_N(𝓀)` is upper
  triangular, because strictly lower entries of `Λ` reduce to `0`. Hence
  `specialUpper : 𝓀 ⊗ Λ → upperTriangular`, and with
  `upperInclusion : upperTriangular → 𝓀 ⊗ M_N(𝒪)` we have
  `upperInclusion_comp_specialUpper` (the composite is `specialInclusion`).
- `upperPart` (keep the entries on or above the diagonal),
  `upperRetraction = upperPart ∘ specialMatrixEquiv`, and
  `upperRetraction_upperInclusion`: a linear retraction of `upperInclusion`.

## Adapted bases and the unipotent kernel

- `kernelBasis`: the base change to `𝓀` of the published scaled matrix-unit
  basis `iwahoriUnitBasisCat` of `Λ`, reindexed by `upperLowerEquiv`, so that
  positions on or above the diagonal come first. `kernelBasis_apply` and
  `kernelBasis_repr_mul` (structure constants are residues of those of `Λ`).
- `upperCoords` (entries on or above the diagonal, a linear equivalence),
  `upperBasis` (matrix units of `upperTriangular`), `upperCoords_symm_apply_val`
  and `upperBasis_apply_val`.
- `specialUpper_one_tmul_val`, `specialUpper_kernelBasis`,
  `residue_iwahoriUniformizer` (`ϖ` reduces to `0`), and
  `specialUpper_kernelBasis_inl` and `specialUpper_kernelBasis_inr`.
  `specialUpper` sends the basis vectors on or above the diagonal to the matrix
  units of `upperBasis`, and the strictly lower ones (`ϖ E_ij`, `i > j`) to `0`.
- `kernelBasis_structureConst`: the structure constants of `𝓀 ⊗ Λ` among
  strictly lower basis vectors vanish. If such a coordinate were nonzero, it
  would be a unit coordinate of a product of two strictly lower scaled units at
  a strictly lower position. The published `isUnit_repr_iwahoriUnit_mul` then
  forces the strictly lower counts to satisfy `1 + 1 = 1`.
- `kernelRadical_nilpotent`, from the published
  `UnipotentPart.isNilpotent_universalRadical_of_weights` with all weights `1`.
- `strictLowerKernel`: the published `UnipotentPart.groupScheme` for
  `specialUpper` and these bases. Its `S`-points are the units of `S ⊗ (𝓀 ⊗ Λ)`
  mapping to `1`, namely `1 + S ⊗ J_-`.
- `strictLowerKernel_properties`: it is smooth, connected and unipotent, by the
  published `UnipotentPart.smooth`, `UnipotentPart.connectedSpace` and
  `UnipotentPart.isUnipotent`.

## The special-fibre kernel

- `specialMatrixBasis`: the base change to `𝓀` of `matrixBasis 𝒪 N`.
- `kernelFibreIso : (iwahoriModel F N).specialFibre ≅ groupScheme (flatBasis
  kernelBasis)`. It is the published `baseChangeIso` followed by the published
  `congrIso` for the identity of `𝓀 ⊗ Λ`, as for the published
  `specialFibreIso`. The base change is along the residue map `Spec 𝓀 → Spec 𝒪`,
  which is definitionally the model's `residueBaseMap`.
- `matrixFibreIso : (matrixOrderModel F N).specialFibre ≅ groupScheme
  specialMatrixBasis`, the published `baseChangeIso`.
- `kernelFibreMap`: the unit map of `specialUpper` (the published
  `UnipotentPart.unitMap`) followed by the unit map of `upperInclusion`.
- `kernelFibre_square_aux` and `kernelFibre_square`: under these
  identifications, `kernelFibreMap` is the special-fibre map of
  `iwahoriMatrixHom`. The proof rewrites with `baseChange_map_comp_baseChangeIso`,
  `map_comp`, `upperInclusion_comp_specialUpper` and `congrIso_hom_eq_map`. The
  auxiliary statement writes both sides with the explicit base-change objects
  and the association of `kernelFibreIso`. The main statement then holds
  definitionally.
- `specialFibreKernelIso : kernel (iwahoriMatrixHom F N).specialFibreMap ≅
  strictLowerKernel F N`. It composes three Library isomorphisms:
  `kernelSquareIso` for the square above; `kernelPostcompIso`, which removes
  the monomorphism `map upperBasis specialMatrixBasis upperInclusion`
  (`mono_map` with `upperRetraction`); and the inverse of
  `UnipotentPart.kernelIso`, which identifies `strictLowerKernel` with the
  kernel of the unit map of `specialUpper`.
- `iwahoriMatrixHom_specialFibreKernel_properties`: the kernel of
  `(iwahoriMatrixHom F N).specialFibreMap` is smooth over `𝓀`, connected and
  unipotent. This is `strictLowerKernel_properties` transported by the Library's
  `smooth_connected_unipotent_of_groupIso`.

## Comparison with Kaletha–Prasad

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition 8.4.15
(printed pp. 306–307) and Theorem 8.4.19(1) (printed p. 309). These are read
with the authors' corrections of 1 November 2024. For §8.4 the corrections
assume that the residue field is perfect, which holds here because `𝓀` is
finite. They also insert, before Proposition 8.4.15, the definition of
`ρ_{Ω,Ω'} : G^0_{Ω'} → G^0_Ω` from the inclusion `G(K)^0_{Ω'} ⊆ G(K)^0_Ω` for
`Ω ≺ Ω'`, and they delete the first sentence of Proposition 8.4.15.

The assertion formalized here is the first clause of Proposition 8.4.15 and of
Theorem 8.4.19(1): for facets `F ≺ F'` the kernel of the special-fibre map of
`ρ_{F,F'}` is a smooth connected unipotent group.

Both results also describe the kernel as a product of root-group kernels, by
multiplication. Proposition 8.4.15 gives the valid product, over all
nondivisible roots `a` of the ambient relative root system `Φ`:
`∏_{a ∈ Φ_nd} ker(Ū_{a,F',0} → Ū_{a,F,0}) ≅ ker(ρ̄_{F,F'})`. Theorem 8.4.19(1)
instead prints the index `Φ'_{F'} − Ψ_F(F')`, in its statement and again in
its proof. That printed index is false, and the 2024 corrections (pp. 37–38)
do not repair it. For an open chamber `F'`, the set `Φ'_{F'}` of §8.4.6
(printed p. 304) is empty, because no affine root vanishes on `F'`, so the
printed product would be trivial. But a direct computation with the `SL_2`
models of KP's Example 8.3.5 (printed pp. 296–297) gives the kernel `G_a` for a
chamber and its hyperspecial vertex. The Library's source ledger records this
discrepancy and the computation (`notes/bruhat-tits/kp-source-ledger.md`, row
8.4.19). Neither product is formalized here.

Here `F'` is the standard alcove, whose Iwahori subgroup consists of the
matrices that are upper triangular modulo `ϖ`, and `F` is the hyperspecial
vertex with stabilizer `GL_N(𝒪)`. The map `iwahoriMatrixHom` plays the role of
`ρ_{F,F'}`. The kernel computed here is `1 + J_-`, with one coordinate for each
strictly lower position. This is a derived observation for this split case,
not a statement printed in KP: it is consistent with the product of
Proposition 8.4.15, where the factor for the root `e_i - e_j` is a copy of
`G_a` when `i > j` and trivial when `i < j`, as in Example 8.3.5. This
root-by-root count is not formalized. KP's proof goes through root groups and
the open cell. The Lean proof is a direct computation in the algebra `𝓀 ⊗ Λ`,
through the Library's unipotent-part construction for finite free algebras.

## Provenance

Derived. The statement is the `GL_N` instance of the smooth-connected-unipotent
assertion of KP Proposition 8.4.15 and Theorem 8.4.19(1), for the concrete
models of this module and the published `GeneralLinearIwahoriModel`. It does
not use the root-group product of either result. The models and homomorphisms
are built from the published unit-group and order-model constructions. No
external code is adapted.

## Not claimed

Nothing here identifies `iwahoriModel F N` or `matrixOrderModel F N` with KP's
connected parahoric models `G^0_{F'}` and `G^0_F`, and no building or facet is
used. KP works over the maximal unramified extension, and these models are over
`𝒪[F]`. The product decomposition of the kernel into root-group kernels
(Proposition 8.4.15) is not formalized, and the dimension `N(N - 1)/2` (the value of `strictLowerCount N`)
is not proved. The image of the special-fibre map (Theorem 8.4.19(2)) is not
computed: the module only uses that the map factors through the upper
triangular units. Other pairs of facets and other groups are not treated.
