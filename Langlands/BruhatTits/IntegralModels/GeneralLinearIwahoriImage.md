# The special-fibre image from the `GL_N` Iwahori model to the hyperspecial model

Module `Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriImage`.

Let `F` be a nonarchimedean local field with valuation ring `𝒪 = 𝒪[F]` and
residue field `𝓀 = 𝓀[F]`. Let `Λ = iwahoriOrder F N` be the Iwahori order, the
matrices over `𝒪` whose strictly lower entries lie in the maximal ideal. The
published module `GeneralLinearIwahoriKernel` defines the hyperspecial model
`matrixOrderModel F N` (the unit group scheme of `M_N(𝒪)`). It also defines the
homomorphism `iwahoriMatrixHom F N` from the Iwahori model `iwahoriModel F N` to
it, which extends the identity of `GL_N`, and shows that its special-fibre
kernel is smooth, connected and unipotent.

This module computes the image of that special-fibre map. The main definition,
`specialFibreImageIso`, identifies the actual schematic image (the Library's
`SchematicImage.image`) of `(iwahoriMatrixHom F N).specialFibreMap` with the
Library's block parabolic subgroup scheme of `GL_N` over `𝓀` for the strictly
decreasing weights `-i`. That subgroup scheme is the upper triangular Borel
subgroup. Under this isomorphism the closed inclusion of the image corresponds
to the block parabolic inclusion, once the special fibre of `matrixOrderModel F N`
is identified with `GL_N` over `𝓀` (`specialFibreImageIso_hom_comp`). The image
is therefore a parabolic subgroup and a Borel subgroup.

The module then packages `iwahoriMatrixHom` as a homomorphism of
relative-component model data, `iwahoriMatrixModelHom`, from the published
`iwahoriModelData F N` to `matrixOrderModelData F N`. It proves three of the
Library's model-morphism predicates for it, the kernel, parabolic-image and
reduction-preimage clauses of KP Axiom 4.1.22: (1), (2) and (4). These are the
`GL_N` instances, for the standard alcove and its hyperspecial vertex, of KP
Theorem 8.4.19(1) (first clause only), (2) (parabolicity only) and (3).

## An algebra section of the upper triangular reduction

Write `UT = upperTriangular F N` for the upper triangular matrices over `𝓀`.
The published `specialUpper : 𝓀 ⊗[𝒪] Λ → UT` reduces `𝓀 ⊗ Λ` to the upper
triangular matrices. Its kernel is the strictly lower part `J_-`.

- `kernelBasis_inl_equivFin` and `iwahoriUnit_mul_upper`. At positions on or
  above the diagonal, the published scaled matrix units of `Λ` are the matrix
  units, so they multiply as matrix units: `E_{ij} E_{kl}` is `E_{il}` if
  `j = k` and `0` otherwise.
- `upperSectionLinear : UT → 𝓀 ⊗ Λ` (`Basis.constr` on the published
  `upperBasis`) sends the matrix unit at an upper position to the corresponding
  basis vector `1 ⊗ E_{ij}` of the published `kernelBasis`
  (`upperSectionLinear_upperBasis`).
- `specialUpper_upperSectionLinear`: `upperSectionLinear` is a linear section of
  `specialUpper`, by the published `specialUpper_kernelBasis_inl`.
- `kernelBasis_inl_mul_mem`, `upperSectionLinear_mul_mem` and
  `one_mem_range_upperSectionLinear`: the range of `upperSectionLinear` is
  closed under multiplication and contains `1`. For `1`, the proof uses the
  published `sum_iwahoriUnit_diag`.
- `upperSectionLinear_specialUpper_of_mem`: on its range, `upperSectionLinear`
  inverts `specialUpper`. So for `x, y ∈ UT` the product
  `upperSectionLinear x * upperSectionLinear y` equals
  `upperSectionLinear (x * y)`. This gives the algebra map `upperSection`, with
  `specialUpper_comp_upperSection` (it is a section of `specialUpper`).

## The upper triangular units

- `upperUnits`: the published unit group scheme of `UT` with `upperBasis`.
- `upperUnitMap`: the published `UnipotentPart.unitMap` of `specialUpper`, from
  the unit group of `𝓀 ⊗ Λ` (with the published flat basis of `kernelBasis`) to
  `upperUnits`.
- `upperSectionMap`: the unit map of `upperSection`, with
  `upperSectionMap_comp_upperUnitMap` (`upperSectionMap ≫ upperUnitMap = 𝟙`), by
  the published `map_comp` and `map_id`.
- `upperUnitMap_dominant`: `upperUnitMap` is scheme-theoretically dominant.
  By Mathlib's `Scheme.Hom.le_ker_comp`, its kernel ideal sheaf lies in that of
  `upperSectionMap ≫ upperUnitMap = 𝟙`, which is `⊥`.

## The upper triangular Borel subgroup of `GL_N` over `𝓀`

- `upperWeight N i = -i`, with `upperWeight_strictAnti` and `upperWeight_lt_iff`.
  The Library's block parabolic subgroup functor `GeneralLinear.blockParabolic`
  for these weights consists of the points with vanishing entries at positions
  `(i, j)` with `j < i`.
- `upperMatrix F N S : S ⊗ UT → M_N(S)` (through Mathlib's `matrixEquivTensor`),
  with `upperMatrix_tmul`, `upperMatrix_apply_of_lt` (strictly lower entries
  vanish), `upperUnitMatrix`, `upperUnitMatrix_val`,
  `upperMatrix_tmul_upperUnitMatrix_apply` and `upperMatrix_sum` (every upper
  triangular matrix over `S` is in the image). `upperPart_val` and
  `upperMatrix_injective` show that `upperMatrix` is injective, using the
  published `upperPart` as a retraction.
- `upperGLMap : upperUnits → GL_N`: the unit map of the inclusion
  `UT ⊆ M_N(𝓀)` followed by the published `generalLinearIso`. On points it is
  `upperMatrix` (`upperGLMap_points`).
- `range_upperGLMap`: its range functor is the block parabolic subgroup functor
  for `upperWeight N`. A point of `GL_N` in that functor has an upper triangular
  matrix, and so has its inverse. Both lift through `upperMatrix_sum`, and
  `upperMatrix_injective` shows that the lifts are mutually inverse units.
- `mono_upperGLMap` (from the published `mono_map` with `upperPart`) and
  `isRepresentedBy_upperGLMap`. Hence `upperBorelIso : upperUnits ≅
  blockParabolicScheme (Fin N) 𝓀 (upperWeight N)`, by the Library's
  `IsRepresentedBy.isoOfIsRepresentedBy`, with `upperBorelIso_hom_comp`
  (it carries `upperGLMap` to the Library's `blockParabolicHom`).
- `isClosedSubgroup_upperGLMap`, from the Library's
  `isClosedSubgroup_blockParabolicHom`.
- `isParabolicSubgroup_upperGLMap`: the Library's
  `isParabolicSubgroup_of_range_eq_dynamicParabolic` applies, with
  `isConnectedReductive_generalLinear` and the diagonal cocharacter of the weights,
  because `range_upperGLMap` and the Library's `parabolic_diagonalCocharacter`
  identify the range with the dynamic parabolic subgroup.
- `isBorelSubgroup_upperGLMap`: the Library's
  `UpperTriangular.isBorelSubgroup_blockParabolicHom` for the strictly
  decreasing weights, transported along `upperBorelIso`.

## The special-fibre image

- `upperFibreInclusion`: the unit map of the published `upperInclusion :
  UT → 𝓀 ⊗ M_N(𝒪)`. The published `kernelFibreMap` is
  `upperUnitMap ≫ upperFibreInclusion` (`kernelFibreMap_eq`, by definition).
- `glFibreIso`: the unit group of `𝓀 ⊗ M_N(𝒪)` (published `specialMatrixBasis`)
  is `GL_N` over `𝓀`, through `specialMatrixEquiv` and `generalLinearIso`.
  `specialMatrixEquiv_comp_upperInclusion` and
  `upperFibreInclusion_comp_glFibreIso` show that `upperFibreInclusion`
  followed by `glFibreIso` is `upperGLMap`, so `upperFibreInclusion` is a closed
  subgroup (`isClosedSubgroup_upperFibreInclusion`).
- Local instances: affineness of the special fibres of integral models, and of
  the unit groups of `𝓀 ⊗ Λ` and `𝓀 ⊗ M_N(𝒪)`, from the published
  `groupScheme_isAffineHom`. `upperUnitMap_dominant` is a local instance.
- `specialFibreImageUnitIso`: the Library's `SchematicImage.isoOfIsoSquare` for
  the published square `kernelFibre_square` identifies the image of the
  special-fibre map with the image of `kernelFibreMap`, compatibly with the
  inclusions (`specialFibreImageUnitIso_hom_comp`).
- `kernelFibreImageIso`: the image of `kernelFibreMap` is `upperUnits`, by the
  Library's `SchematicImage.isoOfDominantFactorizations`, applied to two closed
  factorizations of `kernelFibreMap` with dominant first factor: the actual
  projection and inclusion of the image, and `upperUnitMap` followed by
  `upperFibreInclusion` (`kernelFibreImageIso_hom_comp`).
- `specialFibreImageUpperIso`, the composite, with
  `specialFibreImageUpperIso_hom_comp`. It carries `upperGLMap` to the image
  inclusion followed by `matrixFibreIso ≪≫ glFibreIso`.
- `specialFibreImageIso := specialFibreImageUpperIso ≪≫ upperBorelIso`, with
  `specialFibreImageIso_hom_comp`.
- `isParabolicSubgroup_specialFibreImage` and
  `isBorelSubgroup_specialFibreImage`: the image inclusion is a parabolic and a
  Borel subgroup of the special fibre of `matrixOrderModel F N`. These are
  transported along `specialFibreImageUpperIso` and the ambient isomorphism, by
  the Library's `IsParabolicSubgroup.iso_comp` and `comp_iso_iff`, and
  `IsBorelSubgroup.iso_comp` and `comp_iso`.

## Rational points of the image

- `kernelFibreIso_inv_comp`: the published square, read with the inverse of
  `kernelFibreIso`.
- `specialFibreImageSection`: the map `specialFibreImageUpperIso`, then
  `upperSectionMap`, then the inverse of `kernelFibreIso`. It is a section of the
  projection onto the image: `specialFibreImageSection_comp` says that its
  composite with the special-fibre map is the image inclusion.
- `specialFibreImage_projection_surjective`: the projection onto the image is
  surjective on `𝓀`-points. The inclusion is a monomorphism, so a point of the
  image is the projection of its image under the section.

## The congruence subgroup of `GL_N(𝒪)`

- `matrixOrderModelData`: the published `orderModelData` of `M_N(𝒪)`, with full
  and neutral models both `matrixOrderModel F N`.
- `matrixSectionUnit`: the unit of `M_N(𝒪)` of an integral section (published
  `sectionUnitsEquiv`).
- `matrixSectionUnit_residue_of_reduction_eq_one`: if the reduction of an
  integral section is `1`, its unit reduces to the identity matrix over `𝓀`.
  The proof applies the published `baseChange_congr_map_eq_one_iff` with
  `specialMatrixEquiv` and `specialMatrixEquiv_one_tmul`.
- `matrixIntegralPointMap_matrix`: the matrix of the generic point of an
  integral section is its unit with entries in `F` (published
  `orderModelData_integralPointMap_of_eq`).
- `matrixCongruenceSubgroup_le`: the congruence subgroup of the hyperspecial
  model lies in the Iwahori subgroup. The strictly lower entries of a unit
  congruent to `1` lie in the maximal ideal, so the point is in the published
  `generalLinearIwahoriPoints` (`mem_generalLinearIwahoriPoints`,
  `iwahoriModel_integralPoints`).

## The model-data homomorphism

- `iwahoriMatrixModelHom : RelativeComponentModelHom (iwahoriModelData F N)
  (matrixOrderModelData F N)`, with full and neutral components both
  `iwahoriMatrixHom F N`. Both model data have identity inclusions.
- `iwahoriMatrixModelHom_hasSmoothConnectedUnipotentKernel`: the Library's
  `HasSmoothConnectedUnipotentKernel` (KP Axiom 4.1.22(1)), which is the
  published `iwahoriMatrixHom_specialFibreKernel_properties`.
- `iwahoriMatrixModelHom_hasParabolicSpecialFibreImage`: the Library's
  `HasParabolicSpecialFibreImage` (KP Axiom 4.1.22(2)), which is
  `isParabolicSubgroup_specialFibreImage`.
- `iwahoriMatrixModelHom_isBorelSubgroup_specialFibreImage`: the image
  inclusion `specialFibreImageInclusion` is a Borel subgroup.
- `iwahoriMatrixModelHom_hasParabolicReductionPreimage`: the Library's
  `HasParabolicReductionPreimage` (KP Axiom 4.1.22(4)). Take the integral
  sections of the hyperspecial model whose reduction lies in the residue-field
  points of the image. They are exactly the images of the integral sections of
  the Iwahori model. The Library's `hasParabolicReductionPreimage_iff` applies,
  with the Library's `henselianLocalRing_integer`, the published
  `iwahoriModel_isSmooth` and `specialFibreImage_projection_surjective`, and it
  reduces the claim to the inclusion of the congruence kernel in the image of the
  sections. The Library's `congruenceKernel_le_sectionRange_iff` turns this into
  `matrixCongruenceSubgroup_le`.

## Comparison with Kaletha–Prasad

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Axiom 4.1.22
(printed pp. 163–164) and Theorem 8.4.19 (printed p. 309), read with the
authors' corrections of 1 November 2024. The corrections do not change Axiom
4.1.22 or Theorem 8.4.19. For §8.4 they assume that the residue field is
perfect, which holds here because `𝓀` is finite. They also insert, before
Proposition 8.4.15, the definition of `ρ_{Ω,Ω'}` from the inclusion
`G(K)^0_{Ω'} ⊆ G(K)^0_Ω` for `Ω ≺ Ω'`.

For facets `F ≺ F'`, Axiom 4.1.22 asserts the following, among other things:
(1) the special-fibre map of `ρ_{F,F'}` has smooth connected unipotent kernel;
(2) its image `p_F(F')` is a parabolic subgroup of the special fibre of
`G^0_F`; and (4) the inverse image of `p_F(F')(f)` under the reduction map from
the `o`-points of `G^0_F` is the group of `o`-points of `G^0_{F'}`. KP state
after the axioms (printed p. 166) that part (1) is Proposition 8.4.15 and parts
(2)–(5) are Theorem 8.4.19. Theorem 8.4.19(2) says more than parabolicity: `p_F(F')` is the
parabolic subgroup associated to the parabolic subset `Ψ_F(F')` of the root
system `Φ_F` of the maximal reductive quotient. Theorem 8.4.19(3) is the
preimage assertion, which KP state over the maximal unramified extension.

Here `F'` is the standard alcove, whose parahoric subgroup (an Iwahori subgroup)
consists of the matrices in `GL_N(𝒪)` that are upper triangular modulo the
maximal ideal, and `F` is the hyperspecial vertex whose parahoric subgroup is
`GL_N(𝒪)`. By KP Definition 4.1.3 (printed p. 158), the parahoric subgroup of a
facet is its stabilizer in `G(k)^0`, not its full stabilizer in `G(k)`, where
`k` is the local field. The two differ here: by Axiom 4.1.1 (printed p. 158),
the action of `GL_N(k)` on the reduced building factors through the adjoint
group, so the scalar matrix `ϖ · 1`, for a uniformizer `ϖ`, fixes `F` but does
not lie in `GL_N(𝒪)`. No building, facet stabilizer or parahoric subgroup is
formalized here. The map `iwahoriMatrixHom` plays the role of `ρ_{F,F'}`. The
formalized results are the clauses (1), (2) and (4) of Axiom 4.1.22, stated with
the Library's predicates over `𝒪[F]` and `𝓀[F]`, the formulation of the axiom.
In addition, the image is the upper triangular Borel subgroup. The special fibre
of the hyperspecial model is `GL_N`, which is reductive, so the maximal
reductive quotient in Theorem 8.4.19(2) is the special fibre itself. That this
Borel subgroup is the parabolic subgroup associated to `Ψ_F(F')` is a derived
observation, not formalized: its roots are the `e_i − e_j` with `i < j`. Neither
`Ψ_F(F')` nor KP's correspondence between parabolic subsets and parabolic
subgroups appears here.

The proofs differ from KP's. KP's proof of 8.4.19(2) goes through root groups
and the structure of the special fibre (Theorem 8.4.10), and their proof of (3)
uses Corollary 8.4.12 and the inclusion `G(K)_{F,0+} ⊆ G(K)^0_{F'}` from
6.3.21. Here the image is computed directly in the algebra
`𝓀 ⊗ Λ`. The special-fibre map factors as the split surjection onto the upper
triangular units, followed by a closed immersion. The preimage assertion
reduces, by the Library's Henselian lifting criterion, to the fact that a matrix
in `GL_N(𝒪)` congruent to `1` lies in the Iwahori subgroup.

## Provenance

Derived. The statements are the `GL_N` instances, for the standard alcove and
its hyperspecial vertex, of KP Axiom 4.1.22(1), (2), (4), and of the
corresponding parts of Theorem 8.4.19, for the concrete models of this module
and the published `GeneralLinearIwahoriModel` and `GeneralLinearIwahoriKernel`.
The identification of the image with the upper triangular Borel subgroup is
derived for this split case. The models and homomorphisms are built from the
published unit-group, order-model, schematic-image and block-parabolic
constructions. No external code is adapted.

## Not claimed

Nothing here identifies `iwahoriModel F N` or `matrixOrderModel F N` with KP's
connected parahoric models `G^0_{F'}` and `G^0_F`, and no building or facet is
used. `matrixOrderModelData F N` is not compared with the Library's standard
model data `generalLinearModelData F N`, although both have integral points
`GL_N(𝒪)`. The parabolic subset `Ψ_F(F')`, the Lie-algebra weights of
Axiom 4.1.22(3), and the bijection of Axiom 4.1.22(5) and Theorem 8.4.19(4) are
not formalized. Other pairs of facets and other groups are not treated.
