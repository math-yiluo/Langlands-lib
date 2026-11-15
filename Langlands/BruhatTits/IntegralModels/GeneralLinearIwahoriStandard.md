# The Iwahori model of `GL_N` over the standard hyperspecial model

Module `Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriStandard`.

Let `F` be a nonarchimedean local field with valuation ring `𝒪 = 𝒪[F]` and
residue field `𝓀 = 𝓀[F]`. The published module `GeneralLinearIwahoriImage`
proves the clauses (1), (2) and (4) of KP Axiom 4.1.22 for the homomorphism
`iwahoriMatrixModelHom F N` from the Iwahori model data `iwahoriModelData F N`
to `matrixOrderModelData F N`. The target there is built from the unit group
scheme of the order `M_N(𝒪)` (`matrixOrderModel F N`). The Library's own
hyperspecial model data for `GL_N` is a different object,
`generalLinearModelData F N` (module `GeneralLinearDepthZero`). Its neutral
model is the standard model `GeneralLinear.standardIntegralModel 𝒪 F (Fin N)`,
that is `GL_{N,𝒪}` with the Library's base-change identification over `F`. Its
reductive quotient data `generalLinearQuotientData F N` is the identity
quotient of the special fibre.

This module identifies the two hyperspecial models and moves the published
results to the standard model data. The main definition is
`iwahoriStandardModelHom : RelativeComponentModelHom (iwahoriModelData F N)
(generalLinearModelData F N)`. For it, the module proves the Library's
predicates for the clauses (1), (2) and (4) of KP Axiom 4.1.22, and the
parabolicity of the image in the reductive quotient. It also shows that the two
images are Borel subgroups. It then proves the Library's predicate for clause
(7) for the hyperspecial quotient data and the Iwahori quotient data
`iwahoriQuotientData F N`.

## Two general helpers

- `IntegralModel.reflIso M : M.Iso M (Iso.refl G)`: the identity
  isomorphism of an integral model, over the identity of the generic group.
  No such isomorphism was in the Library.
- `RelativeComponentModelHom.hasParabolicReductionPreimage_iff_imageReductionPreimage`:
  for any homomorphism `φ` of relative-component model data,
  `φ.HasParabolicReductionPreimage` holds if and only if
  `φ.neutral.imageReductionPreimage` equals the image of the neutral integral
  sections under `φ.neutral`. Both sides unfold to the same statement (the
  Library's `Hom.imageReductionPreimage` and `SchematicImage.rationalImage`).
  The Library uses this unfolding inside the proof of
  `hasParabolicReductionPreimage_of_unramifiedModels`. Stating it separately
  avoids a slow definitional unfolding when one of the model data is a defined
  constant such as `matrixOrderModelData F N`.

## The order model of `M_N(𝒪)` is the standard model

- `matrixEquivTensor_symm_orderEquiv`. Let `S` be an `𝒪`-algebra that is also an
  `F`-algebra, with compatible scalars. Take `w` in `S ⊗[𝒪] M_N(𝒪)`. Read `w`
  as a matrix over `S` (the Library's `matrixEquivTensor`). Alternatively, send
  `w` to `S ⊗[F] (F ⊗[𝒪] M_N(𝒪))` by `s ⊗ a ↦ s ⊗ (1 ⊗ a)` (the Library's
  `baseChangeTensorEquiv`), apply the published order identification
  `orderEquiv : F ⊗[𝒪] M_N(𝒪) ≃ M_N(F)`, and read the result as a matrix over
  `S`. The two matrices agree. The proof checks this on pure tensors.
- `matrixOrderModelIso : (matrixOrderModel F N).Iso
  (GeneralLinear.standardIntegralModel 𝒪 F (Fin N)) (Iso.refl _)`. The group
  isomorphism is the Library's `generalLinearIso`, which identifies the unit
  group scheme of `M_N(𝒪)` with `GL_{N,𝒪}`. The compatibility with the two
  generic identifications is checked on points (the Library's
  `hom_ext_points`) after applying the injective point equivalence
  `GeneralLinear.pointsEquiv`. On the standard side the Library's
  `GeneralLinear.pointsEquiv_comp_baseChangeIso_hom`, `baseChangePointsEquiv_comp`
  and `generalLinearIso_hom_points` compute the points. On the order side the
  published unit-group identification computes them, and
  `matrixEquivTensor_symm_orderEquiv` matches the two matrices.
- `standardMatrixOrderIso`: the inverse isomorphism, from the standard model to
  `matrixOrderModel F N` over `Iso.refl _` (the Library's `Iso.symm` and
  `Iso.changeGeneric`).

## The Iwahori model over the standard model

- `iwahoriStandardHom : (iwahoriModel F N).Hom
  (GeneralLinear.standardIntegralModel 𝒪 F (Fin N)) (𝟙 _)`. Its underlying map
  is the published `iwahoriMatrixHom F N`, which comes from the inclusion of the
  Iwahori order into `M_N(𝒪)`, followed by `generalLinearIso`.
- `iwahoriStandardModelHom`: the homomorphism of relative-component model data
  with full and neutral components both `iwahoriStandardHom F N`. Both model
  data have identity inclusions.
- `iwahoriStandardHom_specialFibreMap_square`: the special-fibre map of
  `iwahoriStandardHom F N`, followed by the special-fibre isomorphism of
  `standardMatrixOrderIso F N`, is the special-fibre map of `iwahoriMatrixHom F N`.
  This is the special-fibre base change of the Library's `Iso.hom_square`.

## KP Axiom 4.1.22 over the standard model

Each statement below is transported from the published statement for
`iwahoriMatrixModelHom F N` along `IntegralModel.reflIso (iwahoriModel F N)` on
the source and `standardMatrixOrderIso F N` on the target.

- `iwahoriStandardModelHom_hasSmoothConnectedUnipotentKernel`: the Library's
  `HasSmoothConnectedUnipotentKernel` (KP Axiom 4.1.22(1)). The special-fibre
  kernel is smooth, connected and unipotent. Transport by the Library's
  `Iso.specialFibreKernel_properties`.
- `iwahoriStandardModelHom_hasParabolicSpecialFibreImage`: the Library's
  `HasParabolicSpecialFibreImage` (KP Axiom 4.1.22(2)). The actual schematic
  image of the special-fibre map is a parabolic subgroup of the special fibre
  `GL_{N,𝓀}`. Transport by the Library's `Iso.specialFibreImage_isParabolic`.
- `iwahoriStandardModelHom_isBorelSubgroup_specialFibreImage`: the same image is
  a Borel subgroup. Transport by the Library's
  `SchematicImage.isoOfReverseIsoSquare_hom_comp` and the invariance of
  `IsBorelSubgroup` under composition with isomorphisms.
- `iwahoriStandardModelHom_hasParabolicReductionPreimage`: the Library's
  `HasParabolicReductionPreimage` (KP Axiom 4.1.22(4)). The sections of
  `GL_{N,𝒪}` whose reduction lies in the residue-field points of the image are
  exactly the images of the sections of the Iwahori model. Transport by the
  Library's `Iso.imageReductionPreimage_eq_range` and the helper above.
- `iwahoriStandardModelHom_hasParabolicReductiveImage`: the Library's
  `HasParabolicReductiveImage` for `generalLinearQuotientData F N`. The image in
  the specified reductive quotient is parabolic. That quotient is the identity
  quotient, whose projection is the identity of the special fibre. So the
  reductive image is the special-fibre image, and the claim is the parabolicity
  above.
- `iwahoriStandardModelHom_isBorelSubgroup_reductiveImage`: the image in the
  reductive quotient is a Borel subgroup, for the same reason.
- `generalLinearIwahori_satisfiesPositiveRadicalClause`: the Library's
  `SatisfiesPositiveRadicalClause` for the target quotient data
  `generalLinearQuotientData F N` and the source quotient data
  `iwahoriQuotientData F N` (KP Axiom 4.1.22(7)). The Library's predicate takes
  only the two quotient data, not a model homomorphism. It has three parts. The
  reductions of `GL_{N,𝒪}` and of the Iwahori model are surjective on sections:
  both models are smooth, and `𝒪` is Henselian (the Library's
  `reduction_surjective` and `henselianLocalRing_integer`). The positive subgroup
  of the hyperspecial quotient data lies in the positive subgroup of the Iwahori
  quotient data. The published `iwahoriQuotientData_positivePoints` identifies the
  latter with `I^+ = generalLinearIwahoriPositivePoints F N`, the matrices in
  `GL_N(𝒪)` that reduce to upper unitriangular matrices. The published
  `positivePoints_le_generalLinearIwahoriPositivePoints` gives the inclusion.

## Comparison with Kaletha–Prasad

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Axiom 4.1.22
(printed pp. 163–164), Corollary 8.4.12 (printed p. 306) and Theorem 8.4.19
(printed p. 309), read with the authors' corrections of 1 November 2024. The
corrections do not change Axiom 4.1.22, Corollary 8.4.12 or Theorem 8.4.19. For
§8.4 they assume that the residue field is perfect, which holds here because
`𝓀` is finite. They also insert, before Proposition 8.4.15, the definition of
`ρ_{Ω,Ω'}` from the inclusion `G(K)^0_{Ω'} ⊆ G(K)^0_Ω` for `Ω ≺ Ω'`.

For facets `F ≺ F'`, Axiom 4.1.22 asserts the following, among other things:
(1) the special-fibre map of `ρ_{F,F'}` has smooth connected unipotent kernel;
(2) its image `p_F(F')` is a parabolic subgroup of the special fibre of
`G^0_F`; (4) the inverse image of `p_F(F')(f)` under the reduction map from the
`o`-points of `G^0_F` is the group of `o`-points of `G^0_{F'}`; and (7) the
preimage `G(k)^{0+}_F` of the `f`-points of the unipotent radical of the special
fibre of `G^0_F` lies in `G(k)^{0+}_{F'}`. Part (3) names the image `℘_F(F')` of
`p_F(F')` in the maximal reductive quotient `G_F`. The bijection of part (5) maps
onto the parabolic subgroups of `G_F`, so `℘_F(F')` is parabolic there. The
Library's `HasParabolicReductiveImage` states that parabolicity. KP state after
the axioms (printed p. 166) that part (1) is Proposition 8.4.15, parts (2)–(5)
are Theorem 8.4.19 and part (7) is Corollary 8.4.12.

Here `F'` is the standard alcove, whose parahoric subgroup (an Iwahori subgroup)
consists of the matrices in `GL_N(𝒪)` that are upper triangular modulo the
maximal ideal, and `F` is the hyperspecial vertex whose parahoric subgroup is
`GL_N(𝒪)`. By KP Definition 4.1.3 (printed p. 158), the parahoric subgroup of a
facet is its stabilizer in `G(k)^0`, not its full stabilizer in `G(k)`, where
`k` is the local field. No building, facet stabilizer or parahoric subgroup is
formalized here. The map `iwahoriStandardHom` plays the role of `ρ_{F,F'}`, with
target the Library's standard model `GL_{N,𝒪}`. The special fibre `GL_{N,𝓀}` of
that model is reductive, so its unipotent radical is trivial and `G_F` is the
special fibre itself. Then `℘_F(F') = p_F(F')`, and `G(k)^{0+}_F` is the group
of matrices in `GL_N(𝒪)` congruent to `1` modulo the maximal ideal. For `F'`
the published Iwahori quotient data has the diagonal torus as reductive
quotient, and its positive subgroup, the counterpart of `G(k)^{0+}_{F'}`, is
`I^+` (`iwahoriQuotientData_positivePoints`).

The proofs differ from KP's. KP state Corollary 8.4.12 and Theorem 8.4.19 over
the maximal unramified extension `K`. Corollary 8.4.12 identifies the preimage of
the unipotent radical with the filtration subgroup `G(K)_{Ω,0+}`, using the
structure of the special fibre (Theorem 8.4.10). Here every clause except
(7) is transported from the published computation over the order model of
`M_N(𝒪)`, along the isomorphism of that model with `GL_{N,𝒪}`. Clause (7) is
the published comparison of the two positive subgroups as explicit preimages of
reductions.

## Provenance

Derived. The statements are the `GL_N` instances, for the standard alcove and
its hyperspecial vertex, of KP Axiom 4.1.22(1), (2), (4), (7), of the
parabolicity of `℘_F(F')`, and of the corresponding parts of Theorem 8.4.19 and
Corollary 8.4.12, for the Library's standard model data `generalLinearModelData
F N` and the published Iwahori model data. The Borel statements are derived for
this split case. The isomorphism `matrixOrderModelIso` and the two general
helpers are internal constructions. They are built from the Library's
unit-group, order-model, integral-model isomorphism and schematic-image results.
No external code is adapted.

## Not claimed

Nothing here identifies `iwahoriModel F N` or `GeneralLinear.standardIntegralModel
𝒪 F (Fin N)` with KP's connected parahoric models `G^0_{F'}` and `G^0_F`, and no
building or facet is used. The maximal split tori and Lie-algebra weights of
Axiom 4.1.22(3), the bijection of Axiom 4.1.22(5) and Theorem 8.4.19(4), the
root datum of Axiom 4.1.22(6), the parabolic subset `Ψ_F(F')` and the
product decomposition of the kernel in Theorem 8.4.19(1) are not formalized.
Other pairs of facets and other groups are not treated.
