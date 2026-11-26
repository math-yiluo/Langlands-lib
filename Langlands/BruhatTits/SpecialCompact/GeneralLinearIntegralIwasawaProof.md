# Iwasawa decomposition at the standard integral subgroup of `GL_N`

`Langlands.BruhatTits.SpecialCompact.generalLinearIntegralIwasawa` proves
exactly `GeneralLinearIntegralIwasawaStatement.{u}`: the specialization of
the opening assertion and part (1) of Renard V.5.1 to the standard integral
subgroup of `GL_N`. It applies to every nonarchimedean local field `F` in
universe `u`, every matrix size `N` and every generic cocharacter `ν` of the
diagonal torus, and adds no hypothesis.
[Statement and source](GeneralLinearIntegralIwasawaStatement.md)

Write `G` for `GL_N` over `F`, `i` for its diagonal torus and `M` for
`GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)`, so that the subgroup
`K` of the statement is `M.integralPoints`.

## Compactness, openness and maximality

The generic fibre `G` is connected reductive by
`isConnectedReductive_generalLinear`. The special fibre of `M` is connected
reductive as well: `GeneralLinear.baseChangeIso` identifies it with `GL_N`
over the residue field, and `IsConnectedReductive.of_iso` transports
`isConnectedReductive_generalLinear` for that field. With both fibres
connected reductive, `IntegralModel.maximalCompactStatement` shows that
`M.integralPoints` is compact in the canonical rational-point topology and
equal to every compact subgroup containing it; the latter is the
maximality clause of `IsCompactOpenMaximal`. Openness is
`IntegralModel.isOpen_integralPoints_localField`, the openness of the
integral-point image of any model over a nonarchimedean local field.
[Maximal compactness](../../GroupScheme/IntegralModel/MaximalCompact.md)
[Openness](../../GroupScheme/IntegralModel/LocalIntegralSeparation.md)

## The two Iwasawa products

`GeneralLinear.cocharacterCoordEquiv` sends `ν` to its integer weight vector
`w`, and `GeneralLinear.diagonalCocharacter` over `𝒪[F]` with these weights
is a cocharacter `χ` of the model `M`. Its generic fibre
`M.genericCocharacter χ` is the composite of `ν` with `i`: this combines
`GeneralLinear.baseChangeCocharacter_diagonalCocharacter` with
`GeneralLinear.cocharacterOfWeights_comp_diagonalTorus`.

The diagonal torus is maximal split
(`GeneralLinear.isMaximalSplitTorus_diagonalTorus`), so for the generic
`ν` the empty-index standard parabolic equals the dynamic parabolic of
`ν` composed with `i` on all test schemes
(`standardParabolic_empty_eq_dynamic_of_generic`). The cell parabolic
homomorphism of `χ` represents that dynamic parabolic
(`IntegralModel.isRepresentedBy_cellParabolicHom`), so by
`SubgroupFunctor.rationalPoints_eq_range` the rational points `P` of
`standardParabolicPoints i ν ∅` are the range of this homomorphism on
rational points.

The integral Iwasawa covering `IntegralModel.cellIwasawa`, which uses the
two connected reductive fibres again, gives `P * K = GL_N(F)` as literal
pointwise set products. For the other order, write the inverse of an
arbitrary `g` as `g⁻¹ = p k` with `p ∈ P` and `k ∈ K`; then
`g = k⁻¹ p⁻¹ ∈ K * P` because both subgroups are closed under inversion.
These are the two equalities of `Iwasawa.PointProductEqualities` at the
same subgroup `K`.
[Integral Iwasawa theorem](../../GroupScheme/IntegralModel/IwasawaCellDynamic.md)
[Minimal standard parabolic](../../GroupScheme/Rational/MinimalStandardDynamicComparison.md)
[General-linear indexing](../../GroupScheme/Rational/GeneralLinearIndexing.md)

## Relation to the source

Renard states V.5.1 for a general reductive `p`-adic group and refers the
proofs of Section V.5 to Bruhat–Tits, *Groupes réductifs sur un corps
local* (1972), his reference [14]. This proof instead specializes the
Library's integral-model theorems, which apply to any model with connected
reductive special fibre, to the standard model of `GL_N`. It does not use
building data or the special compact subgroup of an apartment vertex.
