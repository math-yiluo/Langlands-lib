# Iwasawa decomposition for the inherited compact in a standard Levi of `GL_N`

`Langlands.BruhatTits.SpecialCompact.generalLinearIntegralLeviIwasawa` proves
`GeneralLinearIntegralLeviIwasawaStatement.{u}` at arbitrary universe `u`.
For `GL_N` over a nonarchimedean local field `F`, a generic diagonal
cocharacter `ν` and a subset `J` of its simple relative roots, the preimage
`KJ` of the standard integral points `GL_N(𝒪_F)` in the rational points of
the actual standard Levi `M_J` is compact, open and maximal among compact
subgroups, and the minimal standard parabolic `P` of `M_J` (empty index, the
factored diagonal torus and the original `ν`) satisfies `P · KJ = M_J(F)` and
`KJ · P = M_J(F)`. This is Renard, Theorem V.5.1(5), with its opening
maximal-compactness assertion and part (1), for the standard integral subgroup
of `GL_N`.
[Statement](GeneralLinearIntegralLeviIwasawaStatement.md)

## Implemented proof

**An integral model of the Levi.** The published `standardCocharacter`
provides a standard cocharacter `ζ` of the diagonal torus for the index `J`,
whose dynamic centralizer is the standard Levi `M_J`; hence the closed Levi
inclusion `Standard.leviHom` represents that centralizer. The proof lifts `ζ`
to the cocharacter `χ` of the standard integral model with the same diagonal
weights over `𝒪_F` (`GeneralLinear.diagonalCocharacter` applied to
`GeneralLinear.cocharacterCoordEquiv`); its generic fibre is `ζ` followed by
the diagonal torus. The dynamic centralizer of `χ` is then an integral model
`Z` of `M_J` (`IntegralModel.DynamicCentralizer.model`) with a closed
inclusion into the standard integral model, and
`IntegralModel.Hom.integralPoints_eq_comap` identifies the integral points of
`Z` with `KJ`.
[Dynamic centralizer model](../../GroupScheme/IntegralModel/DynamicCentralizer.md)
[Standard cocharacters](../../GroupScheme/Rational/StandardCocharacterProof.md)

**Maximal compactness and openness.** The published
`dynamicCentralizerReductive` shows that both fibres of `Z` are connected
reductive: over `F` it is applied to `GL_N` and `ζ`, and over the residue
field to `GL_N` there and the base change of `χ`, using
`isConnectedReductive_generalLinear` in each fibre. The published
`IntegralModel.maximalCompactStatement` then shows that `KJ` is compact and
maximal among compact subgroups, and
`IntegralModel.isOpen_integralPoints_localField` shows that it is open.
[Dynamic centralizers are reductive](../../GroupScheme/Dynamic/CentralizerReductiveProof.md)
[Maximal compactness of integral points](../../GroupScheme/IntegralModel/MaximalCompact.md)

**The Iwasawa products.** The integral lift `χν` of `ν` with the same diagonal
weights has diagonal matrices as values, so it lies in the block Levi
described by `GeneralLinear.centralizer_diagonalCocharacter`, which is the
dynamic centralizer of `χ`. It therefore factors through `Z` as a cocharacter
`χL`, whose generic fibre is `ν` followed by the factored diagonal torus
`Standard.leviTorusHom`; this is checked after composing with the
monomorphism `Standard.leviHom`, using `Standard.leviTorusHom_comp`. By
`StandardLeviNested.leviScheme_rankPackage` this torus is maximal split in
`M_J` and `ν` is generic there, so
`standardParabolic_empty_eq_dynamic_of_generic` identifies `P` with the
rational points of the dynamic parabolic of that generic cocharacter, which is
the range of `Z.cellParabolicHom χL`. The published integral-model Iwasawa
theorem `IntegralModel.cellIwasawa` gives `P · KJ = M_J(F)`. For the other
order, write `g⁻¹ = p k` with `p ∈ P` and `k ∈ KJ`; then `g = k⁻¹ p⁻¹`
lies in `KJ · P`.
[Integral Iwasawa theorem](../../GroupScheme/IntegralModel/IwasawaCellDynamic.md)
[Minimal standard parabolics as dynamic parabolics](../../GroupScheme/Rational/MinimalStandardDynamicComparison.md)
[Nested standard Levis](../../GroupScheme/Rational/StandardLeviNestedTransport.md)

## Provenance and scope

The proof composes the named Library results; it does not follow Renard's
argument through the building. The theorem uses only the standard integral
model of `GL_N` and imposes no restriction on the characteristic or residue
characteristic of `F`, on `N` or on `J`. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.
