# Split tori and KP building data: proof of `KPSplitTorusBuildingStatement`

The theorem `Langlands.Geometry.Building.kpSplitTorusBuilding` proves exactly
`Langlands.Geometry.Building.KPSplitTorusBuildingStatement.{u}` of
`Langlands.Geometry.Building.KPTorusRegressionStatement`, at an arbitrary universe `u`. The
statement's Markdown records the sources (Kaletha–Prasad, *Bruhat–Tits theory: a new approach*,
2023, and the corrections of 1 November 2024) and the meaning of every object. The proof adds no
premise. Let `T` be a split torus over a nonarchimedean local field `F` with
`splitRank T = N`, `q = Nat.card 𝓀[F]`, and `D : KPBuildingDatum T` with
`D.SatisfiesGroupAxioms`. Of these axioms the proof uses only the clauses `neutral_points` and
`torus_clause` of Axiom 4.1.20 (`hD.bruhatTitsGroupSchemes`) and `reductive_quotients` of
Axiom 4.1.22 (`hD.reductiveQuotients.facets`). It imports the module
`Langlands.Geometry.Building.KPTorusBuildingProof` for the results on every torus.

## Field-level lemmas

- `isIso_of_isMaximalSplitTorus_of_isSplitTorus`: a maximal split torus `i : S → T` of a split
  torus `T` is an isomorphism. The identity of `T`, with the commutative law of
  `IsSplitTorus.isCommMonObj`, is a split subtorus through which `i` factors, so maximality makes
  `i` an isomorphism.
- `normalizedMultiplicativeValuation_le_one_iff`: the valuation
  `FML.normalizedMultiplicativeValuation F : Valuation F ℤᵐ⁰` (the valuation of `F` transported
  along Mathlib's order isomorphism `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`) has
  valuation ring `𝒪[F]`.
- `IntegerValuation.characterValuationKernel_normalized`: its rational-character unit kernel is
  `rationalCommonNormKernel G` (`T(F)^1`), by the Library's
  `characterValuationKernel_eq_rationalCommonNormKernel` and injectivity of the order
  isomorphism.
- `rationalCharacterValuation_surjective_of_isSplitTorus`: the valuation homomorphism
  `Plancherel.rationalCharacterValuation T : T(F) → Hom(X^*_F(T), ℤ)` is surjective (KP
  Lemma 2.5.7). The lattice pairing of a split torus is perfect
  (`CocharacterUniformizer.latticePairing_isPerfPair`), so every `f` is pairing with some
  cocharacter `c`, and the uniformizer point `CocharacterUniformizer.latticeSection F T c` has
  valuation `f` (`CocharacterUniformizer.rationalCharacterValuation_latticeSection`).
- `nonempty_valuationCoordinates_of_isSplitTorus`: `Hom(X^*_F(T), ℤ) ≃ ℤ^N`. A splitting
  `T ≅ splitTorus F I` gives `splitRank T = Nat.card I` (`splitRank_eq_of_splitIso`) and the
  coordinates `splitTorusCharacterCoordinates : X^*(T) ≃ ℤ^I`; the resulting basis of
  `X^*_F(T)` identifies its dual with `ℤ^N` (Mathlib's `Basis.constr` and
  `addMonoidHomLequivInt`).

## The integral split torus of Axiom 4.1.20(3)

Fix a facet `x` with a chart presentation `x = g · Fa`. The datum supplies an integral torus
`A = D.models.torus (ofFacet x) g Fa _` with a map `A.inclusion` into the neutral model of `x`
and a generic identification compatible with the generic inclusion `B.i ≫ Int(g)` of the maximal
split torus (`IntegralTorusData.generic_comm`). The clause `torus_clause` says that `A` is a split
`𝒪[F]`-torus and that `A.inclusion` is a closed subgroup. Since `T` is split, `B.i` is an
isomorphism by the first lemma, so the generic fibre of `A` is identified with `T` by an
isomorphism `ψ`.

- `KPBuildingDatum.rationalCommonNormKernel_le_parahoric_of_isSplitTorus`: `T(F)^1` lies in
  `D.parahoric x`. By the Library's
  `IntegralModel.map_genericHom_mem_integralPoints_of_split_characterKernel`, every unit point of
  the generic fibre of a closed split integral torus maps into the integral points of the model;
  transported along `ψ` (`map_characterValuationKernel_le`), these are all of `T(F)^1`.
- `KPBuildingDatum.card_finiteReductiveQuotientGroup_of_isSplitTorus`: the finite reductive
  quotient at `x` has `(q - 1)^N` elements. First, `A.inclusion` is an isomorphism: it is a
  closed immersion into the flat neutral model whose generic fibre is the isomorphism
  `ψ ≫ (neutral generic identification)⁻¹`, so the Library's
  `isIso_of_isClosedImmersion_of_isIso_pullback` applies, and the forgetful functors from group
  objects reflect isomorphisms. Hence the special fibre of the neutral model is isomorphic to the
  split torus `splitTorus 𝓀[F] J` (`splitTorus.baseChangeIso`), where `A ≅ splitTorus 𝒪[F] J`,
  and `T ≅ splitTorus F J`, so `Nat.card J = N`. A split torus has trivial unipotent radical
  (`IsSplitTorus.hasTrivialUnipotentRadical`), so the specified radical of Axiom 4.1.22 has
  trivial image (`IsUnipotentRadical.range_eq_bot`) and only the identity residue-field point.
  The projection to the specified quotient is then injective on residue-field points
  (`SpecialFibreQuotientData.ker_projectionPoints`) and surjective
  (`SpecialFibreQuotientData.projectionPoints_surjective`, over the perfect finite residue
  field). The points of `splitTorus 𝓀[F] J` are `J → 𝓀[F]ˣ` (`splitTorus.pointsEquiv` and
  `Scheme.ΓSpecIso`), with `(q - 1)^N` elements (`Nat.card_fun`, `Nat.card_units`).

## The theorem

`kpSplitTorusBuilding` installs `IsAffineHom T.X.hom` as the statement does and takes the
unique facet `x` (`ValuationBuildingData.nonempty_unique_buildingFacet_of_isTorus`).

1. `T(F)^0 = T(F)^1`. The inclusion `≤` is `ZeroSubgroupDatum.map_centralizerZero_le_zeroSubgroup`
   with `ZeroSubgroupDatum.zeroSubgroup_le_rationalCommonNormKernel`. For `≥`, `T(F)^1` lies in
   `D.parahoric x`, which is `T(F)^0` by `KPBuildingDatum.parahoric_eq_of_isTorus`.
2. `T(F)^0` is the kernel of the valuation homomorphism (`Plancherel.rationalCharacterValuation_ker`),
   hence normal, and `φ` is the composite of `QuotientGroup.quotientMulEquivOfEq`,
   `QuotientGroup.quotientKerEquivOfSurjective` (using the surjectivity above) and the
   coordinates `e`. The required formula `φ(t T(F)^0) = e(val t)` holds by definition.
3. The count `(q - 1)^N` is `KPBuildingDatum.card_finiteReductiveQuotientGroup_of_isSplitTorus`
   at every facet.

## Provenance

This is an internal composition of the Library results named above. It follows the arguments
recorded in the statement's Markdown: KP Lemma 2.5.7 for the valuation homomorphism, and
Axiom 4.1.20(3) forcing the neutral model to be the split `𝒪[F]`-torus, whose special fibre is
its own reductive quotient with `(q - 1)^N` points. The equality `T(F)^0 = T(F)^1` (the split case
of KP Lemma 2.5.18) is derived from the same integral torus and the parahoric identification, not
quoted, and the count is derived from the axioms, not quoted from KP.
