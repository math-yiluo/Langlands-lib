# Descent of the facet Lie-weight sign formula from the maximal unramified extension

Module `Langlands.BruhatTits.IntegralModels.UnramifiedFacetSignDescent`.

## Overview

The main theorem `unramifiedFacetLieWeightSignFormula_of_descent` proves the third
conclusion of `UnramifiedFacetCommonTorusStatement`, the Lie-weight sign formula, for
all data of that statement. It takes two published but unproved Library statements as
hypotheses:

- `hI : UnramifiedFacetLieWeightSignStatement`, the sign formula over the ring of
  integers `O = fixedFieldIntegers F` of the maximal unramified extension
  `K = inertiaFixedField F`, for the apartment of `C`;
- `hII : UnramifiedDescendedApartmentTorusStatement`, the factorization
  `f ≫ C.i = (P.i)_K` of the base change of the torus inclusion of `B = P.toValuationBuildingData`
  through the torus of `C`.

The theorem does not prove the target statement and makes no claim about `hI`
or `hII`. The other declarations of the module are the steps of this descent.

## Content

### Generic statements (any coefficient square `R → A`, `K → L`)

Throughout, `R`, `A` are domains with fraction fields `K`, `L`, with the commuting
square of algebras used by the Library's `RelativeComponentModelData.baseChange`.

- `IntegralSplitTorusData.toIntegralTorusData` (definition): an
  `IntegralSplitTorusData` of the neutral model `D.neutral` of a model pair `D`, as
  `IntegralTorusData D S i`, with the same torus and inclusion. The generic
  identification is `underlyingTorusIso` of the given one. The simp lemmas
  `toIntegralTorusData_torus` and `toIntegralTorusData_inclusion`, and the lemmas
  `toIntegralTorusData_genericIso_hom` and `toIntegralTorusData_genericIso_inv`,
  record the fields.
- `SpecialFibreQuotientData.isReductiveQuotient_baseChange`: let `R`, `A` be local
  and `R → A` local. Assume the residue field extension is separable
  (`Algebra.IsSeparable`) and algebraic (`Algebra.IsAlgebraic`). If
  `Q.IsReductiveQuotient`, then `(Q.baseChange A L).IsReductiveQuotient`.
- `coefficientSquare_spec`: the two composites `Spec L → Spec R` agree.
- `comparisonGenericMap` (definition). Let `𝒯` be an integral torus of `D'` with
  generic torus `S₀`, let `ε : G_L ≅ H`, let `T'` be an integral torus of
  `(D'.baseChange A L).transport ε`, and let `f : (S₀)_L ⟶ S'`. The map goes from the
  generic fibre of the base change of `𝒯.torus` to `A` to the generic fibre of
  `T'.torus`. It is the composite of the coefficient-square comparison
  `Descent.squareComparison`, the base change of `𝒯.genericIso`, `f`, and the inverse
  of `T'.genericIso`.
- `comparisonGenericMap_comp_inclusion`: if
  `f ≫ i' = (i₀)_L ≫ ε.hom`, then the comparison generic map followed by the generic
  fibre of `T'.inclusion` is the generic fibre of the base-changed inclusion
  `𝒯.baseChangeInclusion A L`.
- `baseChange_genericCharacter_eq_of_comparisonGenericMap`: let
  `ρ : (𝒯.torus)_A ⟶ T'.torus` have generic fibre the comparison generic map. If the
  base change of an integral character `m` of `𝒯.torus` to `A` is `ρ ≫ ψ`, then the
  base change to `L` of the generic character of `m` is `f` followed by the generic
  character of `ψ`.
- `RelativeComponentModelHom.roots_eq_of_nonzeroLieImageWeights_eq`: for any sign
  function `σ` on generic characters, an identity of the form
  `nonzeroLieImageWeights = {χ ∈ relativeRoots | 0 ≤ σ((characterSpecialization)⁻¹ χ)}`
  is the root identity
  `roots (reductiveImageTorusMap) = {χ ∈ roots (quotientTorusInclusion) | 0 ≤ σ(χ^gen)}`,
  where `χ^gen` is the generic character of the integral character with special
  character `χ`.
- `exists_torusHom_of_transport`: let `A` be a Henselian discrete valuation ring
  with separably closed residue field, and let `A'` be an
  `IntegralSplitTorusData` of the neutral model of `(D'.baseChange A L).transport ε`
  whose inclusion is a closed subgroup. If `f ≫ i' = (i₀)_L ≫ ε.hom` and `𝒯.torus`
  is split, there is `ρ : (𝒯.torus)_A ⟶ A'.torus` with
  `ρ ≫ A'.inclusion = 𝒯.baseChangeInclusion A L`. Its generic fibre is the
  comparison generic map for `A'.toIntegralTorusData`.
- `RelativeComponentModelHom.roots_of_transport_comparisonGenericMap`: in the setting
  of `exists_torusHom_of_transport`, with `R`, `R → A` local and the quotient of `Q`
  locally of finite type, let `σ χ = σ' ψ` whenever
  `χ_L = f ≫ ψ` for generic characters `χ` of `S₀` and `ψ` of `S'`. If the root
  identity holds for `A'.toIntegralTorusData`, the transported base change of `φ` and
  the transported base change of `Q` with the sign function `σ'`, then it holds for
  `𝒯`, `φ`, `Q` with the sign function `σ`.

### The maximal unramified extension

The module fixes the algebra `𝒪[F] → O` and its scalar tower and local homomorphism
properties as local instances. They are the instances of the Library's
`IntegralModel.baseChangeUnramified`.

- `unramifiedResidueAlgebra_eq`: the residue field algebra induced by `𝒪[F] → O` is
  the algebra given by the published residue map `residueToFixedField F`.
- `unramifiedResidue_isAlgebraic` and `unramifiedResidue_isSeparable`: the residue
  field of `O` is algebraic and separable over the residue field of `𝒪[F]`.
- `integralPoints_transport_innerIso_inv`: if the integral points of a model `M` over
  `O` are `E(0) ∩ G(K)_{g • Y}` (pointwise fixer of the `g`-translate of
  `C.apartmentMap '' Y`), then after transport along the inner automorphism
  `Int(g⁻¹)` they are `E(0) ∩ G(K)_Y`.
- `baseChange_innerIso_hom_comp_innerIso_inv`: the base change of `Int(g)` followed by
  `Int(g_K⁻¹)` is the identity, where `g_K = rationalExtend g`.
- `integralPoints_transport_baseChangeUnramified`: in the setting of the target
  statement, assume `M.baseChangeUnramified` has integral points
  `E(0) ∩ G(K)_{e(g • A(Fa))}`. Then its transport along `Int(g_K⁻¹)` has integral
  points `E(0) ∩ G(K)_{C.apartmentMap(a(Fa))}`.
- `comp_eq_baseChange_comp_innerIso_inv`: if `f ≫ C.i = (B.i)_K`, then
  `f ≫ C.i = (B.i ≫ Int(g))_K ≫ Int(g_K⁻¹)`.
- `roots_transport_of_unramifiedSign`: assume `hI`, the facet hypothesis on `a`, a face
  relation `Fa ≺ Fa'`, and the integral points of the transported base changes of `D`
  and `D'` as above. Let `A'` be an `IntegralSplitTorusData` of the transported base
  change of `D'` with generic torus `C.S` included by `C.i`. Then for `x ∈ Fa` and `v`
  with `[v] +ᵥ x ∈ Fa'`, the root identity holds for `A'` with the sign function
  `ψ ↦ ⟨ψ, f_* v⟩`. Here `f_* = descendedCocharacterMap B C f`.
- `hasApartmentLieWeightSignFormula_of_transport`: assume `hI`, `f` with
  `f ≫ C.i = (B.i)_K`, the hypotheses on `e`, `a`, the face relation, and the
  transported integral points. Then
  `φ.HasApartmentLieWeightSignFormula B Q 𝒯 hT Fa Fa'` holds for every split integral
  torus `𝒯` of `D'` with generic torus `B.S` included by `B.i ≫ Int(g)`, provided
  `Q.IsReductiveQuotient`.
- `unramifiedFacetLieWeightSignFormula_of_descent`: the main theorem. Its binders are
  those of `UnramifiedFacetCommonTorusStatement`, in the same order. It omits the
  smoothness hypotheses on `D`, `D'` and the torus clause on `𝒯`, which it does not
  need. Given `hI`, `hII`, `Q.IsReductiveQuotient` and `hT : IsSplitTorus 𝒯.torus.toGrp`,
  it concludes `φ.HasApartmentLieWeightSignFormula P.toValuationBuildingData Q 𝒯 hT Fa Fa'`.

## Proofs

`isReductiveQuotient_baseChange`. The neutral special fibre is smooth, affine and
connected; connectedness comes from `neutral_connectedFibres` through
`hasConnectedSpecialFibre_of_hasConnectedFibres`. The radical part follows from the
Library proof `separableAlgebraicUnipotentRadical` (CGP Proposition 1.1.9(1)) and
`IsUnipotentRadical.comp_iso`, applied to the special-fibre square isomorphism
`specialFibreSquareIso`. The quotient part follows from
`RelativeRoot.IsFppfQuotient.baseChange`, `IsFppfQuotient.comapIso`,
`SubgroupFunctor.range_comp_iso` and `SubgroupFunctor.range_baseChangeHom`.
Connected reductivity of the quotient follows from
`IsConnectedReductive.baseChange_of_algebraicExtension`.

`comparisonGenericMap_comp_inclusion`. Compose both sides with the generic
identification of the transported neutral model, which is
`D'.neutral.baseChangeGenericIso A L ≫ ε`. On the left, `T'.generic_comm`, the
cancellation of `T'.genericIso` and the hypothesis on `f` apply. On the right, the
Library lemma `baseChangeGenericIso_eq_square` writes the generic identification as
the square comparison followed by the base change of `D'.neutral.genericIso`.
`squareComparison_naturality` and `𝒯.generic_comm` then finish.

`baseChange_genericCharacter_eq_of_comparisonGenericMap`. Use the tower lemma
`Descent.characterBaseChange_tower` twice, once for each route around the coefficient
square through the common composite `Spec L → Spec R`. Use the hypothesis on `m`
and `characterLattice.baseChange_precomp`. The comparison generic map unfolds into the
two pullback comparisons that make up `squareComparison`, and these cancel.

`roots_eq_of_nonzeroLieImageWeights_eq`. Rewrite with
`nonzeroLieImageWeights_quotientTorusInclusion`. `relativeRoots` is `roots`, and
the inverse of `characterSpecialization` is the generic character of the inverse
special character, by definition.

`exists_torusHom_of_transport`. Apply the published `exists_torusHom_of_generic_factor`
to the neutral model of the transported base change, the split tori `(𝒯.torus)_A` and
`A'.torus`, and the comparison generic map. The required generic factorization is
`comparisonGenericMap_comp_inclusion`.

`roots_of_transport_comparisonGenericMap`. Take `ρ` from
`exists_torusHom_of_transport`. The published
`roots_reductiveImageTorusMap_of_baseChange_transport` applies with the sign functions
`m ↦ σ(m^gen)` and `ψ ↦ σ'(ψ^gen)`. Their compatibility is
`baseChange_genericCharacter_eq_of_comparisonGenericMap` with the hypothesis on
`σ`, `σ'`.

`unramifiedResidueAlgebra_eq`: equality of algebra maps on residues of integers,
which holds by definition (`IsLocalRing.residue_surjective`).
`unramifiedResidue_isAlgebraic`: transport of the algebraicity part of
`fixedFieldResidueIsAlgClosure F` along this equality.
`unramifiedResidue_isSeparable`: the residue field of `𝒪[F]` is finite, hence perfect,
and an algebraic extension of a perfect field is separable.

`integralPoints_transport_innerIso_inv`. Transport maps integral points by
`rationalPoints.map Int(g⁻¹)`, which is conjugation by `g⁻¹`
(`rationalPoints_map_innerIso`). Conjugation is injective, so it maps the
intersection to the intersection (`Subgroup.map_inf_eq`). It preserves `E(0)` because
`E(0)` is normal (`UnramifiedZeroDatum.normal_zeroPoints`). It maps the fixer of
`g • Y` to the fixer of `Y` by `pointwiseFixer_smul_image_map_conj`.

`baseChange_innerIso_hom_comp_innerIso_inv`: `baseChange_innerIso_hom`,
`innerIso_inv_hom` and `rationalExtend_eq_baseChangeBasePoint`.
`integralPoints_transport_baseChangeUnramified`: rewrite
`e '' (g • A(Fa))` as `g_K • C.apartmentMap '' (a '' Fa)` using the equivariance of
`e` and `e ∘ B.apartmentMap = C.apartmentMap ∘ a`, then apply
`integralPoints_transport_innerIso_inv`.
`comp_eq_baseChange_comp_innerIso_inv`: functoriality of base change and
`baseChange_innerIso_hom_comp_innerIso_inv`.

`roots_transport_of_unramifiedSign`. The accepted lemma `exists_isFaceOf_image`
(`AffineFacetIncidenceTransfer`) gives facets `facet(a x) ≺ facet(a x₁)` of the
apartment of `C` containing `a(Fa)` and `a(Fa')`. The accepted lemma
`descendedApartment_map_vadd` (`DescendedApartmentLinearPart`) gives
`a([v] +ᵥ x) = [f_* v] +ᵥ a x`, so `[f_* v] +ᵥ a x ∈ a(Fa')`. Apply `hI` with
`Ω = a(Fa)`, `Ω' = a(Fa')` to the transported base changes of `D`, `D'`, `φ`, `Q`
and the torus `A'.toIntegralTorusData`. The neutral models are smooth by
`isSmooth_baseChange`, and `Q` stays a reductive quotient by
`isReductiveQuotient_baseChange` and `isReductiveQuotient_transport_iff`. Convert the
result with `roots_eq_of_nonzeroLieImageWeights_eq`.

`hasApartmentLieWeightSignFormula_of_transport`. The ring `O` is a Henselian discrete
valuation ring with algebraically closed residue field (Library:
`fixedFieldIntegersIsDVR_of_valuesFromBase`, `fixedFieldIntegersIsHenselian`,
`fixedFieldResidueIsAlgClosure`). The quotient of `Q` is smooth, hence locally of
finite type. The Library's `exists_unramifiedZeroFixerIntegralSplitTorusData` gives a
closed `A'` in the transported base change of `D'`. By
`hasApartmentLieWeightSignFormula_iff_roots` the goal is a root identity for each
`x`, `v`. It follows from `roots_of_transport_comparisonGenericMap` with
`σ χ = ⟨χ, v⟩` and `σ' ψ = ⟨ψ, f_* v⟩`. Their compatibility is
`eval_descendedCocharacterMap`, and the root identity for `A'` is
`roots_transport_of_unramifiedSign`. The required generic factorization is
`comp_eq_baseChange_comp_innerIso_inv`.

`unramifiedFacetLieWeightSignFormula_of_descent`. Obtain `f` from `hII`. The
integral-point hypotheses `hD` and `hD'`, rewritten with `hFc` and `hFc'`, give the
transported integral points through `integralPoints_transport_baseChangeUnramified`.
Then apply `hasApartmentLieWeightSignFormula_of_transport`.

## Provenance

Internal infrastructure for the proof of
`Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement`
(Kaletha–Prasad, *Bruhat–Tits theory: a new approach*, Axiom 4.1.22(3) for the
descended building, with the references given in that statement's documentation).
The module proves the sign formula by descent. It takes the formula over the
integers of the maximal unramified extension for the apartment torus of `C`
(hypothesis `hI`) and the inclusion `S_K ⊆ C.S` (hypothesis `hII`). The transport by
`Int(g⁻¹)` reduces the translated apartment `g • A(S)` to the apartment itself. The
Lean route reduces everything to the root form of the sign formula. It uses only
Library declarations and the accepted modules `FacetRootSignDescent`,
`AffineFacetIncidenceTransfer` and `DescendedApartmentLinearPart`. The literature
results it uses are proved in the Library: `separableAlgebraicUnipotentRadical`
(documented there as CGP Proposition 1.1.9(1), separable algebraic case) and
`smoothHomExtension` (KP Corollary 2.10.10, used through
`exists_torusHom_of_generic_factor`). It makes no other assertion from the
literature.
