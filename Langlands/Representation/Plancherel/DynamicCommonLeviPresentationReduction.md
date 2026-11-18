# Proof of the common-Levi presentation reduction

The theorem
`Langlands.Plancherel.DynamicCommonLeviPresentationReduction.dynamicCommonLeviPresentationReduction`
proves the published proposition
`Langlands.Plancherel.DynamicCommonLeviContinuation.DynamicCommonLeviPresentationReductionStatement.{u,uV,uW}`.
It keeps all three universes independent. It assumes nothing beyond the
statement's single premise, the complete
`Langlands.Plancherel.ConditionalParabolicIntertwiningStatement.{u,uV,uW}`
(Waldspurger 2003, IV.1.1, in its Library formulation). For every displayed
pair of compatible presentations, structural realizations `s`, `s'`, point
decompositions, compact open `K` with its two Iwasawa factorizations, and
admissible finite-length `A` on the actual common Levi `levi χ`, it gives the
actual `CommonLeviContinuationExists χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A`.

The Lean proof is an internal derived adapter. It applies the source theorem
once, then transports every conclusion by the identity-on-ambient-function
comparison maps already published in `DynamicCommonLeviPresentationComparison`,
`DynamicCommonLeviStructuralComparison`, `DynamicCommonLeviCompact` and
`DynamicCommonLeviContinuation`. It adds no analytic hypothesis.

## Generic equal-subgroup lemmas (section `Generic`)

For literal subgroup equalities `eP`, `eM`, `eU`, `eU'` of the ambient group, each
of these lemmas is proved by `subst`:

* `representationOfEq_isAdmissible'` and `representationOfEq_hasFiniteLength'`
  transport admissibility and finite length along `representationOfEq`. The
  representation is the same action on the same carrier.
* `squaredModulusCompatibility_ofEq` transports `SquaredModulusCompatibility`
  between the two pairs of decompositions.
* `quotientMeasureOfEq_rfl`: along `rfl`, `quotientMeasureOfEq` is the
  identity pushforward.
* `hasIntegral_ofEq_iff`: take two normalized induced vectors with the same
  ambient values. One has the transported representation and quotient measure,
  the other the target data. Then they satisfy `StandardIntertwining.HasIntegral`
  with the same represented value `Jf : G → A` simultaneously. After `subst`, the
  two vectors are equal by `Subtype.ext` and function extensionality.
* `domain_ofEq_eq_top_iff`: the full-domain equality `domain … = ⊤` holds for
  the transported data iff it holds for the target data.

## Core assembly (section `Core`)

Section `Core` fixes the statement's structural data, the source moduli `hδ`,
`hδ'` and the source squared-modulus identity `hsq`. It defines:

* `targetPictureComparison` is the identity of compact sections on the `ψ'` side,
  `compactPictureComparisonOfEq` along `parabolicPoints_eq χ ψ' s'`,
  `leviPoints_eq χ ψ s` and `radicalPoints_eq χ ψ' s'`. Both source
  decompositions have the Levi `parabolicLeviPointSubgroup p l`, so the `ψ`-side
  Levi equality identifies it with `levi χ`.
* `commonSquaredModulus` is the actual squared-modulus identity for
  `commonDecomposition χ ψ hψ` and `commonDecomposition χ ψ' hψ'`. It is
  `squaredModulusCompatibility_ofEq` applied to the source `hsq`.
* `mem_pairFullDomainRegion`: by `domain_ofEq_eq_top_iff`, source full convergence
  at the twist by `characterComparison χ ψ r s z` puts `z` in the actual
  `pairFullDomainRegion χ K hK ψ hψ ψ' A`. The source representation is
  `presentationRepresentation χ ψ s A` twisted by that character, and the source
  quotient measure is `presentationQuotientMeasure χ ψ s K ψ' s' hK`. The twisted
  source representation is definitionally `representationOfEq` of the actually
  twisted `A` (cf. `twistedRepresentation_eq`). The source quotient measure is by
  definition `quotientMeasureOfEq` of `pairQuotientMeasure K hK ψ ψ'`.
* `sourceOperator w hw` is the source `standardCompactOperator` at the
  presentation character `w`. It uses the pulled-back measures
  `presentationQuotientMeasure`, `presentationRadicalHaar` and
  `presentationIntersectionHaar`, their compatibility
  `presentationQuotientMeasure_isCompatible`, and the source `hsq`.
* `OperatorSquare` is a proposition stating that, for every `z` in the pair full
  domain and every source full-domain proof `hw` at `characterComparison χ ψ r s z`,
  `targetPictureComparison ∘ sourceOperator (cc z) hw ∘ (compactPictureComparison χ ψ hψ s h K A)⁻¹`
  equals `compactFamily … ⟨z, hz⟩` as a linear map.

### `operatorSquare`

The theorem `operatorSquare` proves `OperatorSquare`. Fix `z`, `hz`, `hw` and a compact
section `f`. Let `E` be the source restriction/extension
`unramifiedLeviInductionCompactEquiv` at `cc z`, and put
`f₀ := E⁻¹ (compactPictureComparison⁻¹ f)` and `f₁ := (compactEquiv χ … z A)⁻¹ f`.

1. `key`: `unramifiedInductionComparison … z f₀ = f₁`. By
   `LinearEquiv.eq_symm_apply` it suffices that `compactEquiv` maps the left side
   to `f`. The published compact restriction square
   `compactRestriction_comparison` at `f₀` turns this into
   `compactPictureComparison (E (E⁻¹ …)) = f`. That equation follows from
   `apply_symm_apply` twice.
2. `hf`: `f₀` and `f₁` have the same values at every ambient `x`, from
   `unramifiedInductionComparison_eval` and `key`.
3. `hint`: `pairFamily_spec`, with the actual `commonSquaredModulus`, gives the
   actual weak integral of `f₁` with represented value
   `eval (pairFamily … ⟨z, hz⟩ f₁)`. Then `hasIntegral_ofEq_iff`, applied with `hf`, turns
   it into the source weak integral of `f₀` with the same represented value.
4. `hop`: `StandardIntertwining.operator_eq` applied to `sourceToDomain … hw f₀`
   and `hint` shows that the source integral operator on `f₀` is that
   represented value.
5. For the compact sections, use `Subtype.ext` twice and function extensionality in `k : K`.
   `compactPictureComparisonOfEq_eval` removes the target comparison. By
   definition, `standardCompactOperator` evaluates as the source `operator` at
   `sourceToDomain … f₀`, and `compactFamily` evaluates as `pairFamily` at `f₁`.
   So `congrFun hop k` closes the goal.

### `continuationExists_of_source`

Let `S ⊆ D` be parameter sets of the source presentation characters. Assume
`S` is open and nonempty, the source standard integral is fully convergent at
every point of `D` (`hfull`), and `StandardCompactRationalOn` holds on `D`
(`hrat`). Given an `OperatorSquare`, `continuationExists_of_source` constructs
`CommonLeviContinuationExists`:

* `Ω := (characterComparison χ ψ r s) ⁻¹' S`. `Ω` is open because the character
  comparison is continuous. It is nonempty because `cc (cc.symm w) = w`.
  It lies in `pairFullDomainRegion` by `mem_pairFullDomainRegion` and `hfull`.
* Rationality: the restriction `hrat.restrict hSD` (`IsRationalOperatorOn.restrict`)
  gives rationality on `S`. Next, `isRationalOperatorOn_comparison_iff` pulls it
  back to `Ω`; this is the proved evaluation-algebra isomorphism of
  `DynamicCommonLeviPresentationComparison` and carries the single denominator
  together with its nonvanishing on the region. `IsRationalOperatorOn.precomp`
  then precomposes with the fixed linear map
  `(compactPictureComparison χ ψ hψ s h K A)⁻¹`, and
  `IsRationalOperatorOn.postcomp` postcomposes with `targetPictureComparison`.
  Neither map depends on the parameter. The denominator is still chosen before
  the input vector and is nonzero on all of `Ω`.
  Given `OperatorSquare`, the resulting family is
  `restrictedCompactFamily … (commonSquaredModulus …) A Ω hΩ` at every point of `Ω`.
* The existential is completed by `commonSquaredModulus`, `Ω`, its openness,
  nonemptiness, the inclusion `hΩ`, this rationality, and the published
  constructor `pairContinuation` applied with `D = Ω`.

## Main theorem

`dynamicCommonLeviPresentationReduction` introduces the premise `hIV` and all
binders of the target statement. It transports `hA` and `hfin` to
`presentationRepresentation χ ψ s A` with the two generic lemmas, then applies
`hIV` to these inputs:

* the displayed presentations, auxiliary opposite data, point decompositions,
  closedness, projection continuity, `K`, `hK` and the two source Iwasawa
  factorizations;
* the quotient measure `presentationQuotientMeasure χ ψ s K ψ' s' hK`;
* the Haar measures `presentationRadicalHaar χ K ψ' s' hK` and
  `presentationIntersectionHaar χ ψ s K ψ' s' hK`;
* the compatibility `presentationQuotientMeasure_isCompatible`;
* the representation `presentationRepresentation χ ψ s A`.

From the source conclusion it keeps the moduli `hδ`, `hδ'`, the squared-modulus
identity `hsq`, a cone parameter `R` with `C R` nonempty and open, full
convergence `hfull` on the twist-orbit saturation of `C R`, and rationality
`hrat` there. Two source conclusions are not used: openness of the orbit region,
and naturality of the full-source intertwiner under changes of representative
`W` in universe `uW`.

It finishes with `continuationExists_of_source`, where `S := C R` and
`D := unramifiedTwistOrbitSaturation … (C R)`. The inclusion is
`subset_unramifiedTwistOrbitSaturation`, and the operator square is
`operatorSquare`. The starting region `Ω` is the pullback of the cone `C R`
itself, not of its saturation. No denominator is claimed on the whole full
convergence domain.

## Scope

The proof supplies no IV.1.1 analysis; that remains with the source theorem's owner.
It claims nothing beyond the target conclusion: squared-modulus compatibility, the
nonempty open rational region inside the actual full convergence domain, and nonempty
`PairContinuation` data. Characteristic, splitness, quasisplitness and rank are
unrestricted, exactly as in the statement.
