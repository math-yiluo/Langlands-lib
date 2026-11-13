# Local-constant systems along an isomorphism of p-adic fields

Worker 5130, Task 5230. Internal derived infrastructure; no external source.

`PadicField.AbelianTransport.haarMeasure_scale` says that the Library's pushforward
of Haar measures along a field isomorphism commutes with positive scaling. It is
`FieldTransport.haarMeasure_scale` under the canonical topological and Borel
structures.

For `g : F ≃ₐ[ℚ_p] E` and an assignment `ε` on the common closure of `E`:

* `additiveCharacterMap L ψ` is `ConductorTransport.additiveCharacter` along
  `fieldEquiv L`, the inverse pullback `y ↦ ψ(g⁻¹ y)` on `σ(L)`.
* `haarMeasureMap L μ` is `AbelianTransport.haarMeasure` along `fieldEquiv L`, the
  pushforward.
* `transportAssignment F E g ε` is the assignment on `F` with
  `L ψ μ x ↦ ε σ(L) (additiveCharacterMap L ψ) (haarMeasureMap L μ) (virtualMap L x)`.
* `additiveRelation_transportAssignment` and
  `haarScalingRelation_transportAssignment` transport the additive and Haar-scaling
  laws. The second uses `degree_virtualMap`.
* `inductionRelation_transportAssignment` transports the induction law. It uses
  `virtualMap_induce`, preservation of degree zero, and
  `traceCharacter_additiveCharacterMap`: the trace character commutes with
  transport. That lemma comes from `mapFieldRingEquiv_symm_trace`, which is Mathlib's
  `Algebra.trace_eq_of_equiv_equiv` for the isomorphisms `M ≅ σ(M)` and `L ≅ σ(L)`.
  The Haar measure on `σ(L)` in the hypothesis is chosen as `haarMeasureMap L μL`.
* `fieldCharacterMap L χ` is `ConductorTransport.quasicharacter` along `fieldEquiv L`.
  `weilCharacter_transportFamily` shows that the transported family's Weil
  character of `χ`, precomposed with `subgroupWeilEquiv L`, is the Weil character of
  `fieldCharacterMap L χ`. Hence `virtualMap_characterClass_transportFamily` holds.
  `rankOneRelation_transportAssignment` then follows from the rank-one law at `σ(L)`
  and the Library's `AbelianTransport.abelianEpsilonExpression_eq`.
* `isSystem_transportAssignment`: if `ε` is a local-constant system on `E` for `eE`,
  then `transportAssignment F E g ε` is one on `F` for `transportFamily F E g eE`.
  Normalization comes from `transportFamily_normalizedReciprocity`.
