# M345.002: addVal_integerMap_eq_ramificationIndex_of_irreducible

The theorem `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension.addVal_integerMap_eq_ramificationIndex_of_irreducible` proves exactly the published target
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension.addVal_integerMap_eq_ramificationIndex_of_irreducibleStatement` from
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal.RestrictionStatements`.
Its declared result type is that Statement applied to `base target ha`.
It does not edit the statement or its imports.

## Mathematical content

For complete discrete valuation fields `K` and `L` with an extension of their
chosen valuations, and an irreducible element `a` (a uniformizer) of the
valuation ring of `K`, the normalized additive valuation of the image of `a` in
the valuation ring of `L` equals the ramification index
`e(𝔪_L | 𝔪_K)`, coerced to `ℕ∞`.

## Source

The source result is `addVal_integerMap_eq_ramificationIndex_of_irreducible` in
`LocalFieldTheory.DiscreteValuationField.ValuedExtension`, from
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationAddVal.lean`,
lines 132–138, at NYLL commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The target's paired Markdown gives the complete source statement correspondence.

## Telescope

The four universes remain independent. The complete common telescope is:

```lean
{K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
(base : CompleteDVF.{u,v} K) (target : CompleteDVF.{w,x} L)
[base.valuation.HasExtension target.valuation]
```

The remaining source binders are exactly `{a : base.valuationSubring} (ha : Irreducible a)`.
No finite-dimensionality or additional module hypothesis is introduced.
The chosen `CompleteDVF` projections, valuation subrings, maximal ideals and
canonical algebra from `Valuation.HasExtension` are the published ones.
The source M108.003 index and M108.005 map are used via their exact Mathlib bodies,
`Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal` and
`algebraMap base.valuationSubring target.valuationSubring`.

## Implemented proof

The proof is a single `exact` term. It specializes the already published generic theorem
`P2MW.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.HerbrandPortG3.addVal_algebraMap_irreducible_eq_ramificationIdx`
(module `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints`).
That theorem states: for discrete valuation rings `R` and `S` with an injective
algebra map `R → S` and an irreducible `π : R`,
`addVal S (algebraMap R S π) = ((maximalIdeal R).ramificationIdx' (maximalIdeal S) : ℕ∞)`.

1. Take `R := base.valuationSubring` and `S := target.valuationSubring`. Their
   ring and domain instances are Mathlib's instances on valuation subrings; the
   discrete-valuation-ring instance is Mathlib's
   `Valuation.valuationSubring_isDiscreteValuationRing`, found from the rank-one
   discreteness stored in each published `CompleteDVF` package (checked by
   instance synthesis in the pinned environment). The algebra `R → S` is Mathlib's
   `Valuation.HasExtension.instAlgebra_valuationSubring`, the same instance that
   the target statement uses.
2. The injectivity premise is
   `Valuation.HasExtension.algebraMap_injective (vK := base.valuation) (vA := target.valuation)`.
   It is stated for the `integer` subrings, which agree definitionally with the
   valuation subrings, as in Mathlib's own definition of
   `instAlgebra_valuationSubring` via `inferInstanceAs`.
3. The irreducibility premise is `ha`.
4. The conclusion of the generic theorem matches the target up to definitional
   unfolding: the published abbreviations `base.maximalIdeal` and
   `target.maximalIdeal` unfold to `IsLocalRing.maximalIdeal` of the respective
   valuation subrings, so `exact` closes the goal.

The generic theorem is itself proved by computing which powers of the maximal ideal of
`S` contain the extension of `𝔪_R = (π)`, using `addVal` of a uniformizer of `S`.
This route replaces the source's proof through M345.001 with direct reuse of an
existing Library theorem; it does not depend on any unpublished NYLL proof.

Every imported mathematical dependency is already in the Library or the pinned
Mathlib environment. The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Modifications and attribution

The modifications relative to the source are the `Langlands.NYLL` namespace prefix,
the explicit published `Statement` result type, focused imports, the two canonical
wrapper substitutions where present, and the proof changes described above.
The original Apache-2.0 copyright and author header is retained, with Worker 308's
modification record. The proof design is Worker 308's checked draft (Task 6248 draft
revision 1), verified and submitted unchanged in its Lean content by Worker 428.
The carried [LICENSE](../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged.
