# Proof of the noetherian seesaw for line bundles on a flat proper family

`Langlands.AlgebraicGeometry.Picard.noetherianLineBundleSeesaw` proves the published
proposition `Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawStatement.{u}` from
module `Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawStatement`.

## Route

The proof applies the ported Anthropic FLT theorem
`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper`
(module
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper`)
to the same data `c`, `hH0`, `t`, `M`, `M'`. Its binders and hypotheses are those of the
statement. Two translations between Library language and the language of the port remain:

1. **Hypotheses.** The lemma `isInvertible_of_isLocallyFreeRankOne` turns the Library
   predicate `IsLocallyFreeRankOne M` (local trivialisations `M.restrict U.ι ≅ unit`) into the
   ported predicate `Scheme.Modules.IsInvertible M` (local trivialisations
   `(Scheme.Modules.pullback U.ι).obj M ≅ unit`). It composes each trivialisation with the
   inverse of the component at `M` of Mathlib's
   `Scheme.Modules.restrictFunctorIsoPullback U.ι : restrictFunctor U.ι ≅ pullback U.ι`.
2. **Conclusion.** The ported theorem gives `Z`, `ι`, the closed-immersion property and, for
   every `ψ : T' ⟶ T`, an equivalence between factoring through `ι` and
   `Scheme.Modules.LocallyIsoOver p N N'`, where `p` is the projection to `T'` and `N`, `N'`
   are the pullbacks of `M`, `M'`. After rewriting with this equivalence and unfolding
   `LocallyIsoOver`, both sides quantify over `τ` and an open `U ∋ τ` in the same way. For each
   `U`, an isomorphism of the restrictions along `(p ⁻¹ᵁ U).ι` and an isomorphism of the
   pullbacks along `(p ⁻¹ᵁ U).ι` are converted into each other by conjugating with the
   components of `restrictFunctorIsoPullback (p ⁻¹ᵁ U).ι` at `N` and `N'`.

No other mathematics is done in this file; all the cohomological content (coherence and base
change of `H^0` for flat proper families, the closed condition for geometrically integral
fibres) is in the ported FLT modules, whose Markdown files describe their sources and the
Mathlib drift patches applied to them.

## Declarations

- `isInvertible_of_isLocallyFreeRankOne`: the hypothesis translation above.
- `noetherianLineBundleSeesaw : NoetherianLineBundleSeesawStatement.{u}`: the theorem.

`lean_check` reports only the axioms `propext`, `Classical.choice` and `Quot.sound` for
`noetherianLineBundleSeesaw`, including everything it uses from the ported FLT modules.

## Provenance

This file is not a port. It was written for the task proving `NoetherianLineBundleSeesawStatement` and
contains no FLT text. It imports the published statement module and the ported FLT theorem module named
above. The ported modules come from the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`, Apache License 2.0, licence files in
`licenses/Anthropic-FLT/`).
