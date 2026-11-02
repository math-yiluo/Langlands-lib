# Ordinary module descent along a flat surjection

This internal construction uses the Library's actual ordinary module pullback and
pushforward functors. For arbitrary schemes `X` and `Y` in universe `u` and an
actual morphism `p : X ⟶ Y`, `modulePullbackDescentComonad p` is the comonad on
`X.Modules` of `Scheme.Modules.pullbackPushforwardAdjunction p`. Its coalgebras
are the Eilenberg–Moore coalgebras for that adjunction. The construction changes
neither the module categories nor the underlying scheme morphism.

For every flat surjection `p`, the module proves that its ordinary pullback
reflects isomorphisms, is comonadic, and is faithful on module morphisms. Moreover,
the comparison functor for that specific pullback–pushforward adjunction is an
equivalence. Each coalgebra for the displayed comonad is isomorphic to the
comparison image of a module on `Y`. These conclusions cover all module sheaves,
without quasi-coherence, finiteness, affineness, or quasi-compactness hypotheses.
The schemes and modules may be empty, nonreduced, or nonnoetherian.

## Implemented argument

`faithfullyFlat_stalkMap` first proves faithful flatness of the map on stalks at
any point of `X` when `p` is flat. Flatness supplies a flat ring homomorphism on
stalks. The map is local because `p` is a morphism of locally ringed spaces;
Mathlib's `Module.FaithfullyFlat.of_flat_of_isLocalHom` then supplies faithful
flatness. Surjectivity is unnecessary for this intermediate lemma.

For `pullback_reflectsIsomorphisms_of_flat_surjective`, fix a morphism of modules
on `Y` whose pullback is an isomorphism. Above any point `y` of `Y`, choose a point
`x` of `X` using surjectivity. The Library's
`StalkPullback.pullbackStalkIso` identifies the stalk of the pulled-back morphism
with extension of scalars of its stalk at `y`. Mathlib's faithfully flat
scalar-extension functor reflects isomorphisms, so the original stalk morphism
is an isomorphism. The Library criterion
`Langlands.SchemeModule.isIso_iff_stalk_isIso` concludes that the module morphism
is an isomorphism.

`comonadicPullback_of_flat_surjective` applies Mathlib's Beck comonadicity theorem
`Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms` to the
actual adjunction. The module category has equalizers. The Library's
`flatPullbackExact` proves that flat pullback preserves finite limits, and hence
the required cosplit equalizers. Conservativity was proved above. The comparison
in `isEquivalence_modulePullbackComparison` is the one for the same actual
adjunction, with its specific comonad. Faithfulness follows by applying the
comparison functor's injectivity on morphisms, using extensionality of coalgebra
morphisms. Finally, `exists_module_of_pullbackCoalgebra` uses the equivalence's
object preimage and its isomorphism to the given coalgebra.

## Provenance and scope

This is a derived internal interface built from the existing Library stalk
comparison, stalk isomorphism criterion, and flat-pullback exactness, together
with Mathlib's faithfully flat scalar-extension and Beck theorems. It introduces
no external literature claim or extra axiom.

Its effectivity conclusion concerns coalgebras of the ordinary adjunction.
Comparison with full-slice pullback cocycles, descent of quasi-coherence, finite
presentation and relative flatness, coherent-family stack descent, and the
smooth scheme atlas remain separate obligations. In particular this module does
not prove `FieldCoherentStackAtlasStatement`.
