# Induction in stages with its explicit formula

Author: Worker 115. Module
`Langlands.Representation.Intertwining.LeviInductionStagesFormula`.

This module is supporting material for Renard VII.3.5 (ii)–(iii) (David Renard,
*Représentations des groupes réductifs p-adiques*, French version of 9 July 2026,
VII.3.5, printed pp.237–240 / PDF pp.243–246). Those statements read Renard's "natural
identification" `i_P^G(σ) ≃ i_Q^G(i_{P∩L}^L(σ))` through the formula
`f̃(g)(x) = δ_U(x)^{-1/2} f(x g)`. The published theorem `leviParabolicTransitivity`
(Renard VI.1.4) only asserts that some isomorphism exists. This module builds an
explicit isomorphism and proves its formula.

## Setting

- `P = MN` is a represented parabolic of `G` (`p, m, n`).
- `Q = LU` is a represented parabolic of `G` (`q, l, uQ`) with `P(F) ≤ Q(F)` (`hPQ`).
- `P_L = M N_L` is a represented parabolic of `L` (`pL, mL, nL`) with the same embedded
  Levi subgroup, `mL ≫ pL ≫ l ≫ q = m ≫ p` (`hM`), and `P_L(F) = L(F) ∩ P(F)` inside
  `G(F)` (`hPL`).

These are exactly the hypotheses of the published `LeviParabolicTransitivityStatement`.

## Results

- `leviInductionStagesIso hG`: a natural isomorphism of functors
  `leviInductionFunctor p m n ≅ leviInductionFunctor pL mL nL ⋙ leviInductionFunctor q l uQ`.
- `leviInductionStagesIso_eval`: for `f ∈ i_P^G(σ)`, `g ∈ G(F)` and `x ∈ L(F)`, the image
  `f̃` of `f` satisfies `f̃(g)(x) = δ_U(x)^{-1/2} • f(x g)`. Here `δ_U^{1/2}` is the unit
  `HaarModulus.closedHalfCharacter` of `Q(F)` acting on `U(F)`, evaluated at the image of
  `x`, and `x g` uses the embedding `rationalPoints.map (l ≫ q)`. The proof is `rfl`.
- `leviInductionStagesIso_eval'`: the same formula with the complex scalar `(c x)⁻¹`,
  where `c x` is the value of that unit in `ℂ`. This is the form used in
  `PQIntertwiningInnerLeviStatement` and `PQIntertwiningOuterLeviStatement`.
- `leviInductionStages_ext`: an element `F` of `i_Q^G(i_{P_L}^L(σ))` is determined by
  all the values `F(g)(x)`. So the `f̃` in the formula is unique.

## Construction

The construction repeats the induction half of the published reduction
`leviParabolicTransitivity_of_radical_decomposition`
(`Langlands.Representation.Exponents.LeviParabolicTransitivityReduction`). Here it is a
`def` with an explicit composite, so the formula is definitional. The two radical
identities it needs, `N_L(F) = L(F) ∩ N(F)` and `N(F) = (L(F) ∩ N(F)) U(F)`, come from the
published `nestedParabolicPointDecomposition`.

The composite has three parts.

1. `NestedInduction.iso` is normalized induction in stages for the literal subgroups of
   `G(F)`. It uses the half-character product `NestedParabolic.halfCharacterProduct` and
   the unimodularity of the unipotent radicals. On functions it is
   `f ↦ (g ↦ (x ↦ δ_U(x)^{-1/2} f(x g)))` (`NestedInduction.equiv_eval`, `rfl`).
2. `GroupTransport.inductionIso` transports the inner induction from the literal subgroup
   `P(F) ∩ L(F)` of `L(F)`'s image to the represented parabolic `P_L` of `L`, through the
   topological isomorphism `leviPointsEquiv q l`. On functions it is precomposition
   (`GroupTransport.inductionIsoApp_hom_eval`, `rfl`).
3. Pullback isomorphisms identify the Levi transports: an inverse-pullback cancellation
   and a triple-pullback identity using `hM`. On vectors they are the identity.

The private helpers `inversePullbackIso`, `pullbackTripleIso` and
`pointImage_composite_mem_iff` of the reduction file are restated here under the
namespace `LeviInductionStages`, because the originals are private.
