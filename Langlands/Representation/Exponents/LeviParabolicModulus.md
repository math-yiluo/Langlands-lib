# Modular characters of represented parabolics

Lean module: `Langlands.Representation.Exponents.LeviParabolicModulus`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

Author: Worker 937. Planned with Worker 1402 for the second adjointness proof of Renard
VI.9.6 (task c0fa1878), where it supplies the modulus inputs of the integral duality
`(i τ)~ ≅ i(τ~)` (`Aubert/General/CompactQuotientNaturalDuality.lean`).

## Source

Renard 2026, *Représentations des groupes réductifs p-adiques*, V.5.4 "Calculs de fonctions
modulaires" (printed pp.126–127, PDF pp.132–133). The Proposition there states that `G` is
unimodular. The Lemma states that, for a parabolic `P = MN` and `m ∈ M`,
`δ_{P\G}(m) = δ_G(m)/δ_P(m) = δ_P(m)⁻¹ = δ_N(m)⁻¹`. The Lemma is stated for the minimal
parabolic `P_∅`; Renard notes that the Cartan decomposition of `M` gives it for `m ∈ M`.

This module does not reproduce Renard's proofs, which use the Cartan and Iwahori
decompositions. It takes unimodularity of reductive rational points from the open Library
statement `RationalReductiveUnimodularityStatement` and computes the modular character of
`P(F)` with the generic semidirect-product formula
`IsSemidirectDecomposition.modularCharacter_eq_restrictCharacter_of_unimodular`
(`Aubert/General/SemidirectModularCharacter.lean`). That formula says that if `M` and `U`
are unimodular, then the modular character of `P = M ⋉ U` at `q` is the Haar modulus of
conjugation by `q` on `U`. This is Renard's `δ_P = δ_N` for all of `P`, with the
Library's orientation of the normalizer character.

## Setting

`k` is a Hausdorff nonarchimedean local field. `G` is an affine group scheme over `k` whose
rational points `rationalPoints G` carry `RationalPointFamily.pointTopology` and are locally
compact and nonarchimedean. `p : P ⟶ G` is a represented parabolic with rational Levi
`l : M ⟶ P`, geometric unipotent radical `r : U ⟶ P` and isomorphic multiplication map
`hmul`. The literal images are `pointImage p`, `pointImage (l ≫ p)` and
`pointImage (r ≫ p)`, with the semidirect decomposition
`isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul`. `M(F)` has the
topology `leviPointTopology l hl`.

## Declarations

- `rationalPoints_modularCharacter_eq_one hUnimod hStandard hG g`: for connected reductive
  `G`, `Measure.modularCharacter g = 1` for every `g ∈ G(F)`. It applies
  `RationalReductiveUnimodularityStatement` to `G`. The Hausdorff instance it needs is
  `rationalPoint_t2Space`.

- `modularCharacter_pointImage_of_leviUnimodular hG p l r hp hl hr hmul hM`: if
  `Measure.modularCharacter m = 1` for every `m ∈ M(F)` (topology `leviPointTopology l hl`),
  then for every `q ∈ pointImage p`

  `Measure.modularCharacter q = HaarModulus.closedRestrictCharacter (pointImage (r ≫ p)) _ (pointImage p) _ q`.

  This is exactly the hypothesis `hδ` of
  `exists_isNaturalIntegralDuality_of_compactSpace` for this decomposition.

- `modularCharacter_pointImage_of_unimodularity hUnimod hStandard hG p l r hp hl hr hmul`:
  the same conclusion with `hM` discharged by `RationalReductiveUnimodularityStatement` for
  the connected reductive Levi `M` (`hl.isConnectedReductive`).

## Proof

The proof of `modularCharacter_pointImage_of_leviUnimodular` follows the Library's
`modularCharacter_of_presentation` (`Exponents/ParabolicPresentationUnitarity.lean`) but
needs no root presentation:

1. `G(F)` is Hausdorff (`rationalPoint_t2Space`) and second countable
   (`RationalPointFamily.reductiveRationalPoint_secondCountable`; this uses that `G` is
   connected reductive). The images of `p`, `r ≫ p` and `l ≫ p` are closed
   (`isClosed_pointImage`, `isClosed_pointImage_comp`, `isClosed_leviPoints`), hence locally
   compact.
2. `leviPointsEquiv p l hp hl : M(F) ≃ₜ* pointImage (l ≫ p)` and
   `modularCharacter_continuousMulEquiv` carry `hM` to the literal Levi image.
3. `pointImage (r ≫ p)` has trivial conjugation modulus on itself
   (`isUnimodularModulus_pointImage_radical`).
4. The Levi projection is continuous (`continuous_projection_pointImage`). The semidirect
   formula then gives the claim, and `HaarModulus.closedRestrictCharacter_eq` rewrites it
   to the closed-subgroup form.

`modularCharacter_pointImage_of_unimodularity` gives `M(F)` the instances required by
`RationalReductiveUnimodularityStatement`: affine structure morphism from
`hl.isConnectedReductive`, Hausdorffness, `leviPoints_locallyCompactSpace` and
`leviPoints_nonarchimedeanGroup`. It then applies the statement to `M`.

## Scope

These are conditional helpers. `RationalReductiveUnimodularityStatement` (and
`StandardCocharacterStatement`, which it takes as a premise) are open Library statements.
The Library reduces the first to structural inputs in
`Aubert/General/RationalReductiveUnimodularityReductionProof.lean`. Nothing here proves
`LeviSecondAdjointnessStatement`.

## Checks

`lean_check` over Library commit 6f75b7b3 (environment `3b864ddf`): diagnostic 4cc63077
(lake build), 0 errors and 0 warnings. `modularCharacter_pointImage_of_unimodularity` is a
theorem with universe parameter `u` and axioms `propext`, `Classical.choice`, `Quot.sound`.
