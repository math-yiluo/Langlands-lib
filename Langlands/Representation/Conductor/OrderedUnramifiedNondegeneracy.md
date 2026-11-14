# Mirabolic nondegeneracy of norm-ordered products of unramified characters

Module `Langlands.Representation.Conductor.OrderedUnramifiedNondegeneracy`.

## Purpose

The proof of `OrderedUnramifiedWhittakerRealizationStatement` needs this fact: every
nonzero subrepresentation of a norm-ordered unramified principal series has nonzero
Whittaker coinvariants. Through `OrderedUnramifiedProductComparison` and
`OrderedUnramifiedTransport`, this reduces to a mirabolic statement about the
normalized product `χ_1 × ⋯ × χ_{n+1}` of rank-one unramified blocks. This module
proves that mirabolic statement from Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), Theorem 4.11, in the all-field form
`AllFieldBZ.Derivative.OrderedCuspidalProductNoDegenerateSubmodules`. That theorem
enters as a hypothesis `h411`. The module does not depend on how Theorem 4.11 is proved.

## Contents

- `nontrivial_coinvariants_rankCast`: rank transport `mirabolicRankCast` along an
  equality `N = M` does not change whether the full upper coinvariants (character
  `mirabolicUpperCharacter ψ`) are nonzero. The proof is `subst` followed by
  `mirabolicRankCast_refl`. It copies the lemma of the same name from the all-field port's
  `Whittaker.PadicMirabolicNondegeneracy`.
- `nontrivial_coinvariants_of_top T ψ N B hk`: if the top-order derivative
  `mirabolicDerivativeOfOrder T ψ N (N+1)` of a mirabolic representation `B` is
  nonzero, then the coinvariants of `B` are nonzero. These are taken for the mirabolic
  upper unipotent subgroup and the character
  `standardCharacter ψ N ∘ Mirabolic.upperUnipotentEquiv`. This is the forward
  direction of the port's `hasNonzeroDerivative_top_iff`, proved the same way:
  1. transport to rank `0` (`generalLinearRankCast`; nontriviality is kept by `subst`);
  2. rewrite with `mirabolicDerivativeOfOrder_top`;
  3. use the natural isomorphism `TopLocalization.mirabolicLocalizationIso` between the
     full upper coinvariants and the top mirabolic derivative;
  4. undo the rank transport (`nontrivial_coinvariants_rankCast`);
  5. identify `mirabolicUpperCharacter ψ.complex N` with the transported standard
     character (`entrywiseCharacter_eq_standardCharacter`).

  The port's version imports `RestrictionBridge` and the port's `LevelCalculus`. The
  latter does not yet build over all fields, so this module inlines the two short
  rank-transport facts it needs. It uses the field-independent Library lemma
  `Derivative.LevelCalculus.nontrivial_iff_of_iso`.
- `product hϖ n z`: the normalized product, over the singleton block shape `blocks n`,
  of the rank-one blocks `rankOneBlock hϖ (z i)` (from
  `OrderedUnramifiedRankOneBlocks`). It is formed with the local-field data `data F`
  of `OrderedUnramifiedProductComparison`.
- `nontrivial_coinvariants h411 n z hz ψ`: suppose the norms `‖z i‖` are weakly
  increasing (`hz : Monotone`). Then every nonzero subrepresentation `U` of the
  restriction of `product hϖ n z` to the mirabolic subgroup has nonzero coinvariants
  for `standardCharacter ψ n ∘ Mirabolic.upperUnipotentEquiv`. The hypothesis of
  Theorem 4.11 is that `χ_j ≇ ν χ_i` for `i < j`. This is
  `rankOneBlock_twist_ne`, applied to `‖z i‖ ≤ ‖z j‖`. Theorem 4.11 then gives a
  nonzero top derivative of `U`, and `nontrivial_coinvariants_of_top` converts it.
