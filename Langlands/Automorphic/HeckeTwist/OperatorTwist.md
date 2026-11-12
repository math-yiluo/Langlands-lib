# Twists of automorphic operator realizations by any Hecke character

Author: Worker 5136.

This internal module twists the Library's operator realizations
(`OperatorRealization F n`: subspaces of the stable automorphic functions that are
invariant under the whole operator algebra) by `χ ∘ det` for an arbitrary Hecke
character `χ`. Write `M_χ` for
`StableAutomorphicFunctions.heckeDeterminantMultiplier n χ` (module
`Langlands.Automorphic.HeckeTwist.StableMultiplier`).

## Operator realizations

- `OperatorRealization.heckeDeterminantTwist S χ`: the image of the space of `S`
  under `M_χ`. It is invariant under every operator `a`, because
  `a (M_χ f) = M_χ (a' f)` for the conjugated operator
  `a' = heckeDeterminantOperatorConjugation n χ a` (module
  `OperatorConjugation`), and `a' f` stays in `S`.
- `heckeDeterminantTwistEquiv`: `M_χ` restricted to a continuous linear
  equivalence from the space of `S` onto the space of the twist. The lemmas
  `heckeDeterminantTwistEquiv_val`, `_operatorAction`, `_finite`, `_compact` and
  `_differential` record its value and its intertwining properties. A finite or
  compact translation picks up the scalar `χ(det ·)`, and a differential
  operator `D(a)` corresponds to `D(heckeEnvelopingShift n χ a)`.
- `toContinuous_heckeDeterminantTwistEquiv` and
  `evaluate_heckeDeterminantTwistEquiv`: the continuous function of the image
  vector is the Library's `determinantMultiplier n χ` applied to the continuous
  function of the source vector, so its value at `g` is `χ(det g) f(g)`.
- `heckeDeterminantTwistSubrepresentationOrderIso`: the lattices of invariant
  subspaces of `S` and of its twist correspond, by the Library's
  `conjugatedSubrepresentationOrderIso` for the automorphism
  `heckeDeterminantOperatorConjugation n χ`.
- `heckeDeterminantTwist_isIrreducible_iff`: the twist is irreducible if and only
  if `S` is.
- `heckeDeterminantTwist_isCuspidal_iff` (when the adele quotient is compact):
  the twist is cuspidal if and only if `S` is. This uses the Library's
  `isCuspidal_determinantMultiplier_iff` and `IsCuspidal.determinantMultiplier`,
  which hold for every Hecke character.

## Cuspidal realizations

`CuspidalOperatorRealization.heckeDeterminantTwist S χ` bundles the twist of an
irreducible cuspidal realization `S` of `GL_{r+1}(𝔸_F)` as an irreducible
cuspidal realization.

Provenance: internal. This is the part of the Library module
`Langlands.Automorphic.OperatorDeterminantTwist` that this development needs,
with the finite-order hypothesis removed. The differential intertwining lemma is
shifted by `heckeEnvelopingShift n χ`. The Library's `DeterminantTwistEquations`
require an unshifted differential identity, and its predicate
`IsFiniteOrderDeterminantTwist` requires finite order, so the lemmas relating the
twist to them are not ported. The twist in this module is the
operation of Henniart (2000), §2.2, `Π ↦ (χ ∘ det) ⊗ Π`, realized on functions.
