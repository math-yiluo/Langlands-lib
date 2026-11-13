# The two ends of the persistence argument

Author: Worker 5120.

This module proves three lemmas, in `Langlands.InducedTwistPersistence`, used at the two
ends of the gallery argument for `InducedTwistQuotientPersistenceStatement`. Throughout,
`H` is an affine group over a Hausdorff topological field, with the canonical topology on
`H(k)` and displayed local compactness and nonarchimedean-group hypotheses. `q : Q ⟶ H` is
an actual rational parabolic with rational Levi `lQ : L ⟶ Q` and geometric unipotent
radical `rQ`. `i_Q` and `r_Q` are the published `leviInductionFunctor` and
`leviJacquetFunctor`.

## Restriction of exponents

`isGeneralizedEigencharacter_of_leviJacquet_restrict`. Let `a : A ⟶ H` and `b_L : B ⟶ L`
be split components, and let `e : A(k) →* B(k)` satisfy
`(lQ ≫ q)(b_L(e t)) = a(t)`. If `χ` is an exponent of `b_L` on `r_Q(π)` for an admissible
`π`, then `χ ∘ e` is an exponent of `a` on `π`.

This is Renard VII.1.1 (ii), published as `normalizedJacquetExponent_restrict`. The proof
translates between the Levi-point form of the exponent and the published normalized
exponent with `isNormalizedJacquetExponent_iff_leviJacquet`, and converts the resulting
generalized weight back with `isGeneralizedEigencharacter_of_isGeneralizedWeight`.

## Exponents through Frobenius reciprocity

`isGeneralizedEigencharacter_jacquet_of_ne_zero_induction`. Let `H` be connected
reductive and `b_L` central. Let `X` be admissible and `Y` irreducible, in independent
carrier universes, with a nonzero intertwiner `f : X → i_Q(Y)`. Then every exponent of
`Y` on `b_L` is an exponent of `r_Q(X)`.

The published `leviFrobeniusReciprocity` turns `f` into a nonzero, hence surjective, map
`r_Q(X) → Y`. `r_Q(X)` is admissible (`arbitraryParabolicJacquetAdmissibility`).
`InducedTwistExclusion.isGeneralizedEigencharacter_of_surjective` lifts the exponent along
a surjection out of an admissible representation.

## Second adjointness at the start

`hom_mkQ_ne_zero`: the quotient map onto `X / S` is nonzero when `S ≠ ⊤`.

`exists_injective_oppositeJacquet_of_quotient`. Let `P = MN` and `P̄` be parabolics with
the same Levi `M`. Suppose an adjunction `i_P ⊣ r_P̄` is supplied, at carrier universe
`max u v`. Then for an irreducible `τ` of `M(k)` and every invariant subspace `S ≠ ⊤` of
`i_P(τ)`, there is an injective intertwiner `τ → r_P̄(i_P(τ)/S)`.

The published `exists_nonzero_oppositeJacquetMap` turns the nonzero quotient map into a
nonzero map `τ → r_P̄(i_P(τ)/S)`, raising the carrier universe as needed. A nonzero map
out of an irreducible representation is injective.

## Provenance and boundary

The adjunction is a hypothesis of the last lemma, not an assumption of the module. It is
supplied later from `LeviSecondAdjointnessStatement` (Bernstein's second adjointness),
which is a proof target, not a theorem. Everything else uses published Library theorems.
The module is an internal helper for the derived persistence argument (see
`InducedTwistQuotientPersistenceReduction`).
