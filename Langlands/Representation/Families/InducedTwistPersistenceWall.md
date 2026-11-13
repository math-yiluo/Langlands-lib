# Transport of an exponent across one rank-one wall

Author: Worker 5120.

This module proves `Langlands.InducedTwistPersistence.isGeneralizedEigencharacter_wall`.
It is the analytic core of one wall step in the persistence argument.

## Statement

Let `G` be connected reductive over a nonarchimedean local field, with the canonical
topology on `G(k)`. The data are:

- an actual parabolic `P₁ = M₁N₁` of `G`;
- two actual parabolics `Q₁ = L V₁` and `Q₁' = L V₁'` of `M₁` with the same Levi `L`;
- two actual parabolics `R` and `R'` of `G` with Levi `L`. On rational points they lie
  in `P₁`, they have the same Levi embedding as `Q₁` and `Q₁'`, and they satisfy
  `R ∩ M₁ = Q₁` and `R' ∩ M₁ = Q₁'` (hypotheses `hRP`, `hRL`, `hRQ` and the primed ones);
- a supplied adjunction `i^{M₁}_{Q₁} ⊣ r^{M₁}_{Q₁'}` at carrier universe `max u v`;
- a central `b_L : B ⟶ L`, a character `χ` of `B(k)`, and an admissible `Z`.

Assume three things:

- `r_{R'}(Z)` has finite length;
- `χ` is an exponent of `b_L` on `r_{R'}(Z)`;
- (`hirr`) `i^{M₁}_{Q₁}(C)` is irreducible for every irreducible subrepresentation `C` of
  `r_{R'}(Z)` on which `χ` is an exponent.

Then `χ` is an exponent of `b_L` on `r_R(Z)`.

## Proof

1. The published transitivity `leviParabolicTransitivity` gives `r_R ≅ r^{M₁}_{Q₁} ∘ r_{P₁}`
   and `r_{R'} ≅ r^{M₁}_{Q₁'} ∘ r_{P₁}`. Put `V = r_{P₁}(Z)` and `W' = r^{M₁}_{Q₁'}(V)`.
   Both are admissible (`arbitraryParabolicJacquetAdmissibility`).
2. `W' ≅ r_{R'}(Z)` has finite length and exponent `χ`.
   `exists_irreducible_sub_isGeneralizedEigencharacter` gives an irreducible `C ↪ W'` with
   exponent `χ`. By `hirr`, `i_{Q₁}(C)` is irreducible.
3. The adjunction turns `C ↪ W' = r_{Q₁'}(V)` into a nonzero map `φ : i_{Q₁}(C) → V`.
   It is injective, because its source is irreducible.
4. `i_{Q₁}(C)` is admissible: `C` is admissible as a subrepresentation of `W'`, and the
   published `leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement` applies
   with `arbitraryParabolicQuotientCompact`. Frobenius reciprocity
   (`isGeneralizedEigencharacter_jacquet_of_ne_zero_induction` applied to the identity of
   `i_{Q₁}(C)`) shows that `χ` is an exponent of `r_{Q₁}(i_{Q₁}(C))`.
5. The Jacquet functor preserves injections (`leviJacquetFunctor_map_injective`). So
   `r_{Q₁}(φ)` carries the exponent into `r_{Q₁}(V) ≅ r_R(Z)`.

## Provenance and boundary

This is the wall step of the second-adjointness route to Konno 2003, Theorem 4.2 (see
`InducedTwistQuotientPersistenceReduction`). The adjunction and `hirr` are hypotheses.
The rest uses published Library theorems. No unproved representation-theoretic statement
is imported.
