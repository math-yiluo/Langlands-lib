# Matching composition factors in length at most two

Module `Langlands.Representation.Filtration.LengthTwoMatching`, namespace
`Langlands.LengthTwo`.

This module proves the internal statement
`Langlands.LengthTwoFactorMatchingCriterion` of
`Langlands.Representation.Filtration.LengthTwoMatchingStatement`; the closed
proof is `lengthTwoFactorMatchingCriterion`. It is a helper for the proof of
`Langlands.CuspidalSupport.TwoBlockAssociatedCuspidalInductionFactorsTheorem`.
It contains no p-adic input. It isolates the lattice-theoretic part of
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), §2.16(1), the case `B.length = 2` of Theorem 2.9(a). There, the count is
the total length of the Jacquet modules along the Levi subgroups associated
with the given one. The precise abstract form below is our own (derived)
formulation of that argument. It is not quoted from the source.

All statements are for representations `ρ : Representation k G V` and
`σ : Representation k G W` of a monoid `G` over a field `k`, with carriers in
independent universes.

## Successive quotients and equivalences

- `LengthCriterionProof.quotientRep S T` is the quotient of the subrepresentation `T` by the preimage of
  `S` in `T`. For a filtration `s` of `Rep.of ρ`, `gradedRepresentation_ρ` states
  that the Library's graded piece `(s.gradedRepresentation i).ρ` is
  definitionally `LengthCriterionProof.quotientRep` of the steps `i` and `i + 1`.
- `comap f S` is the preimage of a subrepresentation under an intertwining map.
- `nonempty_gradedEquiv`: let `f : ρ → σ` be intertwining, and let `S, T` be
  subrepresentations of `ρ` and `S', T'` subrepresentations of `σ`. Suppose `f`
  maps `T` into `T'`, every vector of `T'` is the image of a vector of `T`, and for
  `v ∈ T` we have `f v ∈ S' ↔ v ∈ S`. Then `T/S` and `T'/S'` are equivalent
  representations. The proof descends `f` to the quotients (`Submodule.liftQ`) and
  checks that the descended map is bijective.
- `isIrreducible_of_equiv`: an equivalence of representations preserves
  irreducibility, via the associated `k[G]`-modules.
- `isIrreducible_gradedRep_of_covBy`: if `S ⋖ T` (nothing lies strictly between
  them), then `T/S` is irreducible. The quotient is nonzero. A subrepresentation
  `U` of `T/S` pulls back to a subrepresentation of `ρ` between `S` and `T`, which
  must be `S` or `T`, and so `U` is `⊥` or `⊤`.

## Filtrations

- `hasSimpleFactors_of_covBy`: a filtration whose consecutive steps are covering
  pairs has simple factors.
- `oneStep ρ` is the filtration `0 ⊆ ρ` of `Rep.of ρ`, and `twoStep K` is
  `0 ⊆ K ⊆ ρ`. `oneStep_hasSimpleFactors` and `twoStep_hasSimpleFactors` give
  simple factors when the steps are covering pairs.
- `transport φ s` moves a filtration of `Rep.of ρ` along an equivalence
  `φ : ρ ≃ σ`. Its steps are the preimages of the steps of `s` under `φ⁻¹`.
- `haveSameJordanHolderFactors_of_equiv`: if `ρ ≃ σ` and `Rep.of ρ` has a
  composition series `s`, then `Rep.of ρ` and `Rep.of σ` have the same
  Jordan–Hölder factors. The witness is `s`, its transport, and the identity
  permutation. Each graded equivalence comes from `nonempty_gradedEquiv` with
  `f = φ`.

## Counts

Let `μ : Subrepresentation ρ → ℕ` be strictly monotone with `μ ⊥ = 0`.

- `count_pos`: `μ S > 0` for `S ≠ ⊥`. `eq_bot_of_count_eq_zero` is the
  converse form.
- `covBy_of_count`: if `S < T` and `μ T ≤ μ S + 1`, then `S ⋖ T`.
- `exists_series`: if moreover `μ ⊤ ≤ 2` and `ρ ≠ 0`, then `Rep.of ρ` has a
  composition series. If some `K` lies strictly between `⊥` and `⊤`, then
  `μ K = 1`, `μ ⊤ = 2`, and `0 ⊆ K ⊆ ρ` works. Otherwise `⊥ ⋖ ⊤` and `0 ⊆ ρ`
  works.
- Small facts about nonzero intertwining maps `A`: the source is nonzero
  (`bot_ne_top_of_ne_zero`), `ker A ≠ ⊤`, and `range A ≠ ⊥`.

## Main theorem

`haveSameJordanHolderFactors_of_count_le_two` takes the following hypotheses:

- strictly monotone counts `μ` on the subrepresentations of `ρ` and `ν` on those
  of `σ`, vanishing at `⊥`, with `μ ⊤ ≤ 2` and `ν ⊤ ≤ 2`;
- nonzero intertwining maps `A : ρ → σ` and `A' : σ → ρ` with
  `μ ⊤ = μ (ker A) + ν (range A)` and `ν ⊤ = ν (ker A') + μ (range A')`;
- `hX`: if `μ S = 1` and `A` does not vanish on `S`, then `ρ ≃ σ`;
- `hY`: if `ν S' = 1` and `A'` does not vanish on `S'`, then `ρ ≃ σ`.

Its conclusion is
`HaveSameJordanHolderFactors (Rep.of ρ) (Rep.of σ)`.
`lengthTwoFactorMatchingCriterion` introduces the universally quantified data
of `LengthTwoFactorMatchingCriterion.{uK,uG,uV,uW}` and applies this theorem;
the hypotheses there are exactly the ones above, in the same order.

Proof.

1. If `ρ ≃ σ`, use `exists_series` and `haveSameJordanHolderFactors_of_equiv`.
2. Otherwise `hX` and `hY` say that `A` kills every count-one subrepresentation
   of `ρ`, and `A'` kills every count-one subrepresentation of `σ`.
3. `μ ⊤ = 2`. It is positive because `ρ ≠ 0`. If it were `1`, then `A` would
   kill `⊤`, contradicting `A ≠ 0`. Symmetrically, `ν ⊤ = 2`.
4. `range A ≠ ⊤`. Otherwise additivity gives `μ (ker A) = 0`, so `ker A = ⊥`.
   Then `A` is bijective, hence an equivalence. Symmetrically, `range A' ≠ ⊤`,
   using the inverse of the resulting equivalence.
5. Hence `ν (range A) = 1` and `μ (ker A) = 1`. Symmetrically,
   `μ (range A') = 1` and `ν (ker A') = 1`.
6. By step 2, `range A ≤ ker A'`. Both have count one, so strict monotonicity
   gives `range A = ker A'`. Likewise `range A' = ker A`.
7. The composition series are `0 ⊆ ker A ⊆ ρ` and `0 ⊆ ker A' ⊆ σ`. Their
   consecutive steps are covering pairs by `covBy_of_count`. The permutation is
   the swap of `0` and `1`:
   - `A` identifies `ρ / ker A` with `range A / 0 = ker A' / 0`;
   - `A'` identifies `σ / ker A'` with `ker A / 0`, and the inverse of that
     equivalence is used.

   Both identifications are instances of `nonempty_gradedEquiv`.

The analytic input, which is the instantiation of `μ`, `ν`, `A`, `A'`, `hX`
and `hY` for normalized parabolic inductions, lives in a separate module.
