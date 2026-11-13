# Uniqueness of integral-normalized intertwining operators

Author: Worker 115. Module
`Langlands.Representation.Intertwining.PQIntegralUniqueness`.

This module holds supporting lemmas for Renard VII.3.5 (ii)–(iii) (David Renard,
*Représentations des groupes réductifs p-adiques*, French version of 9 July 2026,
VII.3.4–VII.3.5, printed pp.235–240 / PDF pp.241–246). It formalizes the uniqueness
half of the VII.3.4 characterization, which Renard uses to identify operators in the
proof of VII.3.5. It does not use the unproved explicit integral statement
`PQIntegralIntertwiningOperatorStatement`.

## Results

Let `P = MN` and `Q = MU` be represented parabolics with the same embedded Levi
subgroup, `a : A → M` a split component, and `σ` a `PQ`-regular smooth representation
of `M(F)` (`IsPQRegular`).

- `intertwiner_eq_of_eval_one_eq`: two intertwining operators
  `J₁, J₂ : i_P^G(σ) → i_Q^G(σ)` are equal if `J₁(f)(1) = J₂(f)(1)` for every `f` in
  the boundary vanishing subspace `F̃^{<1̄}_{PQ}(σ)`
  (`boundaryVanishingSubfunctor` at the identity double coset).
- `integralIntertwiner_unique`: two operators satisfying `IsIntegralIntertwiner` for the
  same subgroup `V` and the same measure are equal.

## Proof

The published Frobenius reciprocity `leviFrobeniusReciprocity` (Renard VI.9.6) gives a
linear equivalence `F` from intertwiners `i_P^G(σ) → i_Q^G(σ)` to equivariant maps
`r_Q^G i_P^G(σ) → σ`. Its formula says that `F(J)` sends the Jacquet class of `f` to
`J(f)(1)`. Let `T ⊂ r_Q^G i_P^G(σ)` be the boundary support image at the identity double
coset, and `qT` the restriction of `F(J₁)` to `T`. The published extension lemma
`existsUnique_intertwining_extension` (used in `PQIntertwiningOperatorProof`) applies
because `IsPQRegular` is exactly its sum-of-kernels hypothesis. It gives a unique
equivariant `K` extending `qT`. Then `F(J₁) = K` holds trivially. Every vector of `T` is
the class of some `f ∈ F̃^{<1̄}_{PQ}(σ)`, and on such classes `F(J₂)` agrees with `F(J₁)`
by hypothesis. Hence `F(J₂) = K` as well. Injectivity of `F` gives `J₁ = J₂`.

For `integralIntertwiner_unique`, the second conjunct of `IsIntegralIntertwiner` gives
`ℓ(J₁(f)(1)) = ∫_V ℓ(f(v)) dv = ℓ(J₂(f)(1))` for every linear form `ℓ`. Linear forms
separate points of a complex vector space (`Module.forall_dual_apply_eq_zero_iff`), so
`J₁(f)(1) = J₂(f)(1)`, and the first lemma applies.
