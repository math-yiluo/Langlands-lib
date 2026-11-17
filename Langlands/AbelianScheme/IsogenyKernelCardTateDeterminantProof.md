# Proof: the `p`-adic size of the kernel of an isogeny

This module proves `Langlands.AbelianScheme.IsogenyKernelCardTateDeterminantStatement` as the theorem `Langlands.AbelianScheme.isogenyKernelCardTateDeterminant`. The helper `card_ker_levelMap` is in the namespace `Langlands.AbelianScheme.IsogenyKernelCardTateDeterminant`.

## Helper

`card_ker_levelMap`: for `f : G ⟶ G` and `n`, the kernel of the level map `levelMap T f n` and the subgroup of the kernel points `(GroupScheme.pointsHom f T).ker` killed by `n` have the same cardinality. Both consist of the sections `s` with `s ^ n = 1` and `s ≫ f = 1`. The proof writes the bijection explicitly.

## Proof of the theorem

Fix `k` algebraically closed, `A`, a prime `p` with `(p : k) ≠ 0` and an isogeny `α`. Write `T = Over.mk (𝟙 _)`, `f = groupHom α`, `φ = PrimeAdic.map T p f` (the integral Tate map) and `K` for the kernel of `α` on `k`-points.

1. The published `geometricPrimeAdicRank` makes the integral Tate module free of rank `2g`. `K` is finite by the published `IsIsogeny.finite_ker_pointsHom`, so every element of `K` is killed by `#K`. `map_injective_of_ker_pow` makes `φ` injective, and `det_ne_zero_of_injective` gives `det φ ≠ 0`.
2. Put `N = #K + v(det φ)`. The level group at `p ^ N` is finite: it has `(p ^ N) ^ (2g)` elements by the published `geometricTorsionRank`. Evaluation at level `p ^ N` is surjective by the published `evaluation_surjective_of_pow`, using `algClosedPointDivisibility`. By `pow_smul_mem_range`, every `p ^ N`-multiple lies in `range φ`.
3. The chain of equalities of `p`-adic norms:
   - `‖#K‖ = ‖#{x ∈ K | x ^ (p ^ N) = 1}‖` (`norm_card_eq_norm_card_ker_pow`, since `#K ≤ N`);
   - `= ‖#ker (levelMap f (p ^ N))‖` (`card_ker_levelMap`);
   - `= ‖#(Level ⧸ range (levelMap f (p ^ N)))‖` (`card_ker_eq_card_quotient_range`);
   - `= ‖#(Integral ⧸ range φ)‖` (`card_quotient_range_map_eq`);
   - `= ‖det φ‖` (`norm_card_quotient_range`);
   - `= ‖det V_p(α)‖`, because `V_p(α)` is the base change of `φ` and `LinearMap.det_baseChange` applies.

## Provenance

This is the chain `|#Ker β|_l = (#Ker(β)(l))^{-1} = (#Coker T_l β)^{-1} = |det T_l β|_l` in Milne, *Abelian Varieties* (author revision 2022), proof of Proposition 12.9, p. 23, for an isogeny, carried out with the Library's actual Tate modules. The route through a finite level `p ^ N` is internal.
