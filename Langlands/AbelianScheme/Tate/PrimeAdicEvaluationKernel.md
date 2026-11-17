# The kernel of evaluation on the prime-adic Tate module

This module proves lemmas about the existing actual integral prime-adic Tate module `PrimeAdic.Integral G T p` of a commutative group object `G` over a scheme. It defines nothing. All names are in the namespace `Langlands.GroupScheme.Tate.PrimeAdic`.

## Results

- `toSection_evaluation_add`: the section at level `p ^ n` is `p ^ m` times the section at level `p ^ (n + m)`. The proof iterates the published `evaluation_transition` and `toSection_transition_succ`. `toSection_evaluation_congr` changes the level index along an equality.
- `exists_smul_eq_of_evaluation_eq_zero`: if the level-`p ^ N` coordinate of `x` vanishes, then `x = p ^ N • y` for some `y`. The coordinate of `y` at level `p ^ i` is the section of `x` at level `p ^ (N + i)`. It is killed by `p ^ i` because `p ^ i` times it is the vanishing level-`p ^ N` section. Coherence follows from that of `x`, and `p ^ N • y = x` follows from `toSection_evaluation_add`.
- `card_quotient_range_map_eq`: let `f : G ⟶ G`. Suppose evaluation at level `p ^ N` is surjective and every `p ^ N`-multiple lies in the image of the Tate map `map T p f`. Then `Integral ⧸ range (map f)` and `Level (p ^ N) ⧸ range (levelMap f (p ^ N))` have the same cardinality. The map `x ↦ [evaluation N x]` is surjective. Its kernel is `range (map f)`: if `evaluation N x = levelMap f (evaluation N y)`, then `x - map f y` has vanishing level-`p ^ N` coordinate, so it is a `p ^ N`-multiple and lies in the image.
- `map_injective_of_ker_pow`: if every section in the kernel of `f` is killed by a positive integer `c`, then `map T p f` is injective. Suppose `map f x = 0` and the level-`p ^ m` coordinate of `x` is nonzero. Let `s` be the section of `x` at level `p ^ (m + c)`. Then `s` lies in the kernel of `f`, so `s ^ c = 1`. Also `s ^ (p ^ (m + c)) = 1`. Hence `s ^ gcd = 1`, and the gcd divides `p ^ c` because `p ^ e ∣ c` forces `e < c`. So `s ^ (p ^ c) = 1`, which makes the level-`p ^ m` coordinate zero, a contradiction.

## Provenance

Internal lemmas about the Library's prime-adic Tate module. They carry out the identification of `Ker(β)(l)` with `Coker(T_l β)` in Milne, *Abelian Varieties* (author revision 2022), proof of Proposition 12.9, p. 23. `exists_smul_eq_of_evaluation_eq_zero` is the prime-adic analogue of the published full-Tate result `FullEvaluationKernel`.
