# Chevalley data with Lie relations from simple `SL₂`-data (`ChevalleyLieConstruction`)

Author: Worker 239.

Let `P : RootDatum J X Y` be reduced with finite `J`, and let `b` be a base. This module turns
integral `SL₂`-data for the simple roots (`S : SimpleRootData P b`) into integral Chevalley data
with Lie relations (`ChevalleyLieData P b`). To do so, it constructs divided-power root operators
for all roots and proves the Weyl conjugation formula and the Lie relations for them.

## Generic lemmas

- `map_mul_divExp_mul`: `g · divExp D s · g' = divExp (k ↦ g D_k g') s` for integral `g`, `g'`.
- `divExp_pow_smul`: `divExp (k ↦ z^k • D_k) s = divExp D (z s)`.
- `IsDividedPowerFamily.conj`: conjugation by mutually inverse integral matrices preserves
  divided-power families.
- `map_conj_ne_zero_rat`: conjugation by an integral matrix with an integral left inverse maps
  nonzero rational matrices to nonzero matrices.
- `reflectionPerm_self_not_mem`: the negative `s_i α_i = −α_i` of a simple root is not a simple
  root.

## Families of root operators

`S.IsRootOp j D` says that `D : ℕ → Matrix (Fin S.n) (Fin S.n) ℤ` is a family of root operators
of the root `j`. It has four fields:

- `dp`: `D` is a divided-power family;
- `isWtHom`: `D k` has weight `k • α_j`;
- `prim`: `D 1` is nonzero modulo every prime;
- `mem`: `D 1`, viewed over `ℚ`, lies in `S.toLieGens.lieSpan`.

- `isRootOp_E`, `isRootOp_F`: `E i` is a family for `α_i`, and `F i` is one for `−α_i`.
- `IsRootOp.conj`: conjugating by mutually inverse integral matrices `g`, `g'` gives a family
  for the root `f α_j`. Here `g` and `g'` must move weights by an automorphism `f` and its
  inverse, and conjugation by them must preserve `lieSpan`. Primitivity is preserved by
  `map_conj_ne_zero`.
- `IsRootOp.weylMat`: conjugation by `weylMat i` gives a family for `s_i α_j`.
- `wordOp w i`: the conjugate `n_w E_i n_w⁻¹` by `wordMat w`. `isRootOp_wordOp`: it is a family
  for every root `j` with `α_j = weylWord P b w α_i`.

## Uniqueness up to sign

- `IsRootOp.exists_eq_smul`: the weight-`α_j` component of `lieSpan` is the line of `D 1`. By
  `exists_line_of_root` it is a line, and `D 1` is a nonzero element of it.
- `IsRootOp.exists_eq_pow_smul`: two families `D`, `D'` for the same root satisfy
  `D' k = ε^k • D k` with `ε = ±1`. First `D' 1 = q • D 1` over `ℚ`, and since both are
  primitive, `q = ε = ±1` (`eq_one_or_eq_neg_one_of_map_eq_smul`). Then
  `k! • D' k = (D' 1)^k = ε^k (D 1)^k = ε^k k! • D k` (`IsDividedPowerFamily.pow_one`), and
  `k!` is cancelled.
- `exists_root_of_isWtHom`: every nonzero homogeneous element of `lieSpan` of nonzero weight
  `μ` has a root as weight. Apply the minimal-height argument `mem_range_root_of_weylStable` to
  the set of nonzero weights of nonzero homogeneous elements of `lieSpan`. It is stable under
  the simple reflections (`weylMat_conj_mem`, `isWtHom_weylMat_conj`), its elements have
  coefficients of constant sign (`exists_coeff_of_isWtHom`), and it meets the multiples of a
  simple root only at `±α_i` (`eq_one_or_eq_neg_one_of_isWtHom`).

## The root operators of all roots

- `rootOp j`: `E i` if `j` is a simple root `i`; `F i` if `j = s_i i` is the negative of a
  simple root `i`; otherwise `wordOp w i` for a choice of `w`, `i` with
  `α_j = weylWord P b w α_i` (`exists_weylWord_root`).
- `isRootOp_rootOp`, `rootOp_simple`, `rootOp_reflectionPerm_self`: these are families of root
  operators, and they agree with `E i` and `F i` on simple roots and their negatives.
- `weyl_conj_rootOp`: for every simple root `i` and root `j` there is `ε = ±1` such that, over
  every commutative ring `R : Type u`, `φ_i(w) · divExp (rootOp j) s · φ_i(w)⁻¹ =
  divExp (rootOp (s_i j)) (ε s)`, where `w = sl2Weyl`. The conjugate of `rootOp j` by `weylMat i`
  and `rootOp (s_i j)` are two families for `s_i α_j`, so they differ by `ε^k`. Then use
  `map_weylMat`, `map_weylMatInv`, `map_mul_divExp_mul` and `divExp_pow_smul`.
- `lie_of_isRootOp`: for families `A`, `A'` of roots `j`, `j'` with `α_{j'} ≠ −α_j`, the
  commutator `[A 1, A' 1]` is either `0` or `c • rootOp k 1` for an integer `c` and a root `k`
  with `α_k = α_j + α_{j'}`. A nonzero commutator lies in `lieSpan` (`matAd_mem`) and has
  weight `α_j + α_{j'} ≠ 0`. That weight is a root `α_k` by `exists_root_of_isWtHom`. So the
  commutator is `q • rootOp k 1` over `ℚ`, and `q` is an integer because `rootOp k 1` is
  primitive (`exists_int_of_map_eq_smul`).
- `toChevalleyLieData`: the structure `ChevalleyLieData P b` with `ℓ`, `n`, `wt`, `φ` taken from
  `S` and `e = rootOp`. The fields `φ_upper` and `φ_lower` follow from `rootOp_simple` and
  `rootOp_reflectionPerm_self`, `weyl_conj` is `weyl_conj_rootOp`, and `lie_e_e` is
  `lie_of_isRootOp`.
- `nonempty_chevalleyLieData_of_simpleRootData`: if `SimpleRootData P b` is nonempty, then so
  is `ChevalleyLieData P b`.

## Provenance

This follows the classical route to a Chevalley basis. Root vectors of non-simple roots are
obtained from simple ones by Weyl conjugation, and they are unique up to sign because the root
spaces are lines and the lattice is admissible (Steinberg, *Lectures on Chevalley groups*,
§1, Theorem 1, and §3, Lemma 19; Humphreys, *Introduction to Lie Algebras and Representation
Theory*, §25). The integrality of `c` is obtained here from the primitivity of the root
operators, not from the explicit formula `c = ±(r + 1)` for the structure constants; the latter
is neither stated nor used. The specific organization (families of root operators, `rootOp`
by case distinction) is internal to this project.
