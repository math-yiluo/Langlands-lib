# Matrix coefficients of finite-dimensional subcomodules

Author: Worker 254.

This helper module contains the linear-algebra core of the closed linear embedding
theorem `Langlands.GroupScheme.affineLinearEmbeddingStatement_viaCorepresented`. It is stated for an
abstract comultiplication and counit on a module, without schemes, algebras or
group laws. Only coassociativity and the two counit laws are assumed, as explicit
hypotheses. All declarations
are in the namespace `Langlands.GroupScheme.Comodule`.

## Source and provenance

The mathematics follows J. S. Milne, *Algebraic Groups: The Theory of Group
Schemes of Finite Type over a Field* (2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`:

- Proposition 4.7 and Corollary 4.8, printed p. 86 (PDF p. 102): every comodule
  is the union of its finite-dimensional subcomodules;
- Theorem 4.9, printed p. 87 (PDF p. 103): if `Δ(e_j) = Σ_i e_i ⊗ a_ij` for a basis
  `e` of a finite-dimensional subcomodule `V` of `O(G)`, then
  `e_j = Σ_i ε(e_i) a_ij`.

The registered author's errata (`milne-2017-algebraic-groups-errata-2026-11-02`)
have no entry for these pages.

The definitions below are internal tools for that argument. They are not
separate literature definitions. The Lean route differs from Milne's in two
ways. The finite-dimensional subcomodule containing `x` is the span of all
right contractions of `Δ(x)`, not the span of `x` and its coefficients against a
basis. The subcomodule condition is expressed as stability under all right
contraction operators.

## Definitions

Let `k` be a commutative ring and `B` a `k`-module, with linear maps
`Δ : B → B ⊗ B` and `ε : B → k`. For a linear functional `m : B → k`:

- `rightOp Δ m = rid ∘ (id ⊗ m) ∘ Δ : B → B`, the right contraction operator;
- `leftOp Δ l = lid ∘ (l ⊗ id) ∘ Δ : B → B`, the left contraction operator;
- `convFun Δ m l = mul ∘ (m ⊗ l) ∘ Δ : B → k`, the convolution of two functionals.

The axioms are propositions about the maps:

- `Coassoc Δ` is Mathlib's form of coassociativity,
  `assoc ∘ (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ`;
- `RightCounit Δ ε` is `rid ∘ (id ⊗ ε) ∘ Δ = id`;
- `LeftCounit Δ ε` is `lid ∘ (ε ⊗ id) ∘ Δ = id`.

`IsStable Δ V` says that a submodule `V` is mapped into itself by every
`rightOp Δ m`. This is the subcomodule condition. `orbit Δ x` is the span of all
`rightOp Δ m x`.

## Results over a commutative ring

- `apply_rid_lTensor`: for every `x : B ⊗ B`,
  `l(rid((id ⊗ m) x)) = m(lid((l ⊗ id) x))`. Both sides equal `(l ⊗ m)(x)`. The
  proof is induction on the tensor.
- `rightOp_rightOp`: under `Coassoc Δ`,
  `rightOp m (rightOp l x) = rightOp (convFun m l) x`. The proof first commutes
  `Δ` past the right contraction (an identity of linear maps, checked on pure
  tensors). It then rewrites `(Δ ⊗ id) Δ x` by coassociativity. Finally it
  identifies the resulting contraction of `B ⊗ (B ⊗ B)` by checking triple pure
  tensors.
- `comul_leftOp`: under `Coassoc Δ`, `Δ (leftOp l x)` is the left contraction
  by `l` of `assoc((Δ ⊗ id)(Δ x))`.
- `orbit_isStable`: under coassociativity, `orbit Δ x` is stable. This is span
  induction with `rightOp_rightOp`.
- `rightOp_counit`, `leftOp_counit` restate the counit laws pointwise.
  `mem_orbit` proves `x ∈ orbit Δ x`, since `x = rightOp ε x`.
- `IsStable.sup`: the sum of two stable submodules is stable.

## Results over a field

In the section `Field`, `k` is a field.

- `tensor_ext_of_rid`: two tensors in `B ⊗ B` are equal if all their right
  contractions agree. The proof uses a basis `c` of `B` and Mathlib's
  `TensorProduct.equivFinsuppOfBasisRight`, whose coefficients are the right
  contractions by the coordinate functionals of `c`.
- `exists_finiteDimensional_rid`: the right contractions of one tensor lie in a
  finite-dimensional subspace (`k ∙ p` for `p ⊗ q`, and sums). The proof is
  induction on the tensor. Hence `orbit_finiteDimensional`.
- `exists_stable`: under `Coassoc Δ` and `RightCounit Δ ε`, every finite set
  `s` lies in a finite-dimensional stable submodule. This is induction on `s`,
  using `orbit Δ x ⊔ V`. This is the Lean form of Milne 4.7 for the regular
  comodule.
- `exists_matrix`: under all three axioms, for every finite set `s ⊆ B` there are
  `n : ℕ` and a matrix `a : Matrix (Fin n) (Fin n) B` such that

  ```text
  Δ (a i j) = Σ_l a i l ⊗ a l j,    ε (a i j) = (1 : Matrix (Fin n) (Fin n) k) i j,
  ```

  and every element of `s` lies in the `k`-span of the entries of `a`.

### Proof of `exists_matrix`

Take a finite-dimensional stable `V ⊇ s` from `exists_stable`, its basis
`e = Module.finBasis k V`, and functionals `lam i : B → k` extending the
coordinate functionals of `e` (`LinearMap.exists_extend`). Put
`a i j = leftOp Δ (lam i) (e j)`.

1. For `v ∈ V`, `Δ v = Σ_i e_i ⊗ leftOp (lam i) v`. By `tensor_ext_of_rid` it
   suffices to compare right contractions by any `m`. The left side gives
   `w = rightOp m v`, which lies in `V` by stability. Hence
   `w = Σ_i lam_i(w) e_i`, and `lam_i(w) = m(leftOp (lam i) v)` by
   `apply_rid_lTensor`.
2. Multiplicativity: `comul_leftOp` and step 1 for `e_j` reduce
   `Δ(a i j)` to `Σ_l lid((lam i ⊗ id)(assoc(Δ(e_l) ⊗ a l j)))`. Each term is
   `a i l ⊗ a l j`, by induction on `Δ(e_l)`.
3. Counit: `ε(a i j) = lam_i(rightOp ε (e_j)) = lam_i(e_j) = δ_ij`, by
   `apply_rid_lTensor` and the right counit law.
4. Span: by the left counit law and step 1,
   `e_j = leftOp ε (e_j) = Σ_i ε(e_i) a i j`, which is Milne's identity in the
   proof of Theorem 4.9. Every `x ∈ s` is a combination of the `e_j`.

The module adds no axioms. Only the results in the `Field` section assume that
`k` is a field.
