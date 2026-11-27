# Finite matrix Gauss operators

## Result

`gaussOp_injective_of_card` gives injectivity for every finite index type. For a finite
field `k : Type uK`, a natural number `n`, an additive character `ψ : AddChar k ℂ` with `ψ ≠ 1` and a
complex representation `ρ` of `GL_n(k)` on `V : Type uV`, the operator
`v ↦ ∑_{g ∈ GL_n(k)} ψ(tr g) ρ(g) v` is injective. Rank zero and arbitrary (not necessarily
irreducible or finite-dimensional) representations are included.

## Declarations

The declarations belong to the namespace `Langlands.BushnellKutzko.FiniteGauss`
and is stated for `GL_ι(k)` with an arbitrary finite index type `ι`.

- `sum_addChar_trace_mul_eq_zero`, `sum_addChar_trace_mul`: for a rectangular matrix `B`,
  `∑_X ψ(tr(X B))` over all matrices `X` is `0` if `B ≠ 0` and the number of matrices if `B = 0`.
- `twistedGaussOp ψ A ρ = ∑_g ψ(tr(A g)) ρ(g)` (written `S_A`) and `gaussOp ψ ρ = ∑_g ψ(tr g) ρ(g)`
  (written `T`), as linear maps; `twistedGaussOp_one : S_1 = T`.
- `sum_twistedGaussOp`: `∑_A ψ(-tr A) S_A(v) = |M_ι(k)| v`.
- `twistedGaussOp_mul`: `S_{A h}(v) = ρ(h)⁻¹ S_A(v)` for `h ∈ GL_ι(k)`.
- `gaussOp_map`: `T(ρ(h) v) = ρ(h) T(v)`; `gaussOp_twistedGaussOp`: `T S_A = S_A T`.
- `twistedGaussOp_fixed`: if `A u = A`, then `S_A(v)` is fixed by `ρ(u)`.
- `gaussOp_injective_of_singular`: if `S_A` vanishes on `ker T` for every singular `A`, then `T` is
  injective.
- `glReindex`, `gaussOp_comp_glReindex`: an equivalence of index types induces an isomorphism of
  general linear groups preserving traces, and the Gauss operators correspond.
- `blockDiagHom : GL_{ι₁}(k) × GL_{ι₂}(k) → GL_{ι₁ ⊕ ι₂}(k)`, `(a, D) ↦ diag(a, D)`;
  `blockUnipotent X = [1 X; 0 1]`; `trace_mul_fromBlocks_unipotent`: `tr(M u(X)) = tr M + tr(X C)`
  with `C` the lower left block of `M`; `lowerBlockZeroFactor` and `sum_lowerBlockZero`: the
  matrices with zero lower left block are exactly the products `diag(a, D) u(X)`, each obtained
  once.
- `eq_zero_of_blockUnipotent_fixed`: if the Gauss operators of `GL_{ι₁}(k)` and `GL_{ι₂}(k)` are
  injective on every representation on `V`, then a vector of `ker T` for `GL_{ι₁ ⊕ ι₂}(k)` fixed
  by every `u(X)` is zero.
- `sum_units_addChar`: `∑_{a ∈ kˣ} ψ(a) = -1`; `sum_addChar_trace_of_card_eq_one`: in rank one,
  `∑_g ψ(tr g) = -1`.
- `gaussOp_injective_of_isEmpty`, `gaussOp_injective_of_card_eq_one`: ranks zero and one.
- `gaussOp_injective_of_card`: injectivity for every index type of cardinality `m`, by strong
  induction on `m`.

## Provenance

The proof is the elementary rank induction recorded in the paired Markdown of
`FiniteMatrixGaussInjectivityStatement` ("An elementary proof route"). It uses neither Kondo's
formula nor the classification of the representations of finite general linear groups. The
statement itself is a consequence of Kondo's formula as cited by Bushnell–Fröhlich (1985),
(2.4.11)–(2.4.16).

## Proof

*Fourier inversion.* Swapping the sums, `∑_A ψ(-tr A) S_A(v) = ∑_g (∑_A ψ(tr(A (g - 1)))) ρ(g) v`.
By additive orthogonality the inner sum is `|M_ι(k)|` for `g = 1` and `0` otherwise. For
orthogonality, if `B_{ab} ≠ 0`, then `X ↦ ψ(tr(X B))` is a nontrivial character of the additive
group of matrices, since its value at `t E_{ba}` is `ψ(t B_{ab})`, and `AddChar.sum_eq_zero_of_ne_one`
applies.

*The criterion.* Let `T v = 0`. For invertible `A`, `S_A(v) = ρ(A)⁻¹ T(v) = 0` by reindexing
`g ↦ A⁻¹ g`. If also `S_A(v) = 0` for every singular `A`, Fourier inversion gives `|M_ι(k)| v = 0`,
so `v = 0`.

*Rank zero.* Every matrix is invertible (its determinant is `1`), so the criterion applies
vacuously.

*Rank one.* The only singular matrix is `0`. The vector `w = S_0(v) = ∑_g ρ(g) v` is fixed by the
whole group and lies in `ker T`, because `T` commutes with `S_0`. On fixed vectors `T` acts by
`∑_g ψ(tr g)`. The determinant is a bijection `GL_ι(k) → kˣ` equal to the trace, so this scalar is
`∑_{a ∈ kˣ} ψ(a) = ∑_{x ∈ k} ψ(x) - ψ(0) = -1`. Hence `-w = 0`.

*The parabolic step.* Let `ι = ι₁ ⊕ ι₂`, let `v ∈ ker T` be fixed by every `u(X)`, and let `N` be
the number of matrices `X ∈ M_{ι₁ × ι₂}(k)`. Reindexing `g ↦ g u(X)` and using `ρ(g u(X)) v = ρ(g) v`
gives `T v = ∑_g ψ(tr g) ψ(tr(X C_g)) ρ(g) v`, with `C_g` the lower left block of `g`. Summing over
`X` and using orthogonality,

`N · T v = N · ∑_{C_g = 0} ψ(tr g) ρ(g) v`.

Write each `g` with `C_g = 0` uniquely as `diag(a, D) u(X)`. Its diagonal blocks are invertible
because `det g = det a · det D` (`det_fromBlocks_zero₂₁`). Then `tr g = tr a + tr D` and
`ρ(g) v = ρ(diag(a, 1)) ρ(diag(1, D)) v`, so the last sum is `N · T₁ T₂ v`. Here `T₁` and `T₂`
are the Gauss operators of the restrictions of `ρ` to `GL_{ι₁}(k)` and `GL_{ι₂}(k)` along the
block-diagonal embeddings. From `T v = 0` we get `T₁ T₂ v = 0`, and injectivity of `T₁` and then
of `T₂` gives `v = 0`.

*The induction.* Let `|ι| = m ≥ 2`, let `v ∈ ker T` and let `A` be singular. Choose `x ≠ 0` with
`A x = 0` (`Matrix.exists_mulVec_eq_zero_iff`) and an index `j` with `x_j ≠ 0`. The matrix
`h = (1).updateCol j x` has determinant `x_j ≠ 0` (Cramer's rule, `Matrix.cramer_one`), and the
`j`-th column of `A' = A h` is `A x = 0`. Decompose `ι ≃ {j} ⊕ (ι \ {j})`
(`Equiv.sumCompl`), so that `u(X)` becomes the identity plus a matrix supported in row `j`;
hence `A' u(X) = A'`. The vector `w = S_{A'}(v)` lies in `ker T` and is fixed by every `u(X)`
(`twistedGaussOp_fixed`). Transporting the representation along `glReindex`, the parabolic step,
with the induction hypothesis for cardinalities `1` and `m - 1`, gives `w = 0`. Finally
`S_A(v) = ρ(h) S_{A h}(v) = ρ(h) w = 0`, and the criterion applies.
