# Upper bound for the split rank of the symplectic group of a form

Lean module: `Langlands.GroupScheme.Quaternionic.AntihermitianSplitRankUpper`
(namespace `Langlands.GroupScheme.AntihermitianSplitRank`).

Main result:

```
theorem splitRank_le_wittIndex (σ : FirstKindInvolution K D) {m : ℕ} [NeZero m]
    (H : Matrix (Fin m) (Fin m) D) (hu : IsUnit H) :
    splitRank (σ.symplecticGroup H) ≤ (σ.wittIndex H : ℕ∞)
```

Here `K` is any field (finite fields included), `D` a finite-dimensional central division
`K`-algebra, `σ` an involution of the first kind, and `H` any invertible Gram matrix. No
antihermitian hypothesis is needed for this half. `σ.symplecticGroup H`, `σ.wittIndex H`,
`splitRank` are the Library definitions (`Quaternionic/GroupSchemes`, `Quaternionic/Forms`,
`Rational/SplitTorus`).

## Provenance

This is one half of the formula "relative rank of `SU(D, h)` = Witt index of `h`"
(Tits, *Classification of algebraic semisimple groups*, 1966, Table II, type `C_n`),
the half used for `Langlands.GroupScheme.AntihermitianSymplecticSplitRankStatement`. The
proof below is direct from the Library definitions. All other declarations are internal
auxiliary lemmas.

## Proof

Let `i : 𝔾ₘ^I → σ.symplecticGroup H` be a closed split torus. Write `A = M_m(D)`.

1. **Into the norm-one group.** `toNormOne` is `FactoredKernel.map` from the kernel
   `σ.symplecticGroup H` of `unitaryGroupι ≫ Nrd` to the kernel `normOne K A` of `Nrd`;
   `toNormOne_comp` identifies its composite with `normOneι` as `σ.symplecticAmbientι H`.
   So `j = i ≫ toNormOne` (`normOneTorus`) is a torus of `normOne K A`, and the published
   machinery of `Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankUpper` applies:
   the inverse of the universal unit `g` over `K[ℤ^I]` is `∑ₐ Xᵃ ⊗ eₐ`
   (`universalUnit_inv_eq_sum`), with `eₐ` (`weightElement`) orthogonal idempotents summing
   to `1`, nonzero exactly on the finite weight set `S`.
2. **Generation.** `closure_weightSupport_symplectic`: as `i` and `symplecticAmbientι` are
   closed immersions and the right-regular representation is a monomorphism, the published
   `closure_weights_eq_top` gives `AddSubgroup.closure S = ⊤`.
3. **Isometry equation.** `affinePoint_isometry`: an affine point of `U(H)` read as a unit
   `g` of `R ⊗ A` satisfies `g (1 ⊗ H) ᵗg^σ = 1 ⊗ H` (from `mem_range_unitaryGroupι_iff`
   transported along `Corepresented.map_affineSectionsIso_pointsEquiv`). Applied to the
   universal point (`universalUnit_isometry`) and then to its inverse
   (`universalUnit_inv_isometry`).
4. **Orthogonality** (`weightElement_mul_mul_eq_zero`). `(1 ⊗ e_c) g⁻¹ = Xᶜ ⊗ e_c` and
   `ᵗ(g⁻¹)^σ (1 ⊗ ᵗe_d^σ) = X^d ⊗ ᵗe_d^σ`. Sandwiching the isometry equation for `g⁻¹`
   gives `X^{c+d} ⊗ e_c H ᵗe_d^σ = 1 ⊗ e_c H ᵗe_d^σ`; comparing coefficients of `X^{c+d}`
   (`coeffTensor`) gives `e_c H ᵗe_d^σ = 0` whenever `c + d ≠ 0`.
5. **Symmetry** (`neg_mem_weightSupport`). `e_c H = ∑_d e_c H ᵗe_d^σ`, and only `d = -c`
   can contribute; if `-c ∉ S` then `e_c H = 0`, so `e_c = 0` as `H` is invertible.
6. **Positive half** (`exists_positive_half`). Order `I` and use the lexicographic order on
   `Lex (I → ℤ)` (an ordered group, Mathlib `Pi.Lex`). The positive weights `P ⊆ S` satisfy
   `a + b ≠ 0` for `a, b ∈ P`; since `S = -S`, `P` generates `ℤ^I`, so `|I| ≤ |P|`
   (`card_le_card_of_closure_eq_top`, via `finrank_span_finset_le_card` over `ℤ`).
7. **Isotropic subspace** (`card_le_wittIndex_of_idempotents`). With `E = ∑_{a∈P} eₐ`,
   `E H ᵗE^σ = 0`, so the row vectors fixed by `E` (`fixedRows E`) form a totally isotropic
   subspace (`isTotallyIsotropic_fixedRows`, via `sesqForm_vecMul`). For each `a ∈ P` a
   nonzero row `vₐ` of `eₐ` lies in it, and `vₐ e_b = δ_{ab} vₐ` makes the `vₐ` linearly
   independent over `D`. Hence `|P| ≤ finrank ≤ wittIndex` (`finrank_le_wittIndex`).
8. `card_le_wittIndex` combines 1–7, and `splitRank_le_wittIndex` takes the supremum over
   all closed split tori.
