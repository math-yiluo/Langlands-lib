# Symplectic involutions are adjoint to antihermitian division forms

Author: Worker 74, for Task 6243 (`d75aa284-b911-411c-8e33-34184b737113`). The main result is

`Langlands.GroupScheme.symplecticInvolutionAntihermitian :
  SymplecticInvolutionAntihermitianStatement.{u}`,

a proof of the statement in
`Langlands/GroupScheme/SimplyConnected/SymplecticInvolutionAntihermitianStatement`. Read that
module's Markdown for the precise statement. In short: let `A` be a finite-dimensional central
simple `K`-algebra and `τ` an involution of the first kind. Suppose an `L`-algebra isomorphism
`e : L ⊗[K] A ≃ M_{2n}(L)` satisfies `e (τ_L x) * J = J * (e x)ᵀ`. Then `A ≅ M_m(D)` for a
central division algebra `D` of degree `d` with `m d = 2n`, carrying an involution `σ` with
`dim Sym(D, σ) = d(d+1)/2`. Under this isomorphism `τ` becomes the adjoint involution of an
invertible trace-valued `σ`-antihermitian matrix `H`.

The module also proves the following auxiliary results, in the namespace
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution`. They use the definitions of
`SymplecticInnerForm/EpsilonHermitian` and `SymplecticInnerForm/CornerInvolution`.

## Auxiliary results

- `finrank_symmetricSubspace_baseChange τ L`: for any field `L` over `K`,
  `finrank L (τ.baseChange L).symmetricSubspace = finrank K τ.symmetricSubspace`. The
  symmetric space is `ker (τ - id)`, and `(τ.baseChange L) - id` is the base change of
  `τ - id`. Because `L` is flat over `K`, `LinearMap.tensorKerEquiv` identifies
  `L ⊗[K] ker (τ - id)` with the kernel of the base change, and `Module.finrank_baseChange`
  finishes.
- `finrank_epsSymmetric_scalarInvolution_of_two_eq_zero` and `..._of_two_ne_zero`: for the
  identity involution `Symplectic.scalarInvolution L` of a field `L`, the skew scalars
  `{c | c = -c}` form all of `L` if `(2 : L) = 0` (dimension `1`) and `0` otherwise
  (dimension `0`).
- `map_chart_eq`: from `e (τ_L x) * J = J * (e x)ᵀ` and `J * J = -1`,
  `e (τ_L x) = J * (e x)ᵀ * (-J)`.
- `finrank_symmetricSubspace_of_chart`: under the chart hypothesis,
  `finrank K τ.symmetricSubspace = 2n · s₀ + (2n choose 2)`, where `s₀` is the dimension of
  the skew scalars of `L` from the previous item. Proof: pass to `L` by
  `finrank_symmetricSubspace_baseChange` and transport along `e` (`epsSymmetricCongr`). The
  transported involution is `y ↦ J ᵗy (-J)`, which is `Int(J)` composed with the transpose
  (`scalarInvolution`'s `matrix`), and `ᵗJ = -J`. So `gramEquiv` with `H = J`, `H' = -J`,
  `ε = -1` identifies its symmetric elements with the skew-symmetric `L`-matrices of size
  `2n`. `finrank_epsSymmetric_matrix` counts these as `2n · s₀ + (2n choose 2)`.
- `one_mem_alternatingSubspace_of_chart` (characteristic two): if `(2 : K) = 0`, then
  `1 = a - τ a` for some `a ∈ A`. Proof by contradiction: if `1` is not in the subspace
  `{a - τ a}`, there is a `K`-linear functional `g` vanishing on it with `g 1 ≠ 0`
  (`Submodule.exists_le_ker_of_notMem`). Its `L`-linear extension `G` to `L ⊗[K] A`
  (`LinearMap.liftBaseChange`) vanishes on every `z - τ_L z`, by induction on tensors. Take
  `y = e⁻¹ (diag(1, 0))` in block form. Then `e (y - τ_L y) = diag(1, 0) - J diag(1, 0)ᵀ (-J)`
  `= diag(1, 0) - diag(0, 1) = diag(1, -1)`, which is the identity because `-1 = 1` in `L`.
  Hence `G 1 = g 1 = 0`, a contradiction.
- `IsGramModel.finrank_symmetricSubspace`: if `IsGramModel τ θ ε U U'` for an involution
  `τ` of `M_ι(D)`, then `finrank K τ.symmetricSubspace =
  card ι · finrank K (θ.epsSymmetric ε) + (card ι choose 2) · finrank K D`. This combines
  `finrank_symmetricSubspace_eq_of_gram` for `θ.matrix ι` with `finrank_epsSymmetric_matrix`.
- Private arithmetic lemmas: `(m d choose 2) = m (d choose 2) + (m choose 2) d²`;
  `d (d + 1) / 2 = d + (d choose 2)`; and `d² = d + 2 (d choose 2)`. A cancellation lemma
  derives `s = d t + (d choose 2)` from `m s + (m choose 2) d² = (m d) t + (m d choose 2)`
  with `m > 0`.

## Proof of the main theorem

1. **Wedderburn.** `A` is artinian, so `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`
   gives `m ≠ 0`, a division `K`-algebra `D`, finite-dimensional over `K`, and
   `φ : A ≃ₐ[K] M_m(D)`. `Langlands.CentralSimple.isCentral_of_algEquiv_matrix` makes `D`
   central. Let `d = Langlands.CentralSimple.reducedDegree K D`; then `finrank K D = d * d`
   and `0 < d`.
2. **Degree.** `finrank K A = (2n)²` by base change along `e`, and `finrank K A = (m d)²` by
   `φ`. So `m d = 2n`.
3. **Dimension of `Sym τ`.** Let `τ_B = τ.algEquivCongr φ` be the transported involution
   of `B = M_m(D)`. It has the same symmetric dimension as `τ`, which
   `finrank_symmetricSubspace_of_chart` computes as `2n · t + (2n choose 2)`, where `t = s₀`.
   For any Gram model `(θ, ε, U, U')` of `τ_B`, `IsGramModel.finrank_symmetricSubspace` and
   the cancellation lemma give `finrank K (θ.epsSymmetric ε) = d t + (d choose 2)`.
4. **A model with sign `-1`.** `exists_isGramModel τ_B` gives a model with some `ε`,
   `ε * ε = 1`.
   - If `(2 : K) = 0`, then `(ε - 1)² = 0`, so `ε = 1 = -1`.
   - Otherwise `ε = 1` or `ε = -1`. If `ε = 1`, step 3 with `t = 0` gives
     `dim Sym θ = (d choose 2)`. By `finrank_symmetricSubspace_add_finrank_skew`, the skew
     space then has dimension `d² - (d choose 2) = d + (d choose 2) > 0`. So there is
     `v ≠ 0` with `θ v = -v`, and the sign-change clause of `exists_isGramModel` gives a model
     with sign `-1`.

   Fix such a model `(θ, -1, U, U')`. Step 3 gives `dim (θ-skew) = d t + (d choose 2)`.
5. **`dim Sym θ = d(d + 1)/2 = d + (d choose 2)`.** In characteristic two, `t = 1` and the
   skew and symmetric spaces coincide. Otherwise `t = 0`, and
   `dim Sym θ = d² - (d choose 2) = d + (d choose 2)`.
6. **`U` is antihermitian and trace-valued.** `ᵗU^θ = -U` is part of the model. For the
   diagonal:
   - If `(2 : K) ≠ 0`: from `θ (U i i) = -U i i`, the entry is `c - θ c` with
     `c = 2⁻¹ • U i i`.
   - If `(2 : K) = 0`: by `one_mem_alternatingSubspace_of_chart`, `1 = a - τ a`. With
     `z = φ a` this gives `z - τ_B z = 1`. Using `τ_B z = U ᵗz^θ U'` and
     `ᵗ(zU)^θ = ᵗU^θ ᵗz^θ = -U ᵗz^θ`, we get `U = (z - τ_B z) U = z U + ᵗ(zU)^θ`. Taking the
     `(i, i)` entry gives `U i i = (zU) i i + θ ((zU) i i)`, which equals
     `(zU) i i - θ ((zU) i i)` in characteristic two.
7. **Conclusion.** Take `degree = d`, `m`, `D`, `σ = θ` and `H = U`. `U` is a unit with
   inverse `U'`. For `x : A`, `τ_B (φ x) = φ (τ x)`, so
   `φ (τ x) * U = U * ᵗ(φ x)^θ * U' * U = U * ᵗ(φ x)^θ`.

The theorem depends on the axioms `propext`, `Classical.choice` and `Quot.sound` only.

## Provenance

Provenance: derived. The statement specializes M.-A. Knus, A. Merkurjev, M. Rost and
J.-P. Tignol, *The Book of Involutions* (AMS Colloquium Publications 44, 1998; source
`knus-merkurjev-rost-tignol-1998-book-of-involutions`), Theorem (4.2)(1) (printed p.43,
PDF p.66) to symplectic involutions and division coefficient algebras. The dimension and
alternating-element criteria come from Proposition (2.6) (printed pp.16–17, PDF pp.39–40).

The proof route differs from KMRT. KMRT read off the type through Proposition (2.20) and
reduced traces. Here the type is detected by comparing dimensions of symmetric spaces with
the split model given by `e` (KMRT's own computation before Definition (2.5), printed p.16,
PDF p.39). In characteristic two, the criterion `1 ∈ Alt(A, τ)` of (2.6)(2) is proved
directly from the chart by the linear-functional argument above. The trace-valued property
of `H` then follows as in the last paragraph of the proof of (4.2), printed p.44 (PDF p.67).
