# The Frobenius functions of a Jacquet functional

Module: `Langlands.Representation.Archimedean.ComplexJacquetFrobeniusFunction`.

## Purpose and provenance

This is the fifth helper module for `Langlands.Archimedean.complexJacquetFrobenius` (see
`ComplexJacquetFrobeniusProof.md`). It defines the functions on `GL_n(ℂ)` that the Frobenius
reciprocity map assigns to vectors of a `(𝔤𝔩_n(ℂ), U(n))`-module, and proves that they are
well defined, transform correctly under the upper triangular Borel subgroup and under `U(n)`, and
are smooth.

Mathematically, let `ℓ` be a linear form on `V` that transforms under the diagonal unitary
matrices `m` by the character `m ↦ ∏ⱼ m_jj^{l_j}`, and let `χ` be the Borel character
`β ↦ ∏ⱼ (β_jj/‖β_jj‖)^{l_j} ‖β_jj‖^{α_j}` of `ComplexJacquetBorel`. The Frobenius function of
`w ∈ V` is `f_w(βκ) = χ(β) ℓ(ρ(κ) w)` for `β` invertible upper triangular and `κ` unitary. In
the notation of `ComplexJacquetFrobenius.md`, this is the function `F(βk) = σ_W(β) μ(k · v)`
obtained from Wallach's map `C(v)(k) = μ(k⁻¹ · v)` (N. Wallach, *Representations of reductive
Lie groups*, Proc. Sympos. Pure Math. 33 (1979), 4.16 and Lemma 4.17) after passing from his
right-induced, left-translation model to the Library's left-equivariant, right-translation model.
The module makes no literature claim beyond the elementary properties proved here. `IsTorusEigenfunctional`, `iwasawaB`,
`iwasawaK` and `frobeniusFunction` are auxiliary definitions of this formalization.

## Proof route

*Factorization.* Every `g ∈ GL_n(ℂ)` is `β κ` with `β` invertible upper triangular and `κ`
unitary (Library theorem
`Langlands.LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary`). The definition of
`f_w` uses a chosen factorization (`iwasawaB`, `iwasawaK`). If also `g = b k`, then
`m = k κ* = b⁻¹ β` is upper triangular and unitary, hence diagonal with diagonal entries of norm
one. Then `χ(β) = χ(b) ∏ m_jj^{l_j}` and `ℓ(ρ(κ) w) = ℓ(ρ(m*) ρ(k) w) = ∏ conj(m_jj)^{l_j} ℓ(ρ(k) w)`,
and the two products cancel. So `f_w(g) = χ(b) ℓ(ρ(k) w)` for every such factorization
(`frobeniusFunction_eq`). Translation properties follow directly.

*Smoothness.* Smoothness on the manifold `GL_n(ℂ)` (the Library's model `matrixModel ℂ n`) is
reduced, by the Library lemma `contMDiff_of_contDiffOn`, to smoothness of the extension
`unitsExtension f_w` (extension by `0`) at every invertible matrix. At `1`, use the chart
`Φ(X) = (1 + P_b X) exp(P_u X)` and its `C^∞` local inverse `Ψ` from `ComplexJacquetChart`. For
`y` near `1`, `y = (1 + P_b Ψ(y)) exp(P_u Ψ(y))` with the first factor upper triangular with
nonzero diagonal, so `f_w(y) = χ(1 + P_b Ψ(y)) · G(P_u Ψ(y))`, where `G` is the `C^∞` function of
`IsComplexGKModule.exists_contDiff_coeff` (`ComplexJacquetOrbit`) with
`G(Y) = ℓ(ρ(exp Y) w)` for skew-Hermitian `Y`. Both factors are `C^∞` near `1`. At
`g₀ = β₀ κ₀` the identity `f_w(y) = χ(β₀) f_{ρ(κ₀) w}(β₀⁻¹ y κ₀*)` reduces smoothness at `g₀`
to smoothness of `f_{ρ(κ₀) w}` at `1`.

## Declarations

All declarations are in the namespace `Langlands.Archimedean`.

### Iwasawa factors

- `exists_iwasawa`: every `g ∈ GL_n(ℂ)` has a factorization `g = b u` in the sense of the
  Library's `IsTriangularUnitaryFactorization` (`b` upper triangular and invertible, `u`
  unitary).
- `iwasawaB g`, `iwasawaK g` (definitions): a chosen upper triangular factor and the
  corresponding element of `Matrix.unitaryGroup (Fin n) ℂ`.
- `iwasawa_spec`: `iwasawaB g` is upper triangular and invertible, and `g = iwasawaB g * iwasawaK g`.
- `isUnit_of_upper`: an upper triangular matrix with nonzero diagonal entries is invertible.

### The Frobenius function

- `IsTorusEigenfunctional ρ ℓ l` (definition): for every diagonal unitary `m` and every `w`,
  `ℓ(ρ(m) w) = (∏ⱼ m_jj^{l_j}) ℓ(w)`.
- `frobeniusFunction ρ ℓ l α w g` (definition): `borelChar l α (iwasawaB g) · ℓ(ρ(iwasawaK g) w)`.
- `frobeniusFunction_eq`: under `IsTorusEigenfunctional ρ ℓ l`, if `g = b k` with `b` upper
  triangular and invertible and `k` unitary, then `f_w(g) = borelChar l α b · ℓ(ρ(k) w)`.
- `frobeniusFunction_translate`: if `g = b z k` with `b` upper triangular invertible and `k`
  unitary, then `f_w(g) = borelChar l α b · f_{ρ(k) w}(z)`.
- `frobeniusFunction_mul_left`: `f_w(b g) = borelChar l α b · f_w(g)` for upper triangular
  `b ∈ GL_n(ℂ)`.
- `frobeniusFunction_mul_unitary`: `f_w(g k) = f_{ρ(k) w}(g)` for unitary `k`.
- `frobeniusFunction_diagonal_mul`: for `a : Fin n → ℂˣ` and `u` in the Library's
  `upperUnipotent n ℂ`, `f_w(diag(a) u g) = (∏ⱼ borelFactor (l j) (α j) (a j)) · f_w(g)`.
- `frobeniusFunction_add`, `frobeniusFunction_smul`: `w ↦ f_w` is complex-linear.

### Smoothness

- `contDiffAt_one_frobeniusFunction`: for `IsComplexGKModule n ρ π` and
  `IsTorusEigenfunctional ρ ℓ l`, `unitsExtension f_w` is `C^∞` (over `ℝ`) at the identity
  matrix.
- `contDiffAt_frobeniusFunction`: under the same hypotheses, `unitsExtension f_w` is `C^∞` at
  every invertible matrix `g₀`.
- `contMDiff_frobeniusFunction`: under the same hypotheses, `f_w` is a `C^∞` function on the
  manifold `GL_n(ℂ)`, that is,
  `ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (frobeniusFunction ρ ℓ l α w)`.
