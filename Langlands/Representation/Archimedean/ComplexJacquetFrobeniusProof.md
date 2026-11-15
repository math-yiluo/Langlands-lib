# Proof of Frobenius reciprocity for Jacquet functionals of `(𝔤𝔩_n(ℂ), U(n))`-modules

Module: `Langlands.Representation.Archimedean.ComplexJacquetFrobeniusProof`.

## Result

The theorem `Langlands.Archimedean.complexJacquetFrobenius` proves the Library statement
`Langlands.Archimedean.ComplexJacquetFrobeniusStatement.{uV}` (module
`Langlands.Representation.Archimedean.ComplexJacquetFrobenius`), with no extra hypotheses:

```
theorem complexJacquetFrobenius : ComplexJacquetFrobeniusStatement.{uV}
```

The statement says the following. Let `(ρ, π)` be a `(𝔤𝔩_n(ℂ), U(n))`-module on a complex vector
space `V` (`IsComplexGKModule n ρ π`), and let `ℓ ≠ 0` be a Jacquet functional with exponents
`a`, `b` (`IsComplexJacquetFunctional n π ℓ a b`). Then there are complex characters
`d 0, …, d (n−1)` with `2 (d j).exponent + (n − 1) − 2j = a_j` and `i · (d j).weight = b_j`, and
a nonzero complex-linear map `B` from `V` into the `U(n)`-finite functions of
`complexStandardModule n (List.ofFn d)` that satisfies `IsComplexStandardEmbedding`. That is,
`B(ρ(k) v)` is the right translate of `B v` by `k`, and `B(π(1 ⊗ X) v)` is the right derivative
`rightDerivative (matrixModel ℂ n) X (B v)` for every complex matrix `X`.

The source is Wallach's Frobenius reciprocity (N. Wallach, *Representations of reductive Lie
groups*, Proc. Sympos. Pure Math. 33 (1979), 4.16 and Lemma 4.17), specialized to `GL_n(ℂ)` and
its upper triangular Borel subgroup. `ComplexJacquetFrobenius.md` explains how the statement
relates to Wallach's normalizations. The proof below is a direct construction and does not
follow Wallach's argument step by step. In particular it uses neither irreducibility nor
admissibility of `V`; the statement does not assume them.

## Proof

Fix `(ρ, π)`, `ℓ`, `a` and `b` as above.

1. **Torus character** (`ComplexJacquetTorus`). By `IsComplexJacquetFunctional.exists_weight`,
   there are integers `l_j` with `b_j = i l_j`, and `ℓ(ρ(m) w) = (∏ⱼ m_jj^{l_j}) ℓ(w)` for every
   diagonal unitary `m`. So `ℓ` satisfies `IsTorusEigenfunctional ρ ℓ l`.

2. **Characters.** Put `d j = characterOfParams (l j) t_j` with `t_j = (a_j − (n − 1) + 2j)/2`
   (`ComplexJacquetBorel`). Then `(d j).weight = l_j`, so `i (d j).weight = b_j`, and
   `2 t_j + (n − 1) − 2j = a_j`.

3. **Frobenius functions** (`ComplexJacquetFrobeniusFunction`). For `w ∈ V` let
   `f_w = frobeniusFunction ρ ℓ l a w`, so `f_w(βκ) = χ(β) ℓ(ρ(κ) w)` with
   `χ = borelChar l a`, `β` upper triangular and `κ` unitary. It is independent of the
   factorization, `C^∞` on `GL_n(ℂ)` (`contMDiff_frobeniusFunction`), satisfies
   `f_w(gk) = f_{ρ(k) w}(g)` for unitary `k`, and transforms on the left by
   `f_w(diag(a') u g) = ∏ⱼ borelFactor (l j) (a j) (a'_j) · f_w(g)`. By
   `principalSeriesCharacter_ofFn` and step 2, this product is the principal series character of
   `List.ofFn d` at `a'`. So `f_w` lies in `complexStandardModule n (List.ofFn d)`.

4. **`U(n)`-finiteness** (`frobeniusFunction_mem_kFiniteVectors`). The right translates of
   `f_w` by `k ∈ U(n)` are the functions `f_{ρ(k) w}`. They lie in the image, under the linear map
   `w ↦ f_w` (`frobeniusMap`), of the orbit span of `w`. That span is finite-dimensional because
   `w` is `U(n)`-finite (first clause of `IsComplexGKModule`).

5. **Derivative at the identity** (`fderiv_one_frobeniusFunction`). Let `ψ` be the extension of
   `f_u` by zero to all matrices. It is differentiable at `1` (step 3). The claim is
   `Dψ(1) Y = ℓ(π(1 ⊗ Y) u)` for every complex matrix `Y`. Write
   `Y = N + diag(Re Y_jj) + P_u Y`, where `P_u Y` is the skew-Hermitian part of
   `ComplexJacquetChart` and `N` is strictly upper triangular. Since both sides are real-linear in
   `Y`, it suffices to check three kinds of directions:
   - *skew-Hermitian `S`*: along `t ↦ exp(tS)`, `ψ(exp(tS)) = ℓ(ρ(exp(tS)) u)`, and its derivative
     at `0` is `ℓ(π(1 ⊗ S) u)` by the curve clause of `IsComplexGKModule`
     (`hasDerivAt_skewExp`);
   - *strictly upper triangular `N`*: for every `v` in the Library's `upperUnipotent n ℂ`,
     `ψ(v · 1) = χ(v) ℓ(u) = ℓ(u) = ψ(1)`, because `v` has unit diagonal and so `χ(v) = 1`. The
     Library lemma `Langlands.Archimedean.ComplexDuality.LieInvariance.fderiv_strictUpper_mul_eq_zero`
     (module `ComplexDuality.LieInvariance`), applied at `y = 1`, then gives `Dψ(1) N = 0`. This
     equals `ℓ(π(1 ⊗ N) u)` by the first Jacquet clause;
   - *real diagonal `diag(r)`*: along `t ↦ diag(e^{t r_j})`,
     `ψ = exp(t ∑ⱼ r_j a_j) ℓ(u)` (`borelFactor_exp`), with derivative `(∑ⱼ r_j a_j) ℓ(u)`. This
     equals `ℓ(π(1 ⊗ diag(r)) u)` by `IsComplexJacquetFunctional.apply_upper`.

6. **Right derivatives** (`rightDerivative_frobeniusFunction`). For `g = βκ`, left equivariance
   under `β` (Library lemma `rightDerivative_mul_left_of_eq`) and the conjugation formula for
   right translation (Library lemma `rightTranslation_rightDerivative`) give
   `R(X) f_w(g) = χ(β) · R(κ X κ*) f_{ρ(κ) w}(1)`. By the Library lemma
   `rightDerivative_eq_fderiv` and step 5 this is `χ(β) ℓ(π(1 ⊗ κ X κ*) ρ(κ) w)`. The
   equivariance clause of `IsComplexGKModule` rewrites it as `χ(β) ℓ(ρ(κ) π(1 ⊗ X) w)`, which is
   `f_{π(1 ⊗ X) w}(g)`.

7. **Conclusion** (`complexJacquetFrobenius`). Define `B w = f_w`, which lands in the
   `U(n)`-finite functions of the standard module by steps 3 and 4. It is linear
   (`frobeniusFunction_add`, `frobeniusFunction_smul`). It intertwines `ρ(k)` with right
   translation (step 3) and `π(1 ⊗ X)` with the right derivative (step 6). It is nonzero because
   `f_w(1) = ℓ(w)` and `ℓ ≠ 0`.

## Declarations in this module

All declarations are in the namespace `Langlands.Archimedean`.

- `isUnit_of_unitary`: a unitary matrix is invertible.
- `unitsExtension_frobeniusFunction_eq`: if `y = b k` with `b` upper triangular invertible and `k`
  unitary, then `unitsExtension f_w y = borelChar l α b · ℓ(ρ(k) w)`.
- `fderiv_one_frobeniusFunction`: for `IsComplexGKModule n ρ π`,
  `IsComplexJacquetFunctional n π ℓ a b` and `IsTorusEigenfunctional ρ ℓ l`,
  `fderiv ℝ (unitsExtension (frobeniusFunction ρ ℓ l a u)) 1 Y = ℓ (π (1 ⊗ₜ Y) u)` for every
  matrix `Y`.
- `rightDerivative_frobeniusFunction`: under the same hypotheses,
  `rightDerivative (matrixModel ℂ n) X (frobeniusFunction ρ ℓ l a w) g =
  frobeniusFunction ρ ℓ l a (π (1 ⊗ₜ X) w) g`.
- `frobeniusMap ρ ℓ l α` (definition): the complex-linear map `w ↦ frobeniusFunction ρ ℓ l α w`.
- `frobeniusFunction_mem_kFiniteVectors`: under `IsTorusEigenfunctional ρ ℓ l`, if `w` is
  `U(n)`-finite then `f_w` is a `unitaryCompact ℂ n`-finite vector for right translation.
- `complexJacquetFrobenius : ComplexJacquetFrobeniusStatement.{uV}`: the target theorem.

## Guide to the helper modules

The proof uses five helper modules, each with its own Markdown file:

| Module | Content |
| --- | --- |
| `ComplexJacquetTorus` | integrality `b_j = i l_j` and the torus character of `ℓ` |
| `ComplexJacquetOrbit` | `Y ↦ μ(ρ(exp Y) w)` extends to a `C^∞` function of all matrices |
| `ComplexJacquetBorel` | the Borel character `borelChar`, the principal series character, `characterOfParams` |
| `ComplexJacquetChart` | the chart `Φ(X) = (1 + P_b X) exp(P_u X)` and its `C^∞` local inverse at `1` |
| `ComplexJacquetFrobeniusFunction` | the Frobenius functions, their transformation laws and smoothness |

All modules live in `Langlands/Representation/Archimedean/`. Besides the statement module, they
use the Library modules `ComplexJacquetReduction`, `PrincipalSeriesGKModule`,
`PrincipalSeriesStability`, `StandardModule` and `Langlands.LinearAlgebra.TriangularUnitary`,
Mathlib, and the following Library results:

- `Langlands.IntegerLattice.GlobalBlockBasis.upper_mul_diag` and
  `Langlands.GeneralLinear.UpperBruhatCoordinates.diag_ne_zero_of_upper` (triangular matrices, used
  in `ComplexJacquetBorel`);
- `Langlands.Archimedean.principalSeriesCharacter_eq` and the definitions `unitChar`, `posWeight`
  and `posExponent` (module `ComplexStandardNontrivialProof`, used in `ComplexJacquetBorel`);
- `Langlands.GroupScheme.GeneralLinear.mem_blockLeviSubgroup_of_unitary` (an upper triangular
  unitary matrix is diagonal, used in `ComplexJacquetTorus`);
- `Langlands.Automorphic.OperatorRealization.eq_exp_mul_of_hasDerivAt` (the scalar ODE
  `φ' = c φ`, used in `ComplexJacquetTorus`);
- `Langlands.Archimedean.ComplexDuality.LieInvariance.fderiv_strictUpper_mul_eq_zero` (used in
  this module, step 5).

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
