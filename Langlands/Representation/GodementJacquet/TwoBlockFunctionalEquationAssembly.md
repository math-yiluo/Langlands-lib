# Assembly of the two-block normalized functional equation

Module `Langlands.Representation.GodementJacquet.TwoBlockFunctionalEquationAssembly`.
Author: Worker 33.

The closed statement `TwoBlockMatrixFunctionalEquationInductionStatement` is the
functional-equation part of Godement–Jacquet 1972, Theorem 3.4 (printed pages
36–45), for two blocks. This module reduces it to two inputs:

1. the published two-block analytic statement
   `TwoBlockMatrixAnalyticInductionStatement`, whose proof is the work of task
   be6f556e;
2. the internal interface `TwoBlockMatchedZetaExpansionStatement`, defined here. It
   is proved in module `TwoBlockMatchedZetaExpansion` (theorem
   `twoBlockMatchedZetaExpansion`), not in this module.

## The matched expansion interface

`TwoBlockMatchedZetaExpansionStatement.{uF,uV}` has the same field, instance and
block hypotheses as the target statement, in the same order. The only difference is
that `IsSelfDual ψ ν` is named `hsd`, because the conclusion uses it. Its conclusion
is the following. Write `I = F.canonicalNormalizedProductInduced (succBlockShape m h) σ`
for the actual normalized induced representation. For every full-matrix test
`Φ : MatrixTestFunction t F`, every smooth functional `ℓ : SmoothDual I` and every smooth
vector `v : smoothVectors I`, put `f = biSmoothCoefficient I ℓ v`, the generator
`g ↦ ℓ(I(g) v)` of `biSmoothMatrixCoefficients I`. Then there are `M : ℕ` and

- block tests `Ψ0 j : MatrixTestFunction (m 0) F` and `Ψ1 j : MatrixTestFunction (m 1) F`,
- block coefficients `f0 j ∈ biSmoothMatrixCoefficients (σ 0)` and
  `f1 j ∈ biSmoothMatrixCoefficients (σ 1)`, for `j : Fin M`,

such that both of the following hold.

- On some right half-plane `b < Re s`, with the canonical p-adic `matrixIntegral`
  (normalized absolute value and normalized Haar measure `generalLinearHaar`),

  ```text
  Z(Φ, s + t/2, f) = ∑ j, Z(Ψ0 j, s + m0/2, f0 j) · Z(Ψ1 j, s + m1/2, f1 j).
  ```

- On some right half-plane, with `F̂ = rectangularFourierEquiv ψ ν _ _ hsd` the
  plus-sign full Fourier transform on each matrix size,

  ```text
  Z(F̂ Φ, s + t/2, ι f) = ∑ j, Z(F̂ Ψ0 j, s + m0/2, ι f0 j) · Z(F̂ Ψ1 j, s + m1/2, ι f1 j),
  ```

  where `ι = coefficientIota`, `(ι f)(g) = f(ᵗg⁻¹)`.

The shifts are `jpssShift n = n/2` at rank `n + 1`. The same data
`(M, Ψ0, Ψ1, f0, f1)` appear in both expansions. This is the content of
Godement–Jacquet (3.4.5) (printed 41) and printed pages 41–42: the formal computation
(3.4.1)–(3.4.5) for the original integral and, for the transformed integral,
Lemma 3.4.0 (printed 38) applied to the same tensor data, so that the same constants
`c_ij` appear. The source uses the contragredient coefficient `f̌` on the transformed
side; the interface uses `ι f`, as the target statement does.

Provenance: the interface is internal. It isolates the step of the source proof that
the assembly needs and is not stated separately in the source.

## The assembly theorem

`twoBlockMatrixFunctionalEquationInduction_of_expansion (hexp) (han)` proves
`TwoBlockMatrixFunctionalEquationInductionStatement.{uF,uV}`. The proof:

- The two analytic conjuncts are the two conjuncts of `han`, applied to the same
  hypotheses.
- For each test `Φ`, the Fourier witness is `rectangularFourierEquiv ψ ν (t+1) (t+1) hsd Φ`.
  `MatrixFourierPair` holds by `rectangularFourierEquiv_integrable` and
  `rectangularFourierEquiv_apply`.
- The expansion extends from the generators to every `f ∈ biSmoothMatrixCoefficients I`
  by `Submodule.span_induction`. Zero uses `M = 0` and `matrixIntegral_smul` with
  scalar `0`. For a sum, the data are concatenated with `Fin.append` and
  `Fin.sum_univ_add`. The integral of the sum splits by `matrixIntegral_add`, which
  needs convergence of both summands. That convergence holds on the common half-planes
  given by the convergence conjuncts of `han` (`MatrixConvergesOnRight` and
  `IotaMatrixConvergesOnRight` of `I`). The new half-plane is the maximum of the old
  ones and the convergence abscissa. For a scalar multiple `r • f`, the scalar is
  moved onto `f0 j` by `matrixIntegral_smul`; `coefficientIota` commutes with sums
  and scalars by definition. The groups `GL_{n+1}(F)` carry the Borel structure
  used by the canonical p-adic integrals, introduced as local instances in the proof.
- Given `f`, `R` and `RD` with `HasShiftedRationalValue` for `(Φ, f)` and for
  `(F̂ Φ, ι f)`, the extended expansion supplies `(M, Ψ0, Ψ1, f0, f1)`. The block analytic
  assertions in the block data (`(hdata i).1.2.1` and `(hdata i).2.1.2.1`) supply
  continuations `R0 j`, `R1 j` of the block integrals and `RD0 j`, `RD1 j` of the
  transformed block integrals.
- The block functional-equation data `(hdata i).2.2 (Ψ0 j)` give a Fourier witness.
  Its values equal those of `F̂ (Ψ0 j)` (ext), so the block equation holds for
  `R0 j` and `RD0 j` with `(P 0, PDual 0, c 0, a 0)`. The same holds for block 1.
- `normalizedFunctionalEquation_of_eventually_sum_mul` (module
  `FunctionalEquationProducts`), with `1 < q` from `residueCardinality_gt_one`,
  gives the equation for `R` and `RD` with the product polynomials, product unit and
  summed exponent. `Fin.prod_univ_two` and `Fin.sum_univ_two` match the `Fin 2`
  products and sum of the target.

Compiled clean (0 errors, 0 warnings). Axioms: `propext`, `Classical.choice`, `Quot.sound`.
