# Real orthogonal compact weights reproducing a square test and its Fourier transform

This module collects the orthogonal-group facts needed to apply the real finite-product
expansion `RealLocalEqualShiftedProducts` to both sides of Jacquet's equal-rank functional
equation. The compact group is `O = Matrix.unitaryGroup (Fin j) ℝ`, the real orthogonal group,
mapped into `GL_j(ℝ)` by `Unitary.toUnits`. This is the group and embedding used by Worker 771's
`RealStandardCompactBanach.exists_compactProjection_coefficients`. Throughout, `F_b` is the
real square Fourier integral `rectangularFourierIntegral (realScaledCharacter b) (realSelfDualMeasure b)`:
`F_b Φ (X) = ∫ Φ(Y) ψ_b(∑_{a,c} Y_{ac} X_{ac}) dY` for the entrywise self-dual product measure
`rectangularMeasure (realSelfDualMeasure b) j j`.
`realCompactMatrixTranslate d Ψ g A = d(det g⁻¹) Ψ(g⁻¹ A)` is the twisted left translate of
`RealLocalEqualShiftedProducts`.

## Statements and lemmas

* `inverseTranspose_toUnits`: inverse transpose fixes every orthogonal matrix, i.e.
  `(k⁻¹)ᵀ = k`.
* `measurePreserving_realOrthogonalMatrixLeft`: left multiplication `X ↦ k X` by an orthogonal
  matrix preserves every additive Haar measure on real `j × j` matrices.
* `realOrthogonalMatrixFourier`: `F_b (Y ↦ Φ(k Y)) (X) = F_b Φ (k X)` for orthogonal `k`, for
  every function `Φ`. There is no measure factor and no integrability hypothesis.
* `RealLocalCompactFourierWeightStatement` (proved by `realLocalCompactFourierWeight`): take
  `b ≠ 0`, a finite measure `ν` on `O` and a continuous weight `κ` on `O`. Let `d` be a real
  character and `Ψ` a function integrable for the self-dual product measure, with
  `∫ κ(k) d(det k⁻¹) Ψ(k⁻¹ A) dν(k) = Ψ(A)` for every `A`. Then
  `∫ κ(k) d(det k⁻¹) F_bΨ(k⁻¹ X) dν(k) = F_bΨ(X)` for every `X`, with the same weight and
  character.
* `matrixTransform_eq_realRectangularSchwartzFourier`: Worker 823's trace-pairing square
  Fourier transform `RealSquareFourier.matrixTransform b Φ`, with phase `ψ_b(tr(Xᵀ Y))` and
  the product self-dual measure, equals `realRectangularSchwartzFourier b Φ` as a function.
* `mem_finiteWeights_of_finiteDimensional`: a continuous weight `κ` whose left translates
  `k ↦ κ(x⁻¹ k)` span a finite-dimensional space of functions lies in
  `CompactRepresentativeWeights.finiteWeights`. That is the hypothesis of Worker 771's compact
  projection.
* `finiteDimensional_toUnits_span`: the finite left orbit condition of
  `RealOrthogonalSchwartzDensityStatement` uses the compact subgroup
  `unitaryCompact ℝ j ⊆ GL_j(ℝ)` and `Φ(k⁻¹ X)`. The lemma shows it implies the same condition
  for translates by `Unitary.toUnits k`, as `k` runs over `O`.
* `dualFunction_compactExpansion`: suppose a compact average of right translates of `V` has a
  finite expansion, `∫ κ(k) V(x k g) dν(k) = ∑_i V_i(x) b_i(g)`. Then the Weyl inverse-transpose
  dual `Ṽ(g) = V(w (gᵀ)⁻¹)` (Library `ArchimedeanLocal.dualFunction`) satisfies
  `∫ κ(k) Ṽ(x k g) dν(k) = ∑_i Ṽ_i(x) b_i((gᵀ)⁻¹)`, with the same weight.
* `RealOrthogonalMatchedWeightStatement` (proved by `realOrthogonalMatchedWeight`): take a Haar
  measure `ν` on `O`, a real character `d` and a Schwartz test `Ψ` on real `j × j` matrices
  with finite left orthogonal orbit, in the form of the density theorem. Then there is a
  continuous weight `κ ∈ finiteWeights` that reproduces `Ψ` and, with the same character,
  `realRectangularSchwartzFourier b Ψ`.

## Proofs

The measure statement is proved as in the complex unitary case, `ComplexLocalUnitaryMatrixFourier`.
Push the Haar measure forward along `X ↦ k X`. The result is again an additive Haar measure, hence
a scalar multiple. The scalar is one, because the compact set `O · S`, for a compact
neighbourhood `S` of zero, is invariant and has positive finite measure. The Fourier identity is
the Library change of variables `rectangularFourierIntegral_leftRight` with `A = k`, `B = 1` and
multiplier one, combined with `inverseTranspose_toUnits`.

For the Fourier transport, put `c(k) = κ(k) d(det k⁻¹)`. The shear `(k, Y) ↦ (k, k⁻¹ Y)` preserves
`ν × μ`, because each fibre map preserves `μ`. So `(k, Y) ↦ c(k) Ψ(k⁻¹ Y) ψ_b(⟨Y, X⟩)` is integrable,
and Fubini lets us exchange the `k` and `Y` integrals. Integrating over `k` first and using the
reproduction gives `F_bΨ(X)`. Integrating over `Y` first and using `realOrthogonalMatrixFourier`
for `k⁻¹` gives `c(k) F_bΨ(k⁻¹ X)`. The proof is the real counterpart of
`ComplexLocalCompactFourierWeight`. Inverse transpose fixes every orthogonal matrix
(`inverseTranspose_toUnits`). Applied to the orthogonal matrix `k⁻¹`, this gives
`((k⁻¹)⁻¹)ᵀ = kᵀ = k⁻¹`. So the dual translates are again translates by `k⁻¹` with the same
character `d`, and no inverse-transpose reparametrization of `O` is needed. (The plain transpose
of `k⁻¹` is `k`, not `k⁻¹`.)

The convention bridge is an entrywise computation: `tr(Xᵀ Y) = ∑_{a,c} Y_{ac} X_{ac}`. The
self-dual product measures agree by definition of `rectangularMeasure`. For finite weights,
the coercion `C(O, ℂ) → (O → ℂ)` is injective and maps the left regular orbit span of `κ` into
the span of the translates `k ↦ κ(x⁻¹ k)`, so finiteness transfers. The orbit comparison uses
`⟨Unitary.toUnits k, k.2⟩ ∈ unitaryCompact ℝ j`, whose inverse has the same value as
`(Unitary.toUnits k)⁻¹`. The dual expansion rewrites `w ((x k g)ᵀ)⁻¹` as
`(w (xᵀ)⁻¹) k ((gᵀ)⁻¹)` and applies the given expansion at `(w (xᵀ)⁻¹, (gᵀ)⁻¹)`. The matched weight
comes from `exists_realCompactMatrixWeight` (from `RealLocalEqualShiftedProducts`), applied with
`ι = Unitary.toUnits` to the finite span condition, then from the two finite-weight lemmas and
the Fourier transport. Schwartz tests are integrable for the additive Haar measure
`rectangularMeasure (realSelfDualMeasure b) j j`.

## Provenance

These are internal steps for Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.2,
pp. 56–58. There a left `K_n`-finite square test is reproduced by a `K_n`-finite function, so
that the compact average of the Whittaker function separates into finitely many terms. The same
function must then serve on the dual side after Fourier transformation. Jacquet uses this
implicitly. The Lean module proves only the orthogonal-group, Fourier and finiteness facts listed
above. It proves no integral identity, continuation or functional equation.
