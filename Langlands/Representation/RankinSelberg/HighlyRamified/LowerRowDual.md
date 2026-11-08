# Inverse transposes of the lower-row matrices

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4: the evaluation of the dual side in formula (14), printed
page 329). Here `ū_x = [[I,0],[x,1]]` is `lowerRow x` from `DualSmear`.

- `lowerRow_castSucc_castSucc`, `lowerRow_castSucc_last`, `lowerRow_last_castSucc`,
  `lowerRow_last_last`: the entries of `ū_x`, from the published lower-block entries.
- `lowerRow_inv`: `ū_x⁻¹ = ū_(-x)`.
- `inverseTranspose_lowerRow_mem`: `ᵗū_x⁻¹` is upper unipotent;
  `inverseTranspose_lowerRow_superdiagonal`: its first-superdiagonal sum is `-x_m`, the only
  nonzero superdiagonal entry being in the last column.
- `rankInclusion_mul_lowerRow`: `diag(C,1) ū_x = ū_(x C⁻¹) diag(C,1)`, from the published product
  rule for lower-block representatives.
- `inverseTranspose_rankInclusion`: `ᵗdiag(B,1)⁻¹ = diag(ᵗB⁻¹, 1)`.
- `inverseWhittaker_mul_inverseTranspose_lowerRow`: for an inverse Whittaker function `f'` on
  `GL_(m+2)`, `f'(diag(B,1) ᵗū_x⁻¹) = ψ(Σ_j B_(m,j) x_j) f'(diag(B,1))`. Indeed
  `diag(B,1) ᵗū_x⁻¹ = ᵗū_y⁻¹ diag(B,1)` with `y = x ᵗB`, and `f'` transforms under the upper
  unipotent `ᵗū_y⁻¹` by `ψ(-(-y_m))`.
- `weylLong_mul_inverseTranspose_dual`: `w ᵗ(w ᵗM⁻¹ ū)⁻¹ = M ᵗū⁻¹`.
- `smearedSecondDual_at_dual`: for `Φ(y) = ∫ S(x) f̃'(y ū_x) dx` with `f̃'` the second dual of
  `f'`, `Φ(w ᵗdiag(B,1)⁻¹) = f'(diag(B,1)) ∫ S(x) ψ(Σ_j B_(m,j) x_j) dx`. This is the
  source's identity reducing the dual of the function `F` of formula (10) to `W'` and the
  Fourier transform of the weight.
