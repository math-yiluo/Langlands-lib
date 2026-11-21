# Finite products for the real unfolded equal-rank integral in the dominant chamber

**Source.** Hervé Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §8.2, pp. 55–58. There the unfolded integral (8.1) of a pair `W` on `GL_{t+1}` and `V` on `GL_{t+2}` with a square Schwartz test is compared with finite sums of products of lower-rank integrals. A compact average of right translates of `V` is a finite sum `Σ_j V_j(x) b_j(g)`, and a compact weight reproduces the square test. Inserting this weight and integrating separately over the quotient and the matrix group gives products of corank-one integrals `Ψ(s; V_j, W)` and matrix integrals of the `b_j`. This module proves that separation for the real place. It is an internal supporting result. It is the real analogue of the published complex module `ComplexLocalEqualShiftedProducts`. It uses the generic compact-averaging lemmas of `ComplexLocalCompactAveraging` and `ComplexLocalCompactWeight`, which hold for any compact group mapping into a general linear group. It also uses the joint absolute convergence theorem `realLocalEqualJointIntegrability` of `RealLocalEqualJointIntegrability`.

## Notation

Write `m = t + 1` and `n = t + 2`, `G = GL_m(ℝ)`, `H = GL_n(ℝ)`, `U` for the upper unipotent subgroup of `H`, `Q` for the left unipotent quotient of `G`, and `Y` for real `n × n` matrices. `pad : G → H` is the block embedding `h ↦ diag(h, 1)`, and `h(q) = quotientRepresentative t q` is the continuous section of `Q`. The published kernel is

`equalUnfoldedKernel d Ψ W V s (q, g) = Ψ(g) · V(pad(h) g) · d(det g)|det g|^{s + m/2} · W(h) · |det h|^{s - 1/2}`, with `h = h(q)`.

The measure on `Q × H` is `D.measure.prod D'.groupHaar` for real quotient data `D` of rank `t` and `D'` of rank `t + 1`. `determinantWeight c w g = c(det g) · |det g|^w` is the published real determinant weight (`RealGodementSection`). `charData e z` is the real character `x ↦ (x/|x|)^e |x|^z` with parity `e : Fin 2` and exponent `z`. `realUnequalIntegral gap D V' W s` is the published corank-one integral `Ψ(s; V', W) = ∫_Q V'(pad q) W(q) |det q|^{s - 1/2}`, and `realUnequalIntegrand` is its integrand. `realUniformWhittakerModel r ds a` is the published uniform real Whittaker model of rank `r + 1` for the block list `ds` and additive parameter `a`.

## Declarations

- `realWeightedMatrixTest d Ψ w g = Ψ(g) · determinantWeight d w g` (a definition), for a square test `Ψ` on `j × j` matrices and `g ∈ GL_j(ℝ)`.
- `realCompactMatrixTranslate d Ψ g A = d(det g⁻¹) · Ψ(g⁻¹ A)` (a definition), the left translate of a square test by `g`, twisted by the character of `det g⁻¹`.
- `determinantWeight_charData_shift e z w g`. `determinantWeight (charData e z) w g = determinantWeight (charData e 0) (z + w) g`. The exponent of the character moves into the absolute determinant power.
- `norm_determinantWeight_real c w g`. `‖determinantWeight c w g‖ = |det g|^{Re c.exponent + Re w}`.
- `continuous_determinantWeight c z`. The determinant weight is continuous on `GL_j(ℝ)`.
- `realWeightedMatrixTest_reproduce`. Let `K` be any measurable space with a measure `ν`, `ι : K → GL_j(ℝ)` with `|det ι(k)| = 1` for every `k`, and `κ : K → ℂ`. Suppose `∫ κ(k) · realCompactMatrixTranslate d Ψ (ι k) A dν(k) = Ψ(A)` for every matrix `A`. Then for every `w` and `g`, `realWeightedMatrixTest d Ψ w g = ∫ κ(k) · realWeightedMatrixTest d Ψ w ((ι k)⁻¹ g) dν(k)`.
- `exists_realCompactMatrixWeight`. Let `K` be a group with a compact topology, Borel σ-algebra and Haar measure `μ`, and `ι : K →* GL_j(ℝ)` a continuous homomorphism. Let `Ψ` be continuous, and suppose the span of the functions `A ↦ Ψ((ι k)⁻¹ A)`, `k ∈ K`, is finite-dimensional. Then there is a continuous `κ : K → ℂ` whose left translates `k ↦ κ(h⁻¹ k)` span a finite-dimensional space and with `∫ κ(k) · realCompactMatrixTranslate d Ψ (ι k) A dμ(k) = Ψ(A)` for every `A`.
- `integrable_realCompactInsertion`. Let `K` be a compact topological group with Borel σ-algebra and a finite measure `ν`, `μ` a Haar measure on `H`, `ι : K →* H` and `κ` continuous, and `Ψ` a square Schwartz test. Let `V : H → ℂ` be continuous with `‖V(g)‖ ≤ C · realMatrixHeight(g)^N` for some `C ≥ 0` and `N`. If `t + 2 + 2N ≤ Re d.exponent + Re w`, then for every `x ∈ H` the function `(k, g) ↦ κ(k) · realWeightedMatrixTest d Ψ w (ι(k)⁻¹ g) · V(x g)` is integrable for `ν.prod μ`.
- `realUnequalIntegrand_representative`. Let `V ∈ regularFunctions (t + 1) (-a)` and `W ∈ regularFunctions t a`. Then for every `s` and `q ∈ Q`, `realUnequalIntegrand gap V W s q = V(pad(h(q))) · (W(h(q)) · |det h(q)|^{s - 1/2})`. The corank-one integrand may be evaluated at the continuous section instead of the chosen representative `q.out`.
- `RealLocalEqualShiftedProductsStatement t` (a `Prop`) and its proof `realLocalEqualShiftedProducts`. Let `D` and `D'` be real quotient data of ranks `t` and `t + 1`. Let `K` be a compact topological group with Borel σ-algebra and a finite measure `ν`. Let `ι : K →* H` be a continuous homomorphism with `|det ι(k)| = 1` for all `k`, and `κ : K → ℂ` continuous. Let `a ∈ ℝˣ`, `e : Fin 2`, block lists `ds` and `es`, `W ∈ realUniformWhittakerModel t ds a` and `V ∈ realUniformWhittakerModel (t + 1) es (-a)`. Let `Ψ` be a square Schwartz test reproduced by `κ`: `∫ κ(k) · realCompactMatrixTranslate (charData e 0) Ψ (ι k) A dν(k) = Ψ(A)` for every `A`. Suppose given `c ∈ ℕ`, functions `V_j, b_j : H → ℂ` and `Z_j : ℂ → ℂ` for `j < c` with these properties.
  - Each `V_j ∈ realUniformWhittakerModel (t + 1) es (-a)`.
  - For all `x, g ∈ H`, `∫ κ(k) V(x ι(k) g) dν(k) = Σ_j V_j(x) b_j(g)`.
  - There is `β` such that for every `w` with `Re w > β` and every `j`, the function `g ↦ realWeightedMatrixTest (charData e 0) Ψ (w + m/2) g · b_j(g)` is integrable for `D'.groupHaar`, and `Z_j(w)` is its integral.

  Then there are real `τ` and `σ` such that for all `z, s ∈ ℂ` with `Re z > τ` and `Re s > σ`,

  `∫ equalUnfoldedKernel (charData e z) Ψ W V s = Σ_j realUnequalIntegral gap D V_j W s · Z_j(s + z)`.

  Only the spectral variable of the matrix integrals receives the separated exponent `z`.

All other declarations are private helpers or local instances (Borel σ-algebras, local compactness and second countability of `GL_{j+1}(ℝ)`, σ-compactness of the left unipotent quotient).

## Implemented proof

*Determinant weights.* `determinantWeight_charData_shift` unfolds `charData_character_apply`. With `charData e z`, the sign part `(det/|det|)^e` is unchanged and `|det|^z |det|^w = |det|^{z + w}` (`Complex.cpow_add`, since `|det g| ≠ 0`). `norm_determinantWeight_real` uses `character_eq`. The sign factor has norm one, and `‖|x|^w‖ = |x|^{Re w}` for `|x| > 0` (`Complex.norm_cpow_eq_rpow_re_of_pos`). Continuity follows from continuity of the determinant, of the character, and of `x ↦ x^z` on the slit plane, which contains `|det g| > 0`.

*Reproduction.* If `|det ι(k)| = 1` then `|det ι(k)⁻¹| = 1`, so `determinantWeight d w (ι k)⁻¹ = d(det (ι k)⁻¹)`. The weight is multiplicative, so `realWeightedMatrixTest d Ψ w ((ι k)⁻¹ g) = realCompactMatrixTranslate d Ψ (ι k) g · determinantWeight d w g`. Integrate against `κ` and use the hypothesis at `A = g` (`integral_mul_const`).

*Existence of a reproducing weight.* Apply the published `ComplexJacquet.exists_compactWeight_of_finite_orbit` to `F(k) = realCompactMatrixTranslate d Ψ (ι k)`. Each `F(k)(A)` is continuous in `k` because `ι`, inversion, the determinant, the character and `Ψ` are continuous. Each `F(k)` is a scalar multiple of `A ↦ Ψ((ι k)⁻¹ A)`, so the span of the `F(k)` lies in the finite-dimensional span of the hypothesis (`Submodule.finiteDimensional_of_le`). Scalar covariance holds: `F(h⁻¹k)(A) = d(det ι(h)) · F(k)(ι(h) A)`. The published lemma gives a continuous `κ` with finite-dimensional translates and `∫ κ(k) F(k)(A) = F(1)(A)`, and `F(1) = Ψ`.

*Compact insertion integrability.* By the published shear `ComplexJacquet.integrable_compact_average_iff`, it suffices to show that `(k, g) ↦ A(g) · κ(k) V(x ι(k) g)` is integrable, where `A = realWeightedMatrixTest d Ψ w`. Write `E = realMatrixHeight`. It is submultiplicative (`realMatrixHeight_mul_le`), so `‖V(x ι(k) g)‖ ≤ C · E(x ι(k))^N · E(g)^N`. The integrand is therefore dominated by `T(k) · B(g)` with `T(k) = C · E(x ι(k))^N · ‖κ(k)‖` and `B(g) = E(g)^N · ‖A(g)‖`. `T` is continuous on the compact group, hence integrable for the finite measure `ν`. By `norm_determinantWeight_real`, `B(g) = ‖Ψ(g)‖ · E(g)^N · |det g|^{Re d.exponent + Re w}`, which is integrable by the published `integrable_realMatrixWeightedNorm` because the exponent is at least `n + 2N`. Then `Integrable.mul_prod` and the continuity of the integrand finish the argument.

*Quotient representatives.* Write `q.out = v · h(q)` with `v = RealIwasawa.npart q.out` upper unipotent (`unipotentQuotientHomeomorph`). The padding of `v` is upper unipotent in `H`, and `det v = 1`. The Whittaker laws give `V(pad(v) pad(h)) = θ_{-a}(v) V(pad h)` and `W(v h) = θ_a(v) W(h)`. The characters cancel, `θ_a(v) θ_{-a}(v) = 1` (`realWhittakerCharacter_mul_neg`, together with `realWhittakerCharacter_padGL`).

*Finite products.* By `realUniformWhittakerRegularity`, `W` and `V` are regular with uniform derivative growth. Hence they are continuous and satisfy the real gauge estimate (`RealWhittakerGauge.exists_gauge_bound`). Also `‖V(u g)‖ = ‖V(g)‖` for `u ∈ U`, and `V` has a polynomial height bound with constants `C_V, N_V`. So `realLocalEqualJointIntegrability` applies and gives thresholds `ρ` and `σ_J`. For each `j`, `RealUnequalConvergence.exists_convergence_of_regular` gives a threshold `σ_j` above which the corank-one integrand of `(V_j, W)` is integrable. Let `β_Q` bound the finitely many `σ_j`. Take

`τ = max ρ 0` and `σ = max σ_J (max σ₀ (max β β_Q))`, with `σ₀ = t + 2 + 2 N_V - (t + 1)/2`.

Fix `Re z > τ` and `Re s > σ`. By `determinantWeight_charData_shift` the kernel at `charData e z` is `A(g) · F(q, g)`, where

`A = realWeightedMatrixTest (charData e 0) Ψ (s + z + m/2)` and `F(q, g) = V(pad(h(q)) g) · W(h(q)) |det h(q)|^{s - 1/2}`.

The product `A(g) F(q, g)` is integrable on `Q × H` by `realLocalEqualJointIntegrability`, since `Re z > ρ` and `Re s > σ_J`. For each `q`, `integrable_realCompactInsertion` with `x = pad(h(q))` and `w = s + z + m/2` makes the compact insertion integrable. Its exponent condition `t + 2 + 2N_V ≤ Re(s + z) + (t + 1)/2` holds because `Re z > 0` and `Re s > σ₀`. The weighted test is reproduced by `realWeightedMatrixTest_reproduce`, using `|det ι(k)| = 1`. At `x = pad(h(q))`, the expansion hypothesis and `realUnequalIntegrand_representative` give

`∫ κ(k) F(q, ι(k) g) dν(k) = Σ_j realUnequalIntegrand gap V_j W s q · b_j(g)`.

Each `realUnequalIntegrand gap V_j W s` is integrable because `Re s > β_Q ≥ σ_j`. Each `A · b_j` is integrable by the hypothesis on `Z_j` at `w = s + z`, since `Re(s + z) > β`. Fubini (`integral_prod_symm`) writes the double integral as `∫_H A(g) ∫_Q F(q, g)`. The published `ComplexJacquet.integral_prod_eq_sum_mul_of_compact_average` turns this into `Σ_j (∫_Q realUnequalIntegrand gap V_j W s) · (∫_H A b_j)`. That lemma is stated for any compact group with a homomorphism into any group with a left-invariant measure. Finally `∫_H A b_j = Z_j(s + z)` by hypothesis.

## Scope

The compact expansion `Σ_j V_j(x) b_j(g)` and the convergence of the matrix integrals `Z_j` are hypotheses here. They are not proved in this module. The identity is proved only in the dominant chamber `Re z > τ`, `Re s > σ`. This module proves no continuation, functional equation or `RealLocalUniformPositiveEqualContinuationStatement`.
