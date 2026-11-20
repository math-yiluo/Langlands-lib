# Inner products of restrictions in `H_P`

Module `Langlands.Global.AdelicInducedL2Inner` relates the Hilbert space
`L²(K × M(F)\M(𝔸), β(y(m)) δ_P(m)⁻¹ dk dm)` of `inducedL2Measure` to the induced
inner product `inducedInnerProduct`. It also shows that classes of
square-integrable restrictions of elements of `A^2_P`, and their finite linear
combinations, lie in the Hilbert space `H_P` of `inducedHilbertSpace`. Here
`A^2_P` is `IsSquareIntegrableInducedForm`.

Notation: `H_P` is `characterLog`, `y(m)` are the coordinates
`parameterCoordinates F P e (H_P(m))`, and
`m^{-2ρ_P} = parameterPower F P (-modulusParameter F P) m`, which is
`δ_P(m)⁻¹`.

## Provenance

Internal to the Library. These are bookkeeping identities between the
published definitions `inducedL2Measure`, `inducedRestriction`,
`inducedHilbertSpace` (module `Langlands.Global.AdelicSpectralTransformSpaces`)
and `inducedInnerProduct` (module `Langlands.Global.AdelicInducedInnerProduct`).
That the norm of `H_P` is the inner product `(φ, φ)_P` is the description of
Arthur's space in Arthur 2005, p. 32, and Lapid 2011, §2. No new mathematics
is claimed.

## Declarations

- `continuous_realParameterPairing`: for fixed `μ ∈ X^*(P) ⊗ ℝ`, the pairing
  `H ↦ ⟨μ, H⟩` is continuous on `Hom(X^*(P), ℝ)`. Proof by induction on
  tensors: on `t ⊗ χ` it is `t · H(χ)` (`realParameterPairing_tmul`,
  `continuous_dualEval`), and sums are handled by additivity.

- `parameterPower_neg_modulusParameter`: `m^{-2ρ_P}` equals the real number
  `exp(-H_P(m)(det Ad))`, coerced to `ℂ`. This unfolds `modulusParameter`
  (`1 ⊗ det Ad`) and uses `complexParameterPairing_tmul`.

- `ofReal_norm_parameterPower_neg_modulusParameter`: hence
  `‖m^{-2ρ_P}‖ = m^{-2ρ_P}` (as complex numbers), because the exponential is
  positive.

- `inducedWeight l e β m := β(y(m)) · ‖m^{-2ρ_P}‖`. This is the real density
  that `inducedL2Measure` places at the coset of `m` when `m` is the chosen
  representative `x.out`.

- `characterLog_map_rational_mul`: `H_P(γ m) = H_P(m)` for `γ ∈ M(F)`, because
  `H_P` is a homomorphism that vanishes on rational points
  (`characterLog_mul`, `characterLog_map`, `characterLog_rational`).
  `inducedWeight_rational_mul` deduces that the weight is left
  `M(F)`-invariant.

- `inducedWeight_nonneg`: the weight is nonnegative when `β` is.
  `continuous_inducedWeight`: it is continuous when `β` is. It is built from
  `continuous_characterLog`, `continuous_characterLog_eval`, the continuity of
  `map F M P l`, and the formula above for `m^{-2ρ_P}`.

- `measurable_inducedWeight_out`: for continuous `β`, the function
  `q ↦ inducedWeight (q.out)` on `M(F)\M(𝔸)` is measurable. It is the
  descent `LeftCosetSpace.lift` of the continuous `M(F)`-invariant weight, and
  such descents are measurable by `measurable_from_quotient`.

- Instance `sFinite_discreteQuotientMeasure`: for an s-finite measure `μ_M`,
  the quotient measure `discreteQuotientMeasure` on `M(F)\M(𝔸)` is s-finite.
  It is a pushforward of a restriction of `μ_M`.

- `inner_eq_inducedInnerProduct`: let `β` be continuous and nonnegative, and
  `μ_M` s-finite. If `f, g ∈ L²(inducedL2Measure)` are a.e. equal to the
  restrictions `(k, m) ↦ φ(mk)` and `(k, m) ↦ ψ(mk)`, then
  `⟪f, g⟫ = inducedInnerProduct … ψ φ`. Mathlib's inner product is conjugate
  linear in the first variable and `inducedInnerProduct` in the second, hence
  the order `ψ φ`. Proof:
  - write `inducedL2Measure` as `withDensity` of the product measure with the
    measurable, finite density `ofReal (inducedWeight (x.2.out))`;
  - the pointwise inner product `conj(f) g` is a.e. equal to
    `conj(φ(mk)) ψ(mk)`, which is integrable (`L2.integrable_inner`);
  - `integral_withDensity_eq_integral_toReal_smul` turns the integral into an
    integral against the product measure, and `integral_prod` (Fubini) turns
    that into an iterated integral `∫_K ∫_{M(F)\M(𝔸)}`;
  - the two integrands agree pointwise by the formula
    `‖m^{-2ρ_P}‖ = m^{-2ρ_P}`.

- `toLp_mem_inducedHilbertSpace`: if `φ ∈ A^2_P` and its restriction is in
  `L²(inducedL2Measure)`, its class lies in `H_P`. The class lies in the
  generating set of `H_P`, and `H_P` contains the span of that set
  (`Submodule.le_topologicalClosure`).

- `sum_smul_toLp_mem_inducedHilbertSpace`: for `ψ_1, …, ψ_m ∈ A^2_P` with
  square-integrable restrictions and scalars `c_q`, the class `∑ c_q [ψ_q]`
  lies in `H_P`. It is a.e. equal to the restriction of the function
  `g ↦ ∑ c_q ψ_q(g)`. Membership follows from the previous item by closure
  under sums and scalars. The a.e. identity combines `Lp.coeFn_finsetSum`,
  `Lp.coeFn_smul`, and `MemLp.coeFn_toLp`.
