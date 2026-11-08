# The Kirillov shell vector

Module `Langlands.Representation.RankinSelberg.HighlyRamified.KirillovShell`.

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, Proposition (4.1), printed page 326). It constructs the test vector
that the adjacent-rank step of this project takes as its input `KirillovShellInput` (module
`HighlyRamified.AdjacentStep`). That step uses this vector where Jacquet and Shalika use the
vector `W'` of §4.4, (4.4.16)–(4.4.17). The vector here is not the one Jacquet and Shalika
prescribe. It is an internal construction, and the differences are listed under Provenance.

Let `σ` be a generic representation of rank `m + 2` with central character `ω_σ` and a
nonzero functional for the inverse character `ψ⁻¹`. Let `χ` be a continuous character, `ϖ`
a unit and `c : ℕ`. The module constructs a vector `f'` in the Whittaker model of `σ` for
`ψ⁻¹`. Its restriction to `diag(B, 1)` is supported on `N · GL_(m+1)(O) ϖ^(-c)`, and it
equals `χ(det k)⁻¹` at `diag(k ϖ^(-c), 1)` for `k ∈ GL_(m+1)(O)`. It also satisfies
`f'(g · diag(I, d)) = ω_σ(d) χ(d)^(m+1) f'(g)` for `d ∈ O^×`. The vector is a Kirillov lift.
The last theorem proves `KirillovShellInput`.

## Provenance

In Jacquet–Shalika 1985, §4.4, `σ` is a generic representation of `G_(r-1)` (here
`r - 1 = m + 2`), `a` is the conductor exponent of the twisting character `χ`, and `f` is the
common conductor exponent of the twisted candidates. On printed page 328 they take `W'` in
the Whittaker model `𝒲(σ ⊗ χ; ψ⁻¹)` of `σ ⊗ χ` for the inverse character. On printed page
330 they choose `W'` so that the function `H'(g) = W'(diag(g, 1) · diag(w_(r-2), 1))` on
`G_(r-2)` is supported on `ϖ^(-a(r-1)) N_(r-2) K_(r-2)(f)` (4.4.16), and so that
`H'(ϖ^(-a(r-1)) k) = C₁ C₀⁻¹ q^(-a(r-1)(r-2)/2)` (4.4.17). Here `w_(r-2)` is the antidiagonal
Weyl element, `K_(r-2)(f)` is their level-`f` subgroup of `G_(r-2)(O)`, `C₀` is the constant
of (4.4.15) and `C₁` is defined after (4.4.17). They cite no separate statement for the
existence of such a `W'`; it comes from the Kirillov theory of the mirabolic restriction.

The vector `f'` of this module differs from that prescription as follows.

1. `f'` lies in the model of `σ`, not of `σ ⊗ χ`. The map `f' ↦ χ(det g) f'(g)` identifies
   the two models. It sends `f'` to a function that takes the constant value
   `χ(ϖ)^(-c(m+1))` at every `diag(k ϖ^(-c), 1)`, `k ∈ GL_(m+1)(O)`.
2. The support is the full integral shell `N · GL_(m+1)(O) ϖ^(-c)`, not the level-`f` shell
   `ϖ^(-c) N K_(r-2)(f)`. Since `w_(r-2)` is integral and `ϖ^(-c)` is scalar, right
   translation by `diag(w_(r-2), 1)` preserves the full integral shell. So the Weyl
   translation of (4.4.16) has no counterpart here.
3. `c` and `ϖ` are arbitrary; the adjacent-rank step uses `c = a(r-1)`. The value at
   `diag(k ϖ^(-c), 1)` is normalized to `χ(det k)⁻¹`, with no constant
   `C₁ C₀⁻¹ q^(-a(r-1)(r-2)/2)`. (`KirillovShellInput` allows a nonzero constant `κ₁`; here
   `κ₁ = 1`.)
4. The equivariance under `diag(I, d)`, `d ∈ O^×`, is not stated by Jacquet and Shalika. It
   holds because the construction averages over `diag(d I, 1)`, `d ∈ O^×`, with the weight
   `χ(d)^(m+1)`.

The adjacent-rank step needs only the properties stated in `KirillovShellInput`, and it
proves its own identities from them (see `HighlyRamified/AdjacentStep.md`). No comparison
with the vector `W'` of Jacquet and Shalika is proved or used.

The formal statements and proofs here are internal to this project. They use the published
Kirillov transfer `Whittaker.modelKirillovTransfer` with `whittakerTypeKirillov`, the
mirabolic test-function predicate `IsMirabolicTestFunction`, the multiplicative Haar measure
`localMultiplicativeHaar` (mass one on `O^×`), and the project's `AlgebraicIntegral` vector
integrals.

## Declarations

`F` is a field with a valuation (`ValuativeRel`) in the generic sections. In the p-adic
section `F` is a `PadicField`, with its canonical topology, valuation and local-field
structure, and the Borel σ-algebra on `F^×`, as local instances. `O` is the integer ring
and `O^×` is `integralUnits O`. `ri` is `rankInclusion 1 : GL_(m+1) → GL_(m+2)`,
`g ↦ diag(g, 1)`. `S(e)` is the scalar matrix `Matrix.GeneralLinearGroup.scalar _ e`, and
`IsIntegralMatrix k` means that `k` and `k⁻¹` have entries in `O`.

### The integral shell function (generic field)

- `IsIntegralShell g`: `g = u · diag(k, 1)` with `u` upper unipotent and `k` integral.
- `isIntegralMatrix_iff_mem_integralSubgroup`, `determinant_rankInclusion_one`,
  `determinant_upperUnipotent_val`: `IsIntegralMatrix k ↔ k ∈ GL_(m+1)(O)`,
  `det diag(k, 1) = det k`, and `det u = 1` for upper unipotent `u`.
- `integralShell_value_unique hθ χ`: for `θ` trivial on integral upper unipotent matrices,
  two decompositions `u₁ diag(k₁, 1) = u₂ diag(k₂, 1)` give the same value
  `θ(u) χ(det k)⁻¹`. The two decompositions differ by `diag(k₂ k₁⁻¹, 1)`, which is integral,
  upper unipotent, and has determinant `1`.
- `integralShellValue θ χ g`: the value `θ(u) χ(det k)⁻¹` at a shell point
  `g = u diag(k, 1)` (decomposition chosen by `Classical.choose`), and `0` otherwise.
- `integralShellValue_mul`, `integralShellValue_of_not`,
  `integralShellValue_rankInclusion`, `integralShellValue_unipotent_mul`: the value at
  `u diag(k, 1)` is `θ(u) χ(det k)⁻¹`, the value is `0` off the shell, the value at
  `diag(k, 1)` is `χ(det k)⁻¹`, and left multiplication by `u` multiplies the value by
  `θ(u)`.
- `integralShell hθ χ`: the shell function as an element of
  `(equivariantFunctions N θ).toSubmodule`.
- `integralShell_mul_right_aux`, `integralShellValue_mul_right`: right multiplication by
  an integral mirabolic `k` with `χ(det k) = 1` preserves the shell and the value. Write
  `k = r · diag(A, 1)` with `r` in the mirabolic radical (`Mirabolic.projection`,
  `Mirabolic.levi`). Then `u diag(k₀, 1) k = (u r') diag(k₀ A, 1)`, where
  `r' = diag(k₀, 1) r diag(k₀, 1)⁻¹` is integral upper unipotent and `det A = det k`.
- `exists_isIntegralMatrix_of_isIntegralShell`: if `diag(X, 1)` is a shell point, then
  `u₁ X` is integral for some upper unipotent `u₁` of rank `m + 1`.

### Smearing along a continuous map (generic)

- `mapIntegrand ρ hρ ι hι S hS hSc v` and `mapSmear μ ρ hρ ι hι S hS hSc v`: for a smooth
  representation `ρ` of `G`, a continuous map `ι : H → G` and a locally constant compactly
  supported `S : H → ℂ`, these are the finite simple function `x ↦ S(x) ρ(ι x) v` and its
  algebraic integral `∫ S(x) ρ(ι x) v dμ(x)`.
- `mapSmear_dual`: for every linear form `L`,
  `L(mapSmear …) = ∫ S(x) L(ρ(ι x) v) dμ(x)`. This is the published
  `AlgebraicIntegral.integral_linearMap` followed by `integral_eq_bochner`.

### Scalars and `diag(I, d)`

- `isIntegralMatrix_scalar`: `S(e)` is integral for `e ∈ O^×`.
- `rankInclusion_one_castAdd_castAdd`, `…_castAdd_natAdd`, `…_natAdd_castAdd`,
  `…_natAdd_natAdd`: the four blocks of `diag(X, 1)`.
- `lowerBlockPair_eq_scalar_mul c'`: for a `1 × 1` lower triangular `c'` with determinant
  `d`, `lowerBlockPair 1 0 c' = diag(I_(m+1), d) = S_(m+2)(d) · diag(S_(m+1)(d⁻¹), 1)`.
  It is checked entrywise on the four blocks.

### The p-adic construction

- `determinantKernel F χ hχ n` and `unitKernel F χ hχ`: the open subgroups `ker(χ ∘ det)`
  of `GL_(n+1)` and `ker χ` of `F^×` for continuous `χ` (`quasicharacter_isOpen_ker`).
- `isMirabolicTestFunction_integralShell F ψ' hψ' χ hχ`: for `ψ'` trivial on `O`, the shell
  function for the standard character of `ψ'` is a mirabolic test function. On the
  mirabolic subgroup it is right invariant under `GL_(m+2)(O) ∩ ker(χ ∘ det)`, and its
  support lies in `N · ri(GL_(m+1)(O))`, where `ri(GL_(m+1)(O))` is compact.
- `exists_integralShell_vector F ψ hψ σ hσ ℓ' hℓ' χ hχ`: for `ψ` of conductor exponent `0`,
  `σ` `ψ`-generic and `ℓ' ≠ 0` a functional for the inverse standard character, some
  `v₀` satisfies `ℓ'(σ(q) v₀) = integralShellValue θ χ q` for every mirabolic `q`, where `θ`
  is the standard character of `ψ.scale (-1)`.
- `shellScalar F m`: the homomorphism `d ↦ diag(d I_(m+1), 1)`, and
  `continuous_shellScalar`.
- `shellWeight F χ m`: the weight `d ↦ χ(d)^(m+1)` on `O^×`, extended by `0`. The lemmas
  `shellWeight_mul`, `shellWeight_isLocallyConstant` and `shellWeight_hasCompactSupport`
  give `w(k d) = χ(k)^(m+1) w(d)` for `k ∈ O^×`, local constancy, and compact support.
- `exists_kirillovShell F ψ hψ σ hσ ωσ hωσ ℓ' hℓ' χ hχ ϖ c`: let `ψ` have conductor
  exponent `0`, let `σ` on `GL_(m+2)` be `ψ`-generic with central character `ωσ`
  (`Classification.HasGLCentralCharacter`), and let `ℓ' ≠ 0` be a functional for the
  inverse standard character. Let `χ : F^× →* ℂ^×` be continuous, `ϖ ∈ F^×` and `c : ℕ`.
  Then there are `f' ∈ coefficientModel σ ℓ'` and `κ₁ ≠ 0` (in fact `κ₁ = 1`) with:
  1. for every `B ∈ GL_(m+1)`, `f'(diag(B, 1)) ≠ 0` implies that
     `u B S(ϖ^c)` is integral for some upper unipotent `u`;
  2. for every integral `k`, `f'(diag(k S((ϖ^c)⁻¹), 1)) = κ₁ χ(det k)⁻¹`;
  3. for every `g` and every `1 × 1` lower triangular `c'` whose entry is an integral
     unit, `f'(g · lowerBlockPair 1 0 c') = (ωσ χ^(m+1))(det c') f'(g)`.
- `kirillovShellInput : KirillovShellInput.{uF, uW}`: the previous theorem with
  `χ` a quasicharacter and `hχ = χ.continuous`.

## Proof of `exists_kirillovShell`

1. Kirillov lift. `ψ.scale (-1)` is trivial on `O`, since `ψ` is
   (`hasIntegerConductor_of_additiveConductor_eq_zero`) and `-x ∈ O`. Its standard
   character equals the inverse standard character of `ψ`
   (`standardCharacter_scale_neg_one`). So `ℓ'` is a functional for that standard
   character, and `σ` is of Whittaker type for it (`isOfInverseWhittakerType_of_isGeneric`).
   `Whittaker.modelKirillovTransfer whittakerTypeKirillov` lifts the mirabolic test function
   `integralShell` to a model function, and `modelMap_surjective` gives a vector `v₀` with
   `ℓ'(σ(q) v₀) = integralShellValue θ χ q` on the mirabolic subgroup
   (`exists_integralShell_vector`).
2. Translation and average. Put `v₁ = σ(diag(S(ϖ^c), 1)) v₀`. Let `μ` be
   `localMultiplicativeHaar`, and `v₂ = mapSmear μ σ … shellScalar … shellWeight … v₁`,
   the vector `∫ w(e) σ(diag(e I, 1)) v₁ de`. Let `f'` be the coefficient of `v₂` for `ℓ'`.
   By `mapSmear_dual`,
   `f'(g) = ∫ w(e) ℓ'(σ(g · diag(e I, 1)) v₁) dμ(e)`.
   For `X ∈ GL_(m+1)`, the matrix `diag(X, 1) · diag(e I, 1) · diag(S(ϖ^c), 1)` equals
   `diag(X S(e) S(ϖ^c), 1)`, which is mirabolic. Hence
   `ℓ'(σ(diag(X, 1) · diag(e I, 1)) v₁) = integralShellValue θ χ (diag(X S(e) S(ϖ^c), 1))`.
3. Support (condition 1). If `f'(diag(B, 1)) ≠ 0`, the integrand is nonzero at some `e`.
   Then `w(e) ≠ 0`, so `e ∈ O^×`, and `diag(B S(e) S(ϖ^c), 1)` is a shell point. So
   `u₁ B S(e) S(ϖ^c)` is integral for some `u₁`
   (`exists_isIntegralMatrix_of_isIntegralShell`). Multiplying on the right by the integral
   matrix `S(e⁻¹)` (`isIntegralMatrix_scalar`) shows that `u₁ B S(ϖ^c)` is integral, since
   scalars commute.
4. Values (condition 2). For `X = k S((ϖ^c)⁻¹)` with `k` integral, `X S(e) S(ϖ^c) = k S(e)`.
   For `e ∈ O^×`, `k S(e)` is integral. The integrand is then
   `χ(e)^(m+1) · χ(det k · e^(m+1))⁻¹ = χ(det k)⁻¹`, using `determinant_scalar`. For
   `e ∉ O^×` the integrand is `0`. So the integrand is the indicator of `O^×` times
   `χ(det k)⁻¹`, and the integral is `μ(O^×) χ(det k)⁻¹ = χ(det k)⁻¹`
   (`integral_indicator_const`, `localMultiplicativeHaar_integerUnits`).
5. Equivariance (condition 3). Let `d = det c'`. Then `d` is an integral unit, because its
   value is the entry `c'₀₀`. By `lowerBlockPair_eq_scalar_mul`,
   `g · lowerBlockPair 1 0 c' · diag(e I, 1) = S(d) · g · diag(d⁻¹ e I, 1)`, since `S(d)`
   is central (`Matrix.GeneralLinearGroup.scalar_commute`). The central character turns the
   integrand into `ωσ(d) w(e) Φ(d⁻¹ e)` with `Φ(e) = ℓ'(σ(g · diag(e I, 1)) v₁)`. Since
   `w(e) = w(d (d⁻¹ e))`, this is `G(d⁻¹ e)` for `G(e) = ωσ(d) w(d e) Φ(e)`. Left
   invariance of `μ` (`integral_mul_left_eq_self`) removes `d⁻¹`. Then
   `w(d e) = χ(d)^(m+1) w(e)` (`shellWeight_mul`) and `integral_const_mul` give
   `(ωσ χ^(m+1))(d) f'(g)`.
