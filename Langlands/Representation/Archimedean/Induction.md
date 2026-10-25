# Induced representations, intertwining and Jacquet integrals over `ℝ` and `ℂ`

Author: Worker 35. Definition contribution to task
`91266440-3276-48dc-ab77-8d1c1fa386e8`, revision 1.
This is the second archimedean unit for Shahidi's Theorem 3.1 (1985),
after `Langlands.Representation.Archimedean.GeneralLinear`. For
`F = ℝ` or `ℂ` and a Banach representation `σ` of `GL_m(F) × GL_n(F)`, it
defines:

- the normalized determinant characters;
- the smooth sections of the induced representations `I(s, σ)` and
  `I(-s, σ̃)` of `GL_{m+n}(F)`, with the group acting by right translation;
- the vector-valued intertwining integral `A`;
- the Jacquet integrals of both induced representations;
- the analytic continuation of the target Jacquet integral along flat
  families of sections;
- Shahidi's local-coefficient relation `λ(f) = C λ'(A f)`.

Lean proves the submodule and representation axioms, evaluation formulas
and three uniqueness statements. It proves nothing about convergence,
continuation or existence of local coefficients. The Lean definitions
take an arbitrary representation `σ` and arbitrary linear functionals;
the hypotheses of Shahidi's theorem (an irreducible admissible generic
`σ`, Whittaker functionals) are left to the later statement.

## Mathematical content

The namespace is `Langlands.Archimedean`, and `F` is any `RCLike` field.
As in `GeneralLinear`, `GL_r(F)` is the real Lie group
`Langlands.GeneralLinear r F` with model `matrixModel F r`. Every
smoothness condition is real smoothness, so `GL_r(ℂ)` is treated as a
real group. `E` is a complex normed space.

### Characters

- `normalizedAbsUnits F` is the homomorphism `Fˣ → ℝ≥0ˣ`,
  `x ↦ |x|_F = ‖x‖^[F:ℝ]`: the usual absolute value over `ℝ` and its
  square over `ℂ` (`normalizedAbsUnits_apply`).
  `normalizedDeterminantAbs F n` is `g ↦ |det g|_F` on `GL_n(F)`
  (`normalizedDeterminantAbs_apply`).
- `sourceCharacter F m n s` is the character
  `(h₁, h₂) ↦ |det h₁|^((s+n)/2) |det h₂|^(-(s+m)/2)` of
  `GL_m(F) × GL_n(F)`, built with the Library's `Shahidi.complexPower`
  (`sourceCharacter_apply`). It is the product of the twist
  `|det h₁|^(s/2) |det h₂|^(-s/2)` and the square root
  `|det h₁|^(n/2) |det h₂|^(-m/2)` of the modulus character of the
  parabolic subgroup `P` of type `(m, n)`.
- `targetCharacter F m n s` is the character
  `(h₂, h₁) ↦ |det h₂|^((m-s)/2) |det h₁|^((s-n)/2)` of
  `GL_n(F) × GL_m(F)` (`targetCharacter_apply`). It is the product of the
  twist `|det h₂|^(-s/2) |det h₁|^(s/2)` and the half modulus of the
  parabolic subgroup `P'` of type `(n, m)`.

### Smooth sections and induced representations

For a group `L` with a manifold structure modelled by `IL`, a homomorphism
`ι : L → GL_r(F)`, a function `u : X → GL_r(F)`, a representation
`σ : L →* (E →L[ℂ] E)` and a character `χ : L →* ℂˣ`:

- `inducedSpace F IL ι u σ χ` is the complex subspace of functions
  `f : GL_r(F) → E` that are real `C^∞`, take values in the smooth vectors
  `smoothVectors IL σ`, and satisfy
  `f(ι(h) u(x) g) = χ(h) σ(h) f(g)` for all `h`, `x` and `g`
  (`mem_inducedSpace_iff`).
- `sectionValues` regards a section as a function with values in the
  smooth vectors (`sectionValues_apply`).
- `inducedRepresentation` is the representation of `GL_r(F)` on
  `inducedSpace` by right translation,
  `(g · f)(x) = f(x g)` (`inducedRepresentation_apply`).

### The pair `I(s, σ)` and `I(-s, σ̃)`

- `sourceLevi F m n` is the block-diagonal embedding
  `(h₁, h₂) ↦ diag(h₁, h₂)` of `GL_m × GL_n` into `GL_{m+n}` (the
  Library's `GeneralLinear.blockSum`). `targetLevi F m n` is
  `(h₂, h₁) ↦ diag(h₂, h₁)` from `GL_n × GL_m`, moved to the same group
  `GL_{m+n}(F)` by the Library's `Shahidi.swapRank`.
- `exchange F m n σ` is the representation `σ̃(h₂, h₁) = σ(h₁, h₂)` of
  `GL_n × GL_m` on the same space `E` (`exchange_apply`).
- `sourceSpace F m n σ s` is `inducedSpace` for `pairModel F m n`,
  `sourceLevi`, the Library's upper radical
  `Shahidi.upper m n F a = [[I_m, a], [0, I_n]]`, `σ` and
  `sourceCharacter`. Its elements are the smooth `f` with
  `f(diag(h₁, h₂) [[I_m, a], [0, I_n]] g) =
  |det h₁|^((s+n)/2) |det h₂|^(-(s+m)/2) σ(h₁, h₂) f(g)`.
  `sourceRepresentation` is right translation on it.
- `targetSpace F m n σ s` is `inducedSpace` for `pairModel F n m`,
  `targetLevi`, the Library's exchanged radical
  `Shahidi.intertwiningUnipotent m n F a = [[I_n, a], [0, I_m]]` (the
  radical `U'` of `P'`), `exchange σ` and `targetCharacter`.
  `targetRepresentation` is right translation on it.

### The integrals

Fix a measurable structure on `F` and an additive Haar measure `μ`
(the Library's `AdditiveHaarMeasure`, with no normalization).
`entryMeasure F μ p q` is the product measure `∏ da_{ij}` on `p × q`
matrices with `μ` on every entry (the Library's
`Shahidi.matrixCoordinateMeasure`); it is a Haar measure on
`M_{p×q}(F)`. "Converges absolutely" below means Mathlib's `Integrable`,
and the integrals are Bochner integrals.

- `HasIntertwiningIntegral F μ m n σ s f A`, for a Banach space `E`,
  `f ∈ sourceSpace` and `A ∈ targetSpace`: for every `g`, the integral
  `∫ f(w u'(a) g) da` over `n × m` matrices `a` converges absolutely in
  `E` and equals `A(g)`. Here `w` is the Library's all-positive
  `Shahidi.blockWeyl m n F = [[0, I_m], [I_n, 0]]`, `u'(a)` is
  `intertwiningUnipotent`, and the integrand is the Library's
  `Shahidi.intertwiningIntegrand`. `hasIntertwiningIntegral_unique`: `A`
  is determined by `f`.
- From here on the ranks are `m + 1` and `n + 1`, because the Library's
  Whittaker character is defined at positive rank, and `ψ` is a Library
  `UnitaryAdditiveCharacter F`. `HasJacquetIntegral F μ m n s ψ σ ℓ f z`,
  for a linear functional `ℓ` on the smooth vectors of `σ`: the integral
  `λ(f) = ∫ conj(χ(u'(a))) ℓ(f(w u'(a))) da` converges absolutely to `z`.
  Here `χ` is the standard Whittaker character of `GL_{m+n+2}` built from
  `ψ` (`u ↦ ψ(∑ u_{i,i+1})`), restricted to `U'`, and the integrand is the
  Library's `Shahidi.jacquetIntegrand`.
- `HasSwappedJacquetIntegral F μ m n s ψ σ ℓ' f' z`, for
  `f' ∈ targetSpace` and a linear functional `ℓ'` on the smooth vectors of
  `σ̃`: the integral `λ'(f') = ∫ conj(χ(u(a))) ℓ'(f'(w⁻¹ u(a))) da` over
  `(m+1) × (n+1)` matrices converges absolutely to `z`, with
  `u(a) = Shahidi.upper (m+1) (n+1) F a` and the Library's
  `Shahidi.swappedJacquetIntegrand`.
- `hasJacquetIntegral_unique` and `hasSwappedJacquetIntegral_unique`: the
  values are unique.

### Continuation and the local coefficient

- `IsFlatTargetFamily F m n σ φ`, for a family
  `φ(t) ∈ targetSpace F (m+1) (n+1) σ t`, `t ∈ ℂ`: all `φ(t)` agree on the
  unitary group `K = unitaryCompact F (m+n+2)` (`O(m+n+2)` or
  `U(m+n+2)`). This is a constant family in the compact picture.
- `HasContinuedSwappedJacquetIntegral F μ m n s ψ σ ℓ' f' z`, for
  `f' ∈ targetSpace F (m+1) (n+1) σ s`: there are a flat family `φ` with
  `φ(s) = f'`, an entire function `J : ℂ → ℂ` (Mathlib's
  `Differentiable ℂ`) and a real `a` such that for every `t` with
  `Re t < a` the Jacquet integral `λ'(φ(t))` converges absolutely to
  `J(t)`, and `z = J(s)`. If `Re s < a`, then `z` is the absolutely
  convergent value at `f'`.
- `SatisfiesLocalCoefficientRelation F μ m n s ψ σ ℓ ℓ' f a b`, for a
  Banach space `E` and `f ∈ sourceSpace F (m+1) (n+1) σ s`: there are
  `A`, `z` and `z'` such that `A` is the intertwining integral of `f`,
  the Jacquet integral `λ(f)` converges absolutely to `z`, the continued
  Jacquet integral `λ'(A)` is `z'`, and `a z = b z'`.
- `IsLocalCoefficientAt F μ m n s ψ σ ℓ ℓ' c`: the relation holds with
  `(a, b) = (1, c)` for every section `f` of `I(s, σ)`, so
  `λ(f) = c λ'(A f)`.

The two-scalar form also allows the later statement to use the
multiplied relation `a λ(f) = b λ'(A f)`, with `a` and `b` built from
`L`- and `ε`-factors, without dividing by them.

Degenerate cases, which the definitions do not exclude:

- `c ≠ 0` is not required. If some `λ(f)` is nonzero, then `c ≠ 0`
  follows from the relation.
- `c` is unique if some value `λ'(A f)` is nonzero. If `λ'(A f) = 0` for
  every `f` (for instance `ℓ' = 0`), then any `c` works when every `λ(f)`
  vanishes and no `c` works otherwise. In Shahidi's setting,
  `κ(w(ν), w(σ)) ∘ A(ν, σ, w)` is not identically zero for `ν` in an open
  dense set (printed p.988-989).
- The predicates are false at `s` if some intertwining integral or
  Jacquet integral `λ(f)` fails to converge absolutely. In Shahidi's
  setting they converge for `Re s` large (see below).

## Instances, universes and scope

The file sets `set_option backward.isDefEq.respectTransparency false`, as
`GeneralLinear` and the Library's `Langlands.Global.ArchimedeanGL` do.
This option affects elaboration only.

`[CompleteSpace E]` is assumed exactly where an `E`-valued integral
occurs: `HasIntertwiningIntegral`, its uniqueness theorem,
`SatisfiesLocalCoefficientRelation` and `IsLocalCoefficientAt`. Mathlib
defines the Bochner integral as `0` on an incomplete space, so the
intertwining integral would be meaningless there. The Jacquet integrals
are scalar and need no completeness. The definitions assume only
`[MeasurableSpace F]` and an additive Haar measure; no `BorelSpace F`
hypothesis occurs in any declaration. The intended application is `F`
with its Borel structure, where every additive Haar measure is a positive
multiple of Lebesgue measure (`ℝ`) or of `dx dy` (`ℂ`). The
declarations are universe-polymorphic.

Not proved in Lean: convergence of any integral, smoothness of `A f`,
existence of flat families or of the continuation, uniqueness of the
continued value, and existence of local coefficients. The Lean
definitions do not require `σ` to be continuous, irreducible or
generic, or `ℓ` and `ℓ'` to be continuous Whittaker functionals.
Normalized intertwining operators, `K`-types and the gamma-factor
comparison are not part of this module.

## Original source correspondence

F. Shahidi, *Local coefficients as Artin factors for real groups*, Duke
Math. J. 52 (1985), 973–1007 (literature id `shahidi-1985-real-artin`;
PDF page = printed page − 972). The reused Library integrands come from
F. Shahidi, *Fourier transforms of intertwining operators and Plancherel
measures for GL(n)*, Amer. J. Math. 106 (1984), 67–111 (literature id
`shahidi-1984-fourier`).

- Printed p.976 (PDF 4), §0: for a Banach representation `σ₀` of `M_θ°`
  and `ν ∈ (𝔞_θ)*_ℂ`, `I(ν, σ₀, θ) = Ind σ₀ ⊗ e^ν` is "the left inverse
  action of `G`" on the functions `f` with values in `H(σ₀)` satisfying
  (1) `f(xman) = σ₀(m⁻¹) e^{-(ν+ρ_θ)(log a)} f(x)` for `a ∈ A_θ`,
  `m ∈ M_θ°`, `n ∈ N_θ`, and (2) continuity. For a differentiable
  representation on a Fréchet space the space is the `C^∞` functions with
  (1). Here `ρ_θ` is half the sum of the roots in `N_θ`, so `e^{ρ_θ(log a)}`
  is the square root of the modulus character of `P_θ`.
- Printed p.977 (PDF 5): `I(ν, σ_∞, θ) = I(ν, σ, θ)_∞`, the
  representation on the smooth vectors of the induced Banach
  representation.
- Printed p.978 (PDF 6), Proposition 1.2: the Whittaker integral uses
  "a representative" of the long Weyl element, with no further
  normalization.
- Printed p.985 (PDF 13): `w̃_θ = w̃_l w̃_{l,θ}`, where `w̃_{l,θ}` is the
  longest element of `W(A_M) = W(M, A_M)` and `w̃_l` that of
  `W = W(A_0)` (p.977-978), with
  representative `w_θ = w_l w_{l,θ}` (representatives fixed "as in
  Proposition 1.2"), and `N' = N_{w_θ(θ)}`. Lemma 2.3, (2.2):
  `κ(f) = ∫_{N'} λ(f(n' w_θ)) χ(n') dn'` converges absolutely for
  `Re ν(H_α) ≫ 0` and is a continuous Whittaker functional.
- Printed p.987 (PDF 15), Corollary to Proposition 2.4: `κ(ν, σ)` extends
  to an entire function of `ν ∈ (𝔞_θ)*_ℂ`, and for every `ν` it is a
  nonzero Whittaker functional.
- Printed p.988 (PDF 16), §3: (3.1)
  `A(ν, σ, w) f(g) = ∫_{N_w} f(gnw) dn` with `N_w = U ∩ w N_θ⁻ w⁻¹` (also
  (3.2)) converges absolutely for `Re ν(H_α)` large, and
  `A f ∈ V(w(ν), w(σ), w(θ))_∞`. The functional `κ(w(ν), w(σ))` is
  defined through "analytic continuation of `κ(ν, σ)` to other chambers".
  (3.3): `κ(ν, σ)(f) = C_χ(ν, σ, θ, w) κ(w(ν), w(σ))(A(ν, σ, w) f)` for
  `Re ν(H_α) ≫ 0`, where `C_χ` "a priori may be identically infinity".
- Printed p.989 (PDF 17): the representative `w` of Theorem 3.1 is the
  product of the rank-one representatives `[[0, -1], [1, 0]]`, fixed on
  p.979 (PDF 7) for Lemma 1.4 (p.980, PDF 8), along a reduced
  decomposition.
- Shahidi 1984, printed pp.72-73 (PDF 7-8; PDF page = printed page − 65),
  (0.1)–(0.3) and the swapped functional `λ_{π'}^{-s}` after (0.3): the
  same integrals and relation for `GL_{m+n}` over a nonarchimedean field,
  with `I(s, π) = Ind π₁|det|^{s/2} ⊗ π₂|det|^{-s/2}`, the Weyl
  representative `w_{m,n}`, and the remark on p.73 that `C_χ(s, π)`
  depends on the measures. The Library implements its integrands over any
  field; this unit evaluates them on archimedean sections. The exponents
  `(s+n)/2` and `-(s+m)/2` of `sourceCharacter` are the normalized reading
  of the printed display on p.72 adopted by the Library's
  `Langlands.Representation.Shahidi.Induction` (see its Markdown); they
  also agree with Shahidi 1985 (1), where `e^{ρ_θ}` is the half modulus.

### Derived choices

These points explain the formalization; none is proved in Lean.

1. **Left-inverse versus right-translation convention.** For `f` in
   Shahidi's space, set `f̌(x) = f(x⁻¹)`. Then (1) becomes
   `f̌(m a n x) = e^{(ν+ρ_θ)(log a)} σ₀(m) f̌(x)`, and the left inverse
   action becomes right translation of `f̌`. This is the convention of
   `inducedSpace`, of Shahidi 1984 and of the Library. Smoothness and the
   smooth-vector values are unchanged.
2. **Spaces and parameters.** Write `σ = σ₀ ⊗ e^μ` as in Derived
   choice 1 of `GeneralLinear.md`, and let `ϖ ∈ (𝔞_θ)*` be defined by
   `e^{ϖ(log a)} = |det a₁|^{1/2} |det a₂|^{-1/2}`. The twist in
   `sourceCharacter` is `e^{sϖ}`, so under `f ↦ f̌` the space
   `sourceSpace F m n σ s` is Shahidi's `V(μ + sϖ, σ₀, θ)_∞` for the
   parabolic subgroup of type `(m, n)`. `ϖ(H_α) > 0`, so Shahidi's
   `Re ν(H_α) ≫ 0` is `Re s ≫ 0`. Likewise `targetSpace` is
   `V(w(μ + sϖ), w(σ₀), w(θ))_∞`, since `w⁻¹ diag(h₂, h₁) w = diag(h₁, h₂)`
   gives `w(σ) = σ̃`. Shahidi works with `C^∞` functions into the Fréchet
   space `H(σ)_∞`; `inducedSpace` uses `C^∞` functions into the Banach
   space `E` with values in smooth vectors. By (1), the values of a smooth
   section are automatically smooth vectors, and the two spaces agree
   (p.977, with Shahidi's reference [23]).
3. **Intertwining integral.** Under `f ↦ f̌`, (3.1) becomes
   `(A f)ˇ(g) = ∫_{N_w} f̌(w⁻¹ n g) dn`, because Haar measure on `N_w` is
   inversion invariant. For `M = GL_m × GL_n`, the representative of
   p.989 is `w = [[0, (-1)^m I_n], [I_m, 0]] = w_{m,n}⁻¹ z`, where
   `w_{m,n}` is the Library's `blockWeyl m n` and
   `z = diag(I_m, (-1)^m I_n)`; for `m = n = 1` this is `[[0, -1], [1, 0]]`.
   Then `N_w = w_{m,n}⁻¹ N⁻ w_{m,n} = U'`, and since `z` lies in the Levi
   subgroup with `|det| = 1`, Shahidi's `A` is `σ(I_m, (-1)^m I_n)` times
   the `A` of this module. For irreducible `σ` that central element acts
   by a scalar `±1` (Schur's lemma).
4. **Jacquet integrals.** For the parabolic subgroup of type `(m, n)` of
   `GL_{m+n}`, the permutation matrix of `w̃_θ = w̃_l w̃_{l,θ}` is
   `w_{m,n}⁻¹ = [[0, I_n], [I_m, 0]]`. Then `w_θ(θ)` is the set of simple
   roots of the Levi subgroup `GL_n × GL_m`, so
   `N' = N_{w_θ(θ)} = w_θ N_θ⁻ w_θ⁻¹ = U'`.
   Substituting `n' ↦ n'⁻¹` in (2.2) gives
   `κ(f) = ∫_{U'} conj(χ(n')) λ(f̌(w_θ⁻¹ n')) dn'`, the Library's
   `jacquetIntegrand` with the representative `w_{m,n}`. Proposition 1.2
   allows any representative. Another representative of the same Weyl
   element is `w_θ t` with `t = diag(t₁, t₂)` in the diagonal torus, which
   lies in the Levi subgroup `GL_m × GL_n`. In (2.2) it gives `f(n' w_θ t)`,
   that is `f̌(t⁻¹ w_θ⁻¹ n')`, and the covariance of `sourceSpace` gives
   `f̌(t⁻¹ x) = χ_s(t)⁻¹ σ(t⁻¹) f̌(x)`, where `χ_s = sourceCharacter F m n s`,
   `χ_s(t) = |det t₁|^{(s+n)/2} |det t₂|^{-(s+m)/2}`. So the new functional
   is `χ_s(t)⁻¹` times the old one with `ℓ` replaced by `ℓ ∘ σ(t⁻¹)`; the
   character `χ` and the domain `N'` do not change. The scalar `χ_s(t)⁻¹`
   depends on `s` and is in general not `1`: for `GL_2(ℝ)`, trivial `σ` and
   `t = diag(2, 1)` it is `2^{-(s+1)/2}`, which is `1/2` at `s = 1`. It is
   `1` when all diagonal entries of `t` have absolute value `1`, as for the
   sign matrix `z` of Derived choice 3. Matching the functionals and
   characters of Shahidi's Theorem 3.1 is left to the later statement. The target functional is
   the same construction for the parabolic subgroup of type `(n, m)`,
   which is the Library's `swappedJacquetIntegrand`.
5. **Continuation.** Shahidi continues `κ` analytically in `ν` (Corollary
   to Proposition 2.4). The parameter of `I(-t, σ̃)` is `w(μ + tϖ)`, so its
   Jacquet integral converges absolutely for `Re t ≪ 0`. Already for
   `GL_2` the integrand is `|x|^{s-1}` at infinity, and at `Re s ≫ 0`
   only the continuation is defined. `HasContinuedSwappedJacquetIntegral`
   continues along flat families. Since `G = P'K` (Iwasawa), a section is
   determined by its restriction to `K`, so a flat family through `f'` is
   unique if it exists. It does exist: with `g = p k`, `p ∈ P'` and
   `k ∈ K`, the absolute values `|det h₁|` and `|det h₂|` of the Levi
   blocks of `p` are smooth positive functions of `g` (the Gram
   determinant of the last `m+1` rows of `g` is `‖det h₁‖²`), so
   `φ(t) = e_t f'` with
   `e_t(g) = |det h₂|^{(s-t)/2} |det h₁|^{(t-s)/2}` is smooth. By the
   identity theorem, the entire function `J` and so `z` are then unique.
   None of this is proved in Lean.
6. **Measures.** Shahidi 1984 (p.73) notes that the local coefficient
   depends on the measures. `μ` is an arbitrary Haar measure on `F`, the
   same for the three integrals. Shahidi's explicit formulas use Tate's
   measures (p.980, PDF 8, immediately before Lemma 1.4).
7. **Local coefficient.** `IsLocalCoefficientAt c` is (3.3) with
   `C_χ = c`, in the orientation `λ(f) = c λ'(A f)` of both papers (Shahidi
   1984 writes it as `λ'(A f) = C⁻¹ λ(f)`). By Derived choices 3 and 4,
   if Shahidi's `A` uses the representative `w` of p.989 and his
   functionals (2.2) use the same `ℓ`, `ℓ'` and the permutation-matrix
   representatives (`w_{m,n}⁻¹` for the source and its analogue for the
   target), then `c` is `σ(I_m, (-1)^m I_n) C_χ`. Other representatives
   in (2.2) change this by the scalars and the twists of `ℓ`, `ℓ'`
   described in Derived choice 4.

## Relation to other Library units

The geometry (`blockWeyl`, `upper`, `intertwiningUnipotent`,
`swapRank`), the integrands (`intertwiningIntegrand`, `jacquetIntegrand`,
`swappedJacquetIntegrand`), the coordinate measures and `complexPower`
are the Library's field-general Shahidi 1984 objects, reused without
change. The Library's nonarchimedean relations in
`Langlands.Representation.Shahidi` use stabilized integrals over compact
open subgroups and the nonarchimedean induced spaces; this module uses
absolutely convergent integrals and smooth sections instead. The
statement of Shahidi's Theorem 3.1 for `GL_m × GL_n`, comparing the local
coefficient with the archimedean gamma factors of the Library's
`Langlands.LocalFactor` modules, is a planned later unit.
