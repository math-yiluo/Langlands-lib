# Shahidi's local coefficients for `GL_{m+1} × GL_{n+1}` over `ℝ` and `ℂ`

Author: Worker 35. Statement contribution to task
`91266440-3276-48dc-ab77-8d1c1fa386e8`, revision 1.
This is the fourth archimedean unit for Shahidi's Theorem 3.1 (1985). It
builds on `Langlands.Representation.Archimedean.SmoothVectors`,
`GeneralLinear`, `Induction` and `StandardModule`. It states Shahidi's
Theorem 3.1 (`F = ℝ`) and Theorem 3.13 (`F = ℂ`) for the maximal parabolic
subgroup of type `(m+1, n+1)` of `GL_{m+n+2}(F)`. The statement compares the
local coefficient of `Induction` with the Library's archimedean `L`- and
`ε`-factors of the tensor-dual Weil representation `φ₁ ⊗ φ₂^∨`.

The module contains three `Prop`-valued definitions and nothing else. It
introduces no new objects, and Lean proves nothing about the statements.

## The statements

The namespace is `Langlands.Archimedean`. Throughout, `E` is a complex
Banach space and `σ` is a group homomorphism
`GL_{m+1}(F) × GL_{n+1}(F) →* (E →L[ℂ] E)`, with `GL_r(F)` the real Lie
group `Langlands.GeneralLinear r F` of `GeneralLinear`.

### `RealLocalCoefficientGammaStatement`

The statement quantifies over `m n : ℕ`, `E`, `σ`, a unit `a : ℝˣ`, lists
`ds₁ ds₂ : List RealBlock` and `z : ℂ`. Write `ψ = realScaledCharacter a`,
`ψ(x) = e^{2πiax}`, and `φᵢ = realModel dsᵢ`, the Library's actual sum of the
blocks as a representation of the real Weil group. Assume:

1. `IsGenericBanachPairRepresentation ℝ ψ m n σ`. So `σ` is a continuous,
   topologically irreducible, admissible Banach representation with a
   nonzero Whittaker functional for `pairCharacter ℝ ψ m n`, i.e.
   `(u, u') ↦ ψ(∑ u_{i,i+1}) ψ(∑ u'_{j,j+1})`.
2. `HasRealPairParameter σ ds₁ ds₂`. So `σ` is infinitesimally equivalent to
   the external product of the real standard modules of `ds₁` and `ds₂`.
   For such `σ`, `φ₁` and `φ₂` are the Langlands parameters of the two
   factors (`StandardModule.md`, "Scope of the parameter predicates").
3. `σ(1, -1) = z • id`.

Then there is `b : ℝ` with the following property. Take

- a `ψ`-Whittaker functional `ℓ` of `σ` on its smooth vectors
  (`IsWhittakerFunctional` for `pairUnipotent` and `pairCharacter`);
- a linear functional `ℓ'` on the smooth vectors of `σ̃ = exchange σ` that
  agrees with `ℓ` on every vector smooth for both;
- block lists `P` and `Q` with `realModel P ≅ φ₁ ⊗ φ₂^∨` and
  `realModel Q ≅ φ₂ ⊗ φ₁^∨`. Here `≅` is `Nonempty` of the Library's
  `FiniteRepresentation.Equiv`, and the tensor product and dual are the
  Library's `FiniteRepresentation.tensor` and `FiniteRepresentation.dual`;
- `s : ℂ` with `b < Re s` and a section `f ∈ sourceSpace ℝ (m+1) (n+1) σ s`
  of `I(s, σ)`.

Then `SatisfiesLocalCoefficientRelation` holds for the measure
`μ = realScaledMeasure √|a|`, which is `|a|^{1/2} dx`, and for the two scalars

- `(realLFactor Q).denominator (1 - s)`, which is `L(1-s, φ₂ ⊗ φ₁^∨)⁻¹`;
- `z^{m+1} · realEpsilon P a √|a| s · (realLFactor P).denominator s`, which is
  `z^{m+1} ε(s, φ₁ ⊗ φ₂^∨, ψ, μ) L(s, φ₁ ⊗ φ₂^∨)⁻¹`.

`ReciprocalEntire.denominator` is the entire function `1/L`. The Library's
`realEpsilon P a c hc s` is the `ε`-factor of `realModel P ⊗ |·|^s` for `ψ`
and the measure `c dx`. Unfolding `SatisfiesLocalCoefficientRelation` from
`Induction`, the conclusion says:

- the intertwining integral `A f` and the Jacquet integral `λ(f)` converge
  absolutely;
- the Jacquet integral `λ'(A f)` of `I(-s, σ̃)` has a continued value;
- `L(1-s, φ₂ ⊗ φ₁^∨)⁻¹ λ(f) = z^{m+1} ε(s, φ₁ ⊗ φ₂^∨, ψ, μ) L(s, φ₁ ⊗ φ₂^∨)⁻¹ λ'(A f)`.

All three integrals use the measure `μ` on every matrix entry. Where
`L(1-s, φ₂ ⊗ φ₁^∨)` is finite, the identity says
`λ(f) = z^{m+1} γ(s, φ₁ ⊗ φ₂^∨, ψ, μ) λ'(A f)` with
`γ(s, φ, ψ, μ) = ε(s, φ, ψ, μ) L(1-s, φ^∨)/L(s, φ)`. In other words, the
local coefficient (`IsLocalCoefficientAt`) is `z^{m+1} γ(s, φ₁ ⊗ φ₂^∨, ψ, μ)`.

### `ComplexLocalCoefficientGammaStatement`

The same statement over `ℂ`. Here `a : ℂˣ`, `ψ = complexScaledCharacter a`
with `ψ(w) = e^{2πi Tr(aw)}`, and `ds₁ ds₂ : List ComplexCharacterData`
present characters of the complex Weil group `ℂˣ` through `complexModel`.
The parameter hypothesis is `HasComplexPairParameter σ ds₁ ds₂`, and the
factors are `complexLFactor` and `complexEpsilon`. The measure is
`μ = complexScaledMeasure ‖a‖`, i.e. `|a|_ℂ^{1/2} · 2 dx dy` with
`|a|_ℂ = ‖a‖²`; it is self-dual for `ψ`.

### `LocalCoefficientGammaStatement`

The conjunction of the two statements, in the same universe of `E`.

## Instances, universes and scope

The file sets `set_option backward.isDefEq.respectTransparency false`, as
`GeneralLinear` and `Induction` do. This option affects elaboration only.
The space `E : Type uE` is universe-polymorphic. The conjunction names its
components as `RealLocalCoefficientGammaStatement.{uE}` and
`ComplexLocalCoefficientGammaStatement.{uE}`, so that both use the same
universe. `[CompleteSpace E]` is assumed, as by
`IsGenericBanachPairRepresentation` and `SatisfiesLocalCoefficientRelation`.

Scope:

- Only `GL_{m+1} × GL_{n+1}` inside `GL_{m+n+2}` is treated, with both ranks
  positive, because the Library's Whittaker character is defined at positive
  rank. Shahidi's theorems cover all quasi-split real groups, and over `ℂ`
  all complex groups.
- The statement does not assert that `P` and `Q` exist. They do exist
  (Derived choice 8), so the clause is not vacuous.
- `z` is a hypothesis. For irreducible admissible `σ`, the central element
  `(1, -1)` of the Levi subgroup acts by a scalar (Schur's lemma). Since
  `(1, -1)² = 1`, that scalar is `±1`. For `σ = σ₁ ⊠ σ₂` it is
  `ω_{σ₂}(-1)`, where `ω_{σ₂}` is the central character of `σ₂`.
- Normalized intertwining operators, Plancherel measures and Shahidi's
  §4 are not part of this module.

## Original source correspondence

F. Shahidi, *Local coefficients as Artin factors for real groups*, Duke
Math. J. 52 (1985), 973–1007 (literature id `shahidi-1985-real-artin`;
PDF page = printed page − 972):

- Printed p.977 (PDF 5): Whittaker functionals (1.1), the bound
  `dim V_χ^* ≤ 1` quoted from his reference [31], and Theorem 1.1.
- Printed p.978 (PDF 6), Proposition 1.2: the representatives used in the
  Jacquet functionals may be chosen arbitrarily.
- Printed p.979 (PDF 7): the rank-one representatives `w = [[0, -1], [1, 0]]`
  for `SL₂(F)`, and `ψ_ℂ = ψ_ℝ ∘ Tr_{ℂ/ℝ}`.
- Printed p.980 (PDF 8): Tate's measures, used before Lemma 1.4.
- Printed p.985 (PDF 13), (2.2): the Jacquet functional, with
  `w_θ = w_l w_{l,θ}` fixed as in Proposition 1.2.
- Printed p.988 (PDF 16), (3.1)–(3.3): the identification of `H(σ)_∞` with
  a subspace of a principal series through Proposition 2.2, the
  intertwining operator `A(ν, σ, w)`, the functional `κ(w(ν), w(σ))`
  obtained by analytic continuation, and the local coefficient
  `C_χ(ν, σ, θ, w)`, which exists by Theorem 1.1. Here (3.3) is asserted
  for `Re ν(H_α) ≫ 0`.
- Printed p.989 (PDF 17): (3.4), `C_χ(ν, σ, θ, w) = C_χ(ν₀ + ν, η₀, ∅, w)`,
  the reduction to principal series, computed through Proposition 3.2.1
  of Shahidi 1981 and Lemma 1.4. Also on this page: the Weil group `W_ℝ`,
  the parameter
  `φ : W_ℝ → ^L M`, the adjoint action `ρ` of `^L M` on `^L 𝔫_w̃`, the distinct
  values `a_i` of `2ρ_θ(α^∨)`, and `r_i = ρ · φ | V_i`. The representative `w`
  is the product of the rank-one representatives along a reduced
  decomposition. The character `χ` is fixed by `ψ_ℝ(x) = exp(2πix)` and
  `ψ_ℂ = ψ_ℝ ∘ Tr_{ℂ/ℝ}` on the simple root groups. (3.5) gives the `L`-factor
  of a character of `ℝˣ`.
- Printed p.990 (PDF 18), (3.6)–(3.13): `ε` of a character, `L` and `ε` of
  `Ind_{ℂˣ}^{W_ℝ} θ` with `λ(ℂ/ℝ, ψ_ℝ) = i`, additivity, and
  `γ(s, τ, ψ_ℝ) = ε(s, τ, ψ_ℝ) L(1-s, τ̃)/L(s, τ)`. These agree with the
  Library's `RealBlock` and `ComplexCharacterData` factors at `a = 1` and
  `c = 1`. Theorem 3.1: for an irreducible admissible `χ`-generic Banach
  representation `σ` of `M`, (3.1.1) reads
  `C_χ(-2sρ_θ, σ, θ, w) = λ(ℂ/ℝ, ψ_ℝ)^{2m+p} ∏ ε(a_i s, r_i, ψ_ℝ) L(1 - a_i s, r̃_i)/L(a_i s, r_i)`.
  Here `m` and `p` count the rank-one groups `G_α` whose simply connected
  coverings are `SU(2, 1)` and `SL(2, ℂ)`.
- Printed p.1002 (PDF 30): the end of the proof, through Vogan's
  Theorem 6.2(f) (`σ` is the full induced representation of a tempered one).
- Printed p.1003 (PDF 31), Theorem 3.13: for a complex group, `W_ℂ` and
  `ψ_ℂ`, (3.13.1) is
  `C_χ(-2sρ_θ, σ, θ, w) = ∏ ε(a_i s, r_i, ψ_ℂ) L(1 - a_i s, r̃_i)/L(a_i s, r_i)`,
  with no `λ` factor.

The integrals are those of `Induction`, with the integrands of F. Shahidi,
*Fourier transforms of intertwining operators and Plancherel measures for
GL(n)*, Amer. J. Math. 106 (1984), 67–111 (literature id
`shahidi-1984-fourier`). Its Theorem 5.1 (printed p.103) is the p-adic
analogue: for suitably normalized measures,
`C_χ(s, π₁ ⊗ π₂) = ω_{π₂}(-1)^{rank π₁} γ(s, π₁ × π̃₂, ψ)`.

F. Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981), 297–355
(literature id `shahidi-1981-certain-l`; PDF page = printed page − 295), is
reference [27] of the 1985 paper. Derived choice 3 uses (2.1.3) on printed
p.309 (PDF 14), the normalization of the measures on the factors of a
reduced decomposition; Theorem 2.1.1 on p.310 (PDF 15), the factorization
of the intertwining operator into rank-one operators; and
Proposition 3.2.1 on pp.336–337 (PDF 41–42), the factorization of the local
coefficient into rank-one coefficients.

J. Tate, *Number theoretic background* (1979), printed p.13 (literature id
`tate-1979-number-theoretic-background`; PDF page = printed page + 9):
(3.2.2)–(3.2.3) give the dependence of `ε` on the measure and on the
additive character. (3.2.4)–(3.2.5) use `dx` for `exp(2πix)` on `ℝ` and
`2 dx dy` for `exp(2πi Tr z)` on `ℂ`. These are the self-dual measures, as
in the Library's `HeckeGlobalFunctionalEquationStatement`.

G. Henniart, *A simple proof of the Langlands conjectures for GL(n) over a
p-adic field* (2000), §2.3, pp.444–445 (literature id
`henniart-2000-simple-proof`), compares local factors through global
functional equations for pairs. Their archimedean factors are the ones
compared here.

### Derived choices

These points explain the formalization. None is proved in Lean.

1. **Specialization to `GL`.** For `M = GL_{m+1} × GL_{n+1}` there is one
   value `a₁ = 2ρ_θ(α^∨) = m + n + 2`. `r₁` is the standard representation
   tensored with the dual standard representation, so `r₁ ∘ φ = φ₁ ⊗ φ₂^∨`
   and `r̃₁ ∘ φ = (φ₁ ⊗ φ₂^∨)^∨ ≅ φ₂ ⊗ φ₁^∨`. `GL_N(ℝ)` is split, so every
   rank-one group `G_α` has simply connected covering `SL(2, ℝ)`. Hence
   Shahidi's `m` and `p` are `0`, and Theorem 3.1 has no `λ` factor. Over
   `ℂ`, Theorem 3.13 uses the complex Weil group and `ψ_ℂ` directly.
2. **The variable `s` and the sign of `2sρ_θ`.** For the Levi blocks
   `(h₁, h₂)`, `e^{2ρ_θ(log a)} = |det h₁|^{n+1} |det h₂|^{-(m+1)}`. The twist
   `|det h₁|^{s/2} |det h₂|^{-s/2}` of `sourceCharacter` equals Shahidi's
   `e^{2s'ρ_θ}` with `s = (m+n+2) s'`, times the restriction of the character
   `|det g|^{(m-n)s/(2(m+n+2))}` of `GL_{m+n+2}`. Twisting `σ` by the
   restriction of a character of `GL_{m+n+2}` changes neither the local
   coefficient nor `φ₁ ⊗ φ₂^∨`. Then `a₁ s' = s`.

   Theorem 3.1 is printed with the argument `-2sρ_θ`. With the paper's own
   conventions ((1) on p.976, (3.1), (2.2) and (3.3)), the spherical vector
   `f₀` of `SL₂(ℝ)` gives `κ(ν) f₀ = 2π^{(ν+1)/2} K_{ν/2}(2π)/Γ((ν+1)/2)` and
   `A f₀ = √π Γ(ν/2)/Γ((ν+1)/2) f₀'`, where `f₀'` is the spherical vector of
   the target space. Hence
   `C(ν) = π^{ν-1/2} Γ((1-ν)/2)/Γ(ν/2) = γ(ν(H_α), 1, ψ_ℝ)`, as in Lemma 1.4.
   This holds in the region `Re ν(H_α) > 0`, where `A` converges. So the
   consistent reading is `C_χ(2sρ_θ, …) = ∏ γ(a_i s, r_i, ψ_ℝ)`.

   The printed minus sign comes from the convention of Shahidi's 1981
   `p`-adic paper. There `H_θ` is normalized by `ord`, so `-2sρ_θ` is a
   positive twist. The statement uses the consistent reading, and Derived
   choice 5 confirms it independently.
3. **Weyl representatives and the sign `z^{m+1}`.** Shahidi's local
   coefficient depends on the representatives in his Jacquet functionals
   (2.2). On p.985 these are `w_θ = w_l w_{l,θ}`, with `w_l` and `w_{l,θ}`
   fixed as in Proposition 1.2 (p.978), which allows any representatives.
   Only the representative `w` of the intertwining operator is pinned down
   (p.989). By `Induction.md`, Derived choices 3 and 7, that `w` is
   `w_{m+1,n+1}⁻¹ diag(I_{m+1}, (-1)^{m+1} I_{n+1})`, so his intertwining
   operator is `σ(I_{m+1}, (-1)^{m+1} I_{n+1}) = z^{m+1}` times the `A` of
   `Induction`. His Jacquet functionals carry further constants that depend
   on the representatives. So the sign cannot be read off Theorem 3.1.

   The sign `z^{m+1}` is derived instead in the Library's own conventions.
   The derivation follows the route of Shahidi's proof (Shahidi 1985, (3.4)
   on p.989; Shahidi 1981, Theorem 2.1.1 and Proposition 3.2.1), with
   Derived choice 5 as the rank-one input. Write `p = m+1`, `q = n+1`,
   `N = p+q`, `J_r` for the antidiagonal permutation matrix of size `r`,
   `w_{p,q}` for the Library's `blockWeyl` `[[0, I_p], [I_q, 0]]`, `U_r` for
   the upper unipotent subgroup of `GL_r` and `ψ_r(u) = ψ(∑_k u_{k,k+1})`.
   Every integral uses `μ` on each matrix entry. On a principal series
   `Ind_B(χ_1, …, χ_r)` of `GL_r` (normalized induction, functions `F` with
   `G` acting by right translation), the Borel Jacquet integral is
   `Λ_r(F) = ∫_{U_r} F(J_r u) ψ_r(u)⁻¹ du`. Outside its region of
   convergence it is continued analytically, as on p.988. It satisfies
   `Λ_r(R(u)F) = ψ_r(u) Λ_r(F)` for `u ∈ U_r`.

   1. *Principal-series embeddings.* Each factor `σᵢ` is realized in a
      Borel-induced representation: `σ₁ ⊂ Ind(χ_1, …, χ_p)` and
      `σ₂ ⊂ Ind(χ'_1, …, χ'_q)`. Over `ℝ` the standard modules of
      `StandardModule` are subspaces of the principal series of
      `principalSeriesCharacter`. A block `induced d`, with
      `ℓ = |d.weight|` and `t = d.exponent`, occupies two positions, with the
      characters `sgn^{ℓ+1}|·|^{t+ℓ/2}` and `|·|^{t-ℓ/2}`
      (`realInducedFirstCharacter`, `realInducedSecondCharacter`). A block
      `character d` occupies one position, with its own character. Over `ℂ`
      the standard modules are full principal series. The identification of
      the smooth vectors of `σ` with those of its standard module is the one
      Shahidi makes on p.988, through his Proposition 2.2. A vector `v` of
      `σ` is then a function `v(h₁, h₂)` on `GL_p × GL_q`, and `σ` acts by
      right translation.
   2. *The restricted functionals are nonzero.* Let `S = Ind_P(D)` be one
      factor, a standard module of `GL_r`: `P` is the standard parabolic
      subgroup whose Levi subgroup `M` has the blocks of sizes `r_i ∈ {1, 2}`,
      and `D = D_1 ⊠ ⋯ ⊠ D_k`, where `D_i` is a character for `r_i = 1` and,
      for `r_i = 2`, the subrepresentation of
      `Ind(sgn^{ℓ+1}|·|^{t+ℓ/2}, |·|^{t-ℓ/2})` cut out by the Fourier
      condition of `StandardModule`. Then `S ⊂ Ind_B(χ)` by induction in
      stages. Write `J_r = J_M w_M` with `J_M = diag(J_{r_1}, …, J_{r_k})`.
      The permutation matrix `w_M = J_M J_r` reverses the order of the blocks
      and keeps the order inside each block. So
      `U_r = (w_M⁻¹ U_M w_M) · U_{P'}`, where `P'` is the standard parabolic
      subgroup with the blocks in reversed order. By the entry bookkeeping of
      step 4, `Λ_r(F) = ∫_{U_{P'}} Λ_M(Φ(w_M u)) ψ_r(u)⁻¹ du`. Here
      `Φ(g) ∈ D` is the function `h ↦ F(h g)` on `M`, and
      `Λ_M = Λ_{r_1} ⊗ ⋯ ⊗ Λ_{r_k}`. Now `P w_M U_{P'}` is open, and
      `(p, u) ↦ p w_M u` is a diffeomorphism from `P × U_{P'}` onto it, because
      `w_M U_{P'} w_M⁻¹` is the opposite radical of `P`. So there are smooth
      sections with `Φ(p w_M u) = δ_P^{1/2}(p) φ(u) D(p) v` and support in
      this cell, for any `φ ∈ C_c^∞(U_{P'})` and any smooth `v ∈ D`. For them
      `Λ_r(F) = (∫ φ ψ_r⁻¹) Λ_M(v)`, which is nonzero when
      `φ = ψ_r · β` for a bump function `β ≥ 0` and `v = v_1 ⊗ ⋯ ⊗ v_k` with
      `Λ_{r_i}(v_i) ≠ 0` for all `i`. Such `v_i` exist:
      - for `r_i = 1`, `Λ_1` is evaluation at `1`;
      - for `r_i = 2` and `ℓ = 0`, `D_i` is the whole principal series. There
        `Λ_2 ≠ 0` by the same open-cell argument with `M` the diagonal torus;
      - for `r_i = 2` and `ℓ ≥ 1`, `D_i` is the discrete series, and the
        quotient `Q` of the principal series by `D_i` has dimension `ℓ`
        (`StandardModule.md`). If `Λ_2` vanished on `D_i`, it would factor
        through `Q`. On `Q` the element `u(x)` acts as `exp(xX)` with `X`
        nilpotent, since `X` is conjugate to `aX` for every `a > 0`. So
        `x ↦ Λ_2(u(x) v) = ψ(x) Λ_2(v)` would be a bounded polynomial, hence
        constant, which forces `Λ_2(v) = 0` for all `v`. That contradicts
        `Λ_2 ≠ 0` on the principal series.

      Over `ℂ` every `r_i` is `1`. So `Λ_p ⊗ Λ_q` restricts to a nonzero
      continuous `ψ`-Whittaker functional of `σ`.
   3. *One constant for `ℓ` and `ℓ'`.* `σ` is irreducible, so its continuous
      `ψ`-Whittaker functionals form a space of dimension at most one
      (p.977, Theorem 1.1 and Shahidi's reference [31]). By step 2,
      `ℓ = c · (Λ_p ⊗ Λ_q)` for one constant `c`:
      `ℓ(v) = c ∫_{U_p} ∫_{U_q} v(J_p u₁, J_q u₂) ψ_p(u₁)⁻¹ ψ_q(u₂)⁻¹ du₁ du₂`.
      The space of `exchange σ` is the same `E`, its smooth vectors are those
      of `σ`, and `ℓ' = ℓ` on them (Derived choice 7). So `ℓ'` is given by
      the same formula with the same `c`. This simultaneous normalization is
      essential. If `ℓ'` were `c'` times the same functional, the
      coefficient would be multiplied by `c/c'`.
   4. *Reduction to the Borel subgroup.* For `f ∈ I(s, σ)` put
      `F(g) = [f(g)](1, 1)`, so that `[f(g)](h₁, h₂) = F(diag(h₁, h₂) g)`.
      By induction in stages (`sourceCharacter` contains `δ_P^{1/2}`), `F`
      lies in the normalized principal series of `GL_N` with the characters
      `χ_i|·|^{s/2}` followed by `χ'_j|·|^{-s/2}`. For `f' ∈ I(-s, σ̃)` put
      `F'(g) = [f'(g)](1, 1)`;
      since the target Levi is `diag(h₂, h₁)`,
      `[f'(g)](h₁, h₂) = F'(diag(h₂, h₁) g)`. Then:
      - *Intertwining integral.* `A f(g) = ∫ f(w_{p,q} u'(a) g) da` gives
        `F_{Af} = M(w_{p,q}) F` with `M(w)F(g) = ∫_{U'} F(w u' g) du'`.
        Here `U' = {u'(a) = [[I_q, a], [0, I_p]]}` is the Library's
        `intertwiningUnipotent`.
      - *Source functional.*
        `λ(f) = ∫ ψ(a_{q,1})⁻¹ ℓ(f(w_{p,q} u'(a))) da`, since `a_{q,1}` is the
        `(q, q+1)` entry of `u'(a)`. Inserting `ℓ` gives the argument
        `diag(J_p u₁, J_q u₂) w_{p,q} u'(a)`. Now
        `diag(h₁, h₂) w_{p,q} = w_{p,q} diag(h₂, h₁)` and
        `diag(J_p, J_q) w_{p,q} = J_N`, so the argument is
        `J_N · diag(u₂, u₁) u'(a)`. The map
        `(u₂, u₁, a) ↦ diag(u₂, u₁) u'(a)` is a bijection onto `U_N`. Its
        entries are those of `u₂`, `u₁` and `u₂ a`, so it has Jacobian `1`
        for the entrywise measures. Since the last row of `u₂` is
        `(0, …, 0, 1)`,
        `ψ_N(diag(u₂, u₁) u'(a)) = ψ_q(u₂) ψ_p(u₁) ψ(a_{q,1})`. Hence
        `λ(f) = c Λ_N(F)`.
      - *Target functional.*
        `λ'(f') = ∫ ψ(a_{p,1})⁻¹ ℓ'(f'(w_{p,q}⁻¹ u(a))) da` with
        `u(a) = [[I_p, a], [0, I_q]]`. Here `w_{p,q}⁻¹ = w_{q,p}` and
        `diag(J_q, J_p) w_{q,p} = J_N`. The same computation, with the roles
        of `p` and `q` exchanged, gives `λ'(f') = c Λ_N(F')`.

      So `λ(f) = C λ'(A f)` says `Λ_N(F) = C Λ_N(M(w_{p,q}) F)`: the constant
      `c` cancels, and both sides use the same representative `J_N`. This is
      (3.4) of Shahidi 1985: the coefficient of `σ` is that of the principal
      series.
   5. *Multiplicativity.* Write the permutation of `w_{p,q}` as a reduced
      product of `pq` simple transpositions. Each step exchanges adjacent
      characters `χ_i` (on the left) and `χ'_j` (on the right), and each
      pair `(i, j)` occurs exactly once. Permutation matrices multiply
      exactly, so `M(w_{p,q})` is the composite of the rank-one integrals
      with no sign. The entrywise measures decompose as in Shahidi 1981,
      (2.1.3) on p.309 and Theorem 2.1.1 on p.310, because each
      factorization of the integration group permutes entries and has
      Jacobian `1`. Every intermediate functional is the same `Λ_N`,
      continued as on p.988 of Shahidi 1985. So the rank-one relations
      `Λ_N = c_k · Λ_N ∘ M(s_k)` telescope, and the coefficient is `∏ c_k`,
      as in Shahidi 1981, Proposition 3.2.1 on pp.336–337.
   6. *Rank one.* For the step `s_k`, write `J_N = s_k y` with
      `y = s_k J_N`. Then `y u_{α_{N-k}}(x) y⁻¹ = u_{α_k}(x)`: a simple root
      group element with the same entry `x`, so the character value is
      `ψ(x)`. Split `U_N` as `U_{α_{N-k}}` times the unipotent radical of the
      corresponding standard parabolic subgroup. This reduces `Λ_N` and
      `M(s_k)` to the `GL₂` integrals at the positions `k, k+1`, with the
      representative `[[0, 1], [1, 0]] = w_{1,1}` in all three integrals.
      The `GL₂` characters are `χ_i|·|^{s/2}` and `χ'_j|·|^{-s/2}`, both
      times a common `|·|^c` coming from `δ_B^{1/2}`, which changes nothing.
      By Derived choice 5, `c_k = χ'_j(-1) γ(s, χ_i χ'_j⁻¹, ψ, μ)`.
   7. *Product.* The coefficient is
      `(∏_j χ'_j(-1))^p ∏_{i,j} γ(s, χ_i χ'_j⁻¹, ψ, μ)`. Here `∏_j χ'_j(-1)`
      is the scalar by which `-1 ∈ GL_q` acts, i.e. `z`, and `p = m+1`. Over
      `ℂ`, `φ₁ ⊗ φ₂^∨` is the sum of the characters `χ_i χ'_j⁻¹`, so the
      product of the gamma factors is `γ(s, φ₁ ⊗ φ₂^∨, ψ, μ)`. Over `ℝ` the
      same holds by Derived choice 9.

   The derivation uses the Library's permutation-matrix integrands, Tate's
   local functional equation (Derived choice 5), the Gamma identities of
   Derived choice 9, and the analytic facts of Shahidi's proof: absolute
   convergence for `Re s` large, continuation of the Jacquet integrals,
   uniqueness of Whittaker functionals and Proposition 2.2. It never uses
   Shahidi's representatives. The result agrees with Shahidi 1984,
   Theorem 5.1, and with the Library's
   `Langlands.Shahidi.IsGeneralLocalCoefficientGammaComparison`
   (`ω(-1)^(m+1)` for the central character `ω` of the second factor), which
   use the same integrands. Since `z = ±1`, `z^{m+1} = z^{-(m+1)}`.
4. **Additive character and measures.** Shahidi fixes `ψ_ℝ(x) = e^{2πix}`,
   `ψ_ℂ = ψ_ℝ ∘ Tr` and Tate's measures, which are self-dual for them. The
   statement extends this to every `ψ_a`.

   Set `N₀ = (m+1)(n+1)`, the dimension of `φ₁ ⊗ φ₂^∨` and the number of
   matrix entries in each integral. The torus element
   `t = diag(a^{m+n+1}, …, a, 1)` lies in the Levi subgroup, and the standard
   characters satisfy `χ_a(u) = χ_1(t u t⁻¹)`. Changing
   variables by `t`, with the self-dual measure `μ_a` of `ψ_a` in all three
   integrals, gives
   `C_a(s) = det(φ₁ ⊗ φ₂^∨)(a) |a|_F^{N₀(s-1/2)} C_1(s)`. By the Library's
   epsilon formula, the same factor relates `ε(s, φ₁ ⊗ φ₂^∨, ψ_a, μ_a)` to
   `ε(s, φ₁ ⊗ φ₂^∨, ψ_1, μ_1)`: the factor is `c^{rank}` with
   `c = |a|_F^{1/2}`, times `det(a) |a|_F^{rank(s-1)}`.

   The measure cannot be arbitrary. Replacing `μ` by `cμ` multiplies each
   of `A`, `λ` and `λ'` by `c^{N₀}`. So the coefficient becomes `c^{-N₀} C`,
   while `ε` becomes `c^{N₀} ε`. The identity can therefore hold for only
   one scale, and this is the self-dual one. The scales are those of the
   Library's `HeckeGlobalFunctionalEquationStatement`: `√|a|` over `ℝ` and
   `‖a‖` over `ℂ`.
5. **Check for `m = n = 0`.** Take `σ = χ₁ ⊠ χ₂`, write `η = χ₁χ₂⁻¹`, and let
   `ψ` be any nontrivial character with self-dual measure `dx`. A section
   supported in the big cell, `f(b w u'(y)) = (character of b) φ(y)` with
   `φ ∈ C_c^∞(F)`, has `λ(f) = ∫ ψ(-x) φ(x) dx`. The Bruhat decomposition
   `[[1, y], [x, 1 + xy]] = [[-1/x, 1], [0, x]] w u'(y + 1/x)` gives
   `A f(w u(y)) = χ₁(-1) ∫ η(u) |u|^{s-1} φ(y + u) du`. Hence
   `λ'(A f) = χ₁(-1) (∫ η(u) |u|^{s-1} ψ(u) du) λ(f)`, where the middle
   integral, after continuation, is `γ(1-s, η⁻¹, ψ, dx)` by Tate's local
   functional equation. Since `γ(s, η) γ(1-s, η⁻¹) = η(-1)` for self-dual
   `dx`, `C = χ₂(-1) γ(s, χ₁χ₂⁻¹, ψ, dx)`. This is `z^{m+1} γ(s, φ₁ ⊗ φ₂^∨)`
   with `z = χ₂(-1)`. The computation is the same over `ℝ` and `ℂ`.
6. **Multiplied form and the half-plane.** Shahidi's identity is between
   meromorphic functions of `s`. The Library's relation evaluates the
   actual integrals at one `s`. `A f` and `λ(f)` converge absolutely for
   `Re s` large (p.985, Lemma 2.3; p.988, (3.1)). This region depends only
   on `σ` (and `a`), not on `ℓ`, `ℓ'`, `P`, `Q` or `f`, so `b` is chosen
   before them. For `ℓ = 0` the relation is trivial.

   Every section at a given `s` lies in a flat family (`Induction.md`,
   Derived choice 5). Along a flat family, multiplying Shahidi's identity by
   the entire function `L(1-s, φ₂ ⊗ φ₁^∨)⁻¹` gives an identity of
   holomorphic functions on `Re s > b`, hence an identity at every point.
   At a pole of `L(1-s, φ₂ ⊗ φ₁^∨)`, the left side vanishes, while `ε` and
   `L(s, φ₁ ⊗ φ₂^∨)⁻¹` are nonzero for `Re s` large; so the identity says
   that `λ'(A f) = 0`. A quotient form would not be defined there.
7. **The functional `ℓ'`.** Shahidi's `κ(w(ν), w(σ))` uses the same
   functional on `H(σ) = H(w(σ))`. `exchange σ` acts on the same space `E`
   with the factors swapped, so its smooth vectors are those of `σ`. The
   hypothesis that `ℓ'` agrees with `ℓ` on vectors smooth for both
   expresses this without a Lean proof that the two subspaces coincide.
8. **Existence of `P` and `Q`.** Over `W_ℝ`:
   - `χ ⊗ χ'` is a character;
   - `χ ⊗ Ind θ ≅ Ind(θ · (χ ∘ N))`;
   - `Ind θ₁ ⊗ Ind θ₂ ≅ Ind(θ₁θ₂) ⊕ Ind(θ₁ · (θ₂ ∘ conj))`;
   - `(Ind θ)^∨ ≅ Ind θ⁻¹`.

   So `φ₁ ⊗ φ₂^∨` and `φ₂ ⊗ φ₁^∨` are sums of characters and two-dimensional
   inductions, i.e. `realModel` of some block lists. The Library's
   `RealBlock` allows the reducible weight-zero induction. Over `ℂˣ`, a
   tensor product of characters is a character. The factors do not depend
   on the choice of `P` and `Q`: this is the Library's
   `RealFactorPresentationIndependenceStatement` and
   `ComplexFactorPresentationIndependenceStatement`, quoted here as an
   explanation and not assumed.
9. **Real gamma factors of the principal-series characters.** This
   completes step 7 of Derived choice 3 over `ℝ`. It proves
   `∏_{i,j} γ(s, χ_i χ'_j⁻¹, ψ, μ) = γ(s, φ₁ ⊗ φ₂^∨, ψ, μ)` for the
   characters `χ_i`, `χ'_j` of step 1 and all real block lists. Every
   identity below is an exact identity of meromorphic functions of `s`. It
   uses only `Γ(y + 1) = y Γ(y)` and the reflection formula
   `Γ(y) Γ(1 - y) = π/sin(πy)`.

   *The factors.* Put `Γ_ℝ(y) = π^{-y/2} Γ(y/2)` and
   `Γ_ℂ(y) = 2(2π)^{-y} Γ(y)`, the Library's `gammaReal` and
   `gammaComplex`. By Legendre's duplication formula,
   `Γ_ℂ(y) = Γ_ℝ(y) Γ_ℝ(y + 1)`. Take `ψ(x) = e^{2πix}` and `dx`. For
   `e ∈ {0, 1}` and `u ∈ ℂ`, the Library gives `L(s, sgn^e|·|^u) = Γ_ℝ(s + u + e)`
   and `ε = i^e`, so
   `γ(s, sgn^e|·|^u) = i^e Γ_ℝ(1 - s - u + e)/Γ_ℝ(s + u + e)`. For a block
   `Ind θ_{ℓ,t}` (`induced d` with `ℓ = |d.weight| ≥ 0` and
   `t = d.exponent`), it gives `L = Γ_ℂ(s + t + ℓ/2)` and `ε = i^{ℓ+1}`.
   The dual is `Ind θ_{ℓ,-t}`, so
   `γ(s, Ind θ_{ℓ,t}) = i^{ℓ+1} Γ_ℂ(1 - s - t + ℓ/2)/Γ_ℂ(s + t + ℓ/2)`.
   For general `ψ_a` with self-dual measures, both sides of each identity
   below change by the same factor. The Library's factor depends only on
   the determinant and the rank, and these agree: `det Ind θ_{ℓ,t}` is
   `sgn^{ℓ+1}|·|^{2t}`, the product of the two characters of item 1, and
   `det(φ₁ ⊗ φ₂^∨) = ∏_{i,j} χ_i χ'_j⁻¹`.

   Gamma factors multiply over direct sums, and the characters of step 1
   are listed block by block. So it suffices to compare one block of `σ₁`
   with one block of `σ₂`. For two characters `χ` and `χ'` there is nothing
   to prove, since `χ ⊗ χ'^∨ = χ χ'⁻¹`. The other cases follow.

   1. *One block.*
      `γ(s, Ind θ_{ℓ,t}) = γ(s, sgn^{ℓ+1}|·|^{t+ℓ/2}) γ(s, |·|^{t-ℓ/2})`. Put
      `x = s + t` and use `Γ_ℝ(y + 2k) = Γ_ℝ(y) ∏_{j<k} (y + 2j)/(2π)`.
      - `ℓ` odd: the first character has `e = 0`. With `k = (ℓ+1)/2`, the
        left side divided by the right side is
        `i^{ℓ+1} Γ_ℝ(2 - x + ℓ/2) Γ_ℝ(x - ℓ/2)/(Γ_ℝ(x + ℓ/2 + 1) Γ_ℝ(1 - x - ℓ/2))`,
        which equals `i^{2k} ∏_{j<k} (1 - x - ℓ/2 + 2j)/(x - ℓ/2 + 2j)`.
      - `ℓ` even: the first character has `e = 1`. With `k = ℓ/2`, the
        quotient is
        `i^{ℓ} Γ_ℝ(2 - x + ℓ/2) Γ_ℝ(x - ℓ/2)/(Γ_ℝ(x + ℓ/2) Γ_ℝ(2 - x - ℓ/2))`,
        which equals `i^{2k} ∏_{j<k} (2 - x - ℓ/2 + 2j)/(x - ℓ/2 + 2j)`.

      In both cases the numerator factor at `j` is minus the denominator
      factor at `k - 1 - j`, so the quotient is `i^{2k} (-1)^k = 1`. For
      `ℓ = 0` the product is empty. Then the identity reads
      `γ(s, Ind θ_{0,t}) = γ(s, sgn|·|^t) γ(s, |·|^t)`, and `L` and `ε`
      agree separately: `Γ_ℂ(s + t) = Γ_ℝ(s + t + 1) Γ_ℝ(s + t)` and
      `i = i^1 · i^0`. The reducible weight-zero block and the sum of its
      two characters have the same factors.
   2. *Changing two signs.* For `y = s + u`, the reflection formula gives
      `γ(s, sgn|·|^u)/γ(s, |·|^u) = i cot(πy/2)`. So changing the sign
      exponent `e` of one character multiplies its gamma factor by
      `r_e(y) = i cot(πy/2)` for `e = 0` and by `r_e(y) = -i tan(πy/2)` for
      `e = 1`. Let `u - u' = n` be an integer with `n + e + e'` odd, and change
      both `sgn^e|·|^u` and `sgn^{e'}|·|^{u'}`. Write `y' = y - n` for the
      second character. The product of their gamma factors is multiplied by
      `r_e(y) r_{e'}(y')`. Use `cot(π(y - n)/2) = -tan(πy/2)` and
      `tan(π(y - n)/2) = -cot(πy/2)` for `n` odd, and periodicity for `n`
      even:
      - `e = e' = 0`, `n` odd: `(i cot)(i · (-tan)) = 1`;
      - `e ≠ e'`, `n` even: `(i cot)(-i tan) = 1`;
      - `e = e' = 1`, `n` odd: `(-i tan)(-i · (-cot)) = 1`.

      So the product does not change.
   3. *Character and block.* Let `χ = sgn^e|·|^u` and let `σ₂` have the
      block `Ind θ_{ℓ₂,t₂}`. Then `χ ⊗ (Ind θ₂)^∨ = Ind θ_{ℓ₂, u-t₂}`,
      because `sgn ∘ N_{ℂ/ℝ} = 1`. The characters `χ χ'_j⁻¹` are
      `sgn^{e+ℓ₂+1}|·|^{u-t₂-ℓ₂/2}` and `sgn^e|·|^{u-t₂+ℓ₂/2}`. If `e + ℓ₂` is
      odd, they are the two characters of item 1 for `Ind θ_{ℓ₂, u-t₂}`.
      If `e + ℓ₂` is even, both signs differ from those, by a change as in
      item 2 with `n = ℓ₂`; here `e' ≡ e + ℓ₂ + 1`, so
      `n + e + e' ≡ 2ℓ₂ + 2e + 1` is odd. Similarly, a block
      `Ind θ_{ℓ₁,t₁}` of `σ₁` and a character `χ' = sgn^{e'}|·|^{u'}` of
      `σ₂` give the characters of item 1 for `Ind θ_{ℓ₁, t₁-u'}` when
      `e' = 0`, and differ from them by such a change when `e' = 1`. Item 1 at
      `ℓ = 0` covers weight-zero blocks.
   4. *Two blocks.* Let the blocks be `Ind θ_{ℓ₁,t₁}` and `Ind θ_{ℓ₂,t₂}`.
      Put `t = t₁ - t₂`, `w = s + t`, `d = |ℓ₁ - ℓ₂|` and
      `G = Γ_ℂ(1 - w + (ℓ₁+ℓ₂)/2)/Γ_ℂ(w + (ℓ₁+ℓ₂)/2)`. Group the four
      characters `χ_i χ'_j⁻¹` by `i`. The two characters of the block of
      `σ₁` have the exponents `t₁ ± ℓ₁/2`. Item 3 allows either sign, and
      its output depends only on the exponent. So the product is
      `Π₁ = γ(s, Ind θ_{ℓ₂, t+ℓ₁/2}) γ(s, Ind θ_{ℓ₂, t-ℓ₁/2})`, which is
      `i^{2ℓ₂+2} G · Γ_ℂ(1 - w + (ℓ₂-ℓ₁)/2)/Γ_ℂ(w + (ℓ₂-ℓ₁)/2)`. By Derived
      choice 8, `Ind θ₁ ⊗ (Ind θ₂)^∨` has the blocks `Ind θ_{d,t}` and
      `Ind θ_{ℓ₁+ℓ₂,t}`, so its gamma factor is
      `Π₂ = i^{d+ℓ₁+ℓ₂+2} G · Γ_ℂ(1 - w + d/2)/Γ_ℂ(w + d/2)`.
      - `ℓ₁ ≤ ℓ₂`: `d = ℓ₂ - ℓ₁` and `d + ℓ₁ + ℓ₂ = 2ℓ₂`, so `Π₁ = Π₂`
        term by term. This includes equal weights `ℓ₁ = ℓ₂`, where `d = 0`
        and the first output block `Ind θ_{0,t}` is the reducible
        weight-zero induction `|·|^t ⊕ sgn|·|^t`.
      - `ℓ₁ > ℓ₂`: `d = ℓ₁ - ℓ₂` and
        `Π₂/Π₁ = i^{2d} Γ_ℂ(1 - w + d/2) Γ_ℂ(w - d/2)/(Γ_ℂ(w + d/2) Γ_ℂ(1 - w - d/2))`.
        The powers of `2π` cancel, and by the reflection formula this is
        `i^{2d} sin(π(w + d/2))/sin(π(w - d/2)) = (-1)^d (-1)^d = 1`.
   5. *Other presentations.* `P` may be any block list presenting
      `φ₁ ⊗ φ₂^∨`, for instance with a weight-zero block split into its two
      characters, or with the sign of a weight changed. The irreducible
      representations of `W_ℝ` of dimension at most two are the characters
      and the `Ind θ` with nonzero weight, and `Ind θ ≅ Ind θ̄`. By
      semisimplicity and Jordan–Hölder, two block lists present isomorphic
      representations exactly when they agree up to order, the signs of the
      weights and the splitting of weight-zero blocks. The Library's factors
      are products over the list (`realLFactor_perm`, `realEpsilon_perm`),
      use `|d.weight|`, and are unchanged by the splitting (item 1 at
      `ℓ = 0`). So `L`, `ε` and `γ` do not depend on the presentation. In
      general this is the Library's `RealFactorPresentationIndependenceStatement`;
      the argument here covers the presentations that occur. The same holds
      for `Q`.

   So `∏_{i,j} γ(s, χ_i χ'_j⁻¹, ψ, μ) = γ(s, φ₁ ⊗ φ₂^∨, ψ, μ)` for all block
   lists. As an independent check, the identity was also evaluated
   numerically for random blocks of every shape. Changing the parity of the
   first character of a block breaks it, so the characters of
   `StandardModule` matter here.

## Relation to other Library units

- `Induction`: `sourceSpace`, `exchange` and
  `SatisfiesLocalCoefficientRelation`. `GeneralLinear`:
  `IsGenericBanachPairRepresentation`, `pairModel`, `pairUnipotent` and
  `pairCharacter`. `SmoothVectors`: `smoothVectors` and
  `IsWhittakerFunctional`. `StandardModule`: `HasRealPairParameter` and
  `HasComplexPairParameter`.
- `Langlands.LocalFactor.ArchimedeanPresentation`: `realModel`,
  `realLFactor`, `realEpsilon`, `complexModel`, `complexLFactor` and
  `complexEpsilon`. `Langlands.LocalFactor.ArchimedeanScaling`: the scaled
  characters and measures. `Langlands.Weil.Representation.{SumsTensor,Dual}`:
  `FiniteRepresentation.tensor` and `FiniteRepresentation.dual`.
- The `p`-adic analogue is
  `Langlands.Representation.Shahidi.GeneralLocalCoefficientGammaStatement`.
  It has the same integrands, the sign `ω(-1)^(m+1)` and the gamma factor of
  `(π₁, π̃₂)`. There, measures are asserted to exist. Here the self-dual
  measure is fixed in all three integrals, and the relation is stated in
  multiplied form on a right half-plane.
