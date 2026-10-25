# Generic Banach representations of real and complex general linear groups

Author: Worker 35. Definition contribution to task
`91266440-3276-48dc-ab77-8d1c1fa386e8`, revision 1.
This module specializes the generic vocabulary of
`Langlands.Representation.Archimedean.SmoothVectors` to `GL_n(F)` and to
the Levi subgroups `GL_n(F) × GL_m(F)`, for `F = ℝ` or `ℂ`. It defines
the compact and unipotent subgroups, the generic character, and the
predicate "irreducible admissible generic Banach representation" in the
sense of Shahidi 1985. On the pair Levi subgroup the predicate is stated
for representations of the full Levi subgroup, whereas Shahidi uses its
Langlands factor `M_θ°`; Derived choice 1 explains the correspondence.
Apart from the subgroup axioms, a membership criterion and an evaluation
formula, nothing is proved.

## Mathematical content

The namespace is `Langlands.Archimedean`; `F` is any `RCLike` field, so
`ℝ` or `ℂ`. The group is the Library's `Langlands.GeneralLinear n F`,
which is Mathlib's `Matrix.GeneralLinearGroup (Fin n) F`, the units of
the matrix algebra. Matrices carry Mathlib's `L^∞` operator norm
(`open scoped Matrix.Norms.Operator`), which makes them a real Banach
algebra; its topology is the usual entrywise one. Mathlib's manifold
structure on the units of a complete normed algebra then makes `GL_n(F)`
a real Lie group, with model the real normed space `M_n(F)`, which is
its real Lie algebra `𝔤𝔩_n(F)`.

- `matrixModel F n` is the model with corners `𝓘(ℝ, M_n(F))`. The two
  `example`s check that `GL_n(F)` and `GL_n(F) × GL_m(F)` are real Lie
  groups for `matrixModel` and `pairModel`.
- `unitaryCompact F n` is the subgroup of `g ∈ GL_n(F)` with
  `g* g = 1`, built from Mathlib's `Matrix.unitaryGroup`; it is `O(n)` for
  `F = ℝ` and `U(n)` for `F = ℂ`, the standard maximal compact subgroup.
  `mem_unitaryCompact_iff` states the membership criterion
  `g* g = 1`.
- `pairModel F n m` is the product model; `pairCompact F n m` is
  `K_n × K_m`, the product of the unitary subgroups.
- `pairUnipotent F n m` is `N_n × N_m`, the product of the Library's
  upper unipotent subgroups `upperUnipotent n F` (upper triangular with
  ones on the diagonal).
- `pairCharacter F ψ n m`, for a Library `UnitaryAdditiveCharacter F`
  `ψ` (continuous, unitary and nontrivial), is the character of
  `N_{n+1} × N_{m+1}` given by
  `(u, u') ↦ ψ(∑_{i<n} u_{i,i+1}) · ψ(∑_{j<m} u'_{j,j+1})`
  (`pairCharacter_apply`). It is the product of the Library's
  `Whittaker.standardCharacter ψ n` and `Whittaker.standardCharacter ψ m`.
- `IsGenericBanachRepresentation F ψ n σ`, for a representation
  `σ : GL_{n+1}(F) →* (E →L[ℂ] E)` on a complex Banach space `E`:
  `IsIrreducibleAdmissibleGeneric` for the model `matrixModel F (n+1)`,
  the compact subgroup `unitaryCompact F (n+1)`, the subgroup
  `upperUnipotent (n+1) F` and the standard character of `ψ`.
- `IsGenericBanachPairRepresentation F ψ n m σ`, for a representation
  `σ` of `GL_{n+1}(F) × GL_{m+1}(F)`: the same predicate for
  `pairModel`, `pairCompact`, `pairUnipotent` and `pairCharacter`.

Unwinding the generic module, `σ` satisfies these predicates when it is
jointly continuous, topologically irreducible, has finite-dimensional
`K`-intertwiner spaces from every continuous finite-dimensional
representation of `K`, and has a nonzero functional `λ` on its smooth
vectors, bounded by finitely many seminorms `‖dσ(X₁)⋯dσ(Xₖ)v‖`, with
`λ(σ(u)v) = χ(u)λ(v)` for `u` in the unipotent subgroup.

## Instances, universes and scope

The file sets `set_option backward.isDefEq.respectTransparency false`, as
the Library's `Langlands.Global.ArchimedeanGL` (Worker 2) does: the charts
on the units of `M_n(F)` are found only after unfolding the normed-ring
instances of the operator norm. This option affects elaboration only.

Ranks are written `n + 1` and `m + 1` because the Library's standard
character is defined on `upperUnipotent (n + 1) F`. The declarations are
universe-polymorphic in `F` and `E`.

The block-diagonal embedding of `GL_n × GL_m` into `GL_{n+m}`, the
parabolic induction from it and the local coefficient are not part of
this module.

## Original source correspondence

F. Shahidi, *Local coefficients as Artin factors for real groups*, Duke
Math. J. 52 (1985), 973–1007 (literature id `shahidi-1985-real-artin`;
PDF page = printed page − 972).

- Printed p.976 (PDF 4), §0: `G` is quasi-split over `ℝ` with Borel
  subgroup `B = TU`, maximal compact `K` "relative to `B`", Levi
  subgroups `M_θ` of standard parabolics `P_θ = M_θ N_θ`, and
  `P_θ = M_θ° A_θ N_θ`. For `GL_N(F)` (as a real group; `GL_N(ℂ)` is the
  restriction of scalars of `GL_N` from `ℂ` to `ℝ`), `U` is the upper
  unipotent group and `K` is `O(N)` or `U(N)`. For
  `M_θ = GL_n × GL_m` (block-diagonal), `M_θ ∩ U = N_n × N_m` and
  `M_θ ∩ K = K_n × K_m`, which are `pairUnipotent` and `pairCompact`.
- Printed p.977 (PDF 5), §1: a character of `U` is nondegenerate if it is
  `∏_{α ∈ Δ} χ_α` with every `χ_α` nontrivial on the simple root group
  `U_α`; relation (1.1) defines χ-Whittaker functionals. For `GL_N`, the
  simple roots are the superdiagonal entries, and the standard character
  `u ↦ ψ(∑ u_{i,i+1})` of a nontrivial `ψ` is nondegenerate.
- Printed p.973 (PDF 1), Introduction: `P = P_θ` is written `P = MAN`,
  "its Langlands decomposition", `σ` is "an irreducible admissible
  χ-generic Banach … representation of `M`", and the induced
  representation is `Ind_{P↑G} σ ⊗ e^ν` with `ν ∈ 𝔞*_ℂ`, the complex
  dual of the Lie algebra of `A`. Printed p.976 (PDF 4), §0: `A_θ` is
  the split component of the centre of `M_θ`, `P_θ = M_θ° A_θ N_θ` is
  the Langlands decomposition, and `I(ν, σ, θ) = Ind σ ⊗ e^ν` induces a
  representation `σ` of `M_θ°` together with `ν ∈ (𝔞_θ)*_ℂ`.
- Printed p.984 (PDF 12), §2: Shahidi fixes "an irreducible admissible
  χ-generic (more precisely `χ|M_θ ∩ U`-generic) Banach representation
  `(σ, H(σ))` of `M = M_θ°`". Printed p.988 (PDF 16), §3: `ν ∈ (𝔞_θ)*_ℂ`
  and "an irreducible admissible χ-generic Banach representation
  `(σ, H(σ))` of `M_θ° = M`". So in Shahidi `M` is the Langlands factor
  `M_θ°`, not the full Levi subgroup `M_θ`, and the character `e^ν` of
  `A_θ` is separate data.
- The restriction of the standard character of `GL_{n+m}` to
  block-diagonal `diag(u, u')` with `u ∈ N_n`, `u' ∈ N_m` is
  `ψ(∑ u_{i,i+1} + ∑ u'_{j,j+1})`, because the superdiagonal entry
  joining the two blocks is `0`; this is `pairCharacter`.
  `N_n × N_m = M_θ ∩ U` lies in `M_θ°`.
- Printed p.990 (PDF 18), Theorem 3.1: "Let `σ` be an irreducible
  admissible χ-generic Banach (in particular unitary χ-generic)
  representation of `M`", with `M = M_θ°` as fixed on p.988.
  `IsGenericBanachPairRepresentation` is not literally this hypothesis:
  it is a derived packaging on the full Levi subgroup
  `M_θ = GL_n(F) × GL_m(F)`, explained in Derived choice 1.

### Derived choices

These points are explanations of the formalization; none is proved in
Lean.

1. **Full Levi subgroup versus Shahidi's `M = M_θ°`.** Shahidi's
   hypothesis concerns a representation `σ₀` of `M = M_θ°` (pp.984, 988),
   with the spectral parameter `ν ∈ (𝔞_θ)*_ℂ` as separate data.
   `IsGenericBanachPairRepresentation` instead concerns a representation
   `σ` of the full Levi subgroup `M_θ = GL_n(F) × GL_m(F)`; this is a
   derived packaging of the pair `(σ₀, character of A_θ)`. For
   `GL_n × GL_m`, with `|·|` the usual absolute value of `F`,
   `M_θ° = {(g₁, g₂) : |det g₁| = |det g₂| = 1}` and
   `A_θ = {(a I_n, b I_m) : a, b > 0}`, which is central, and
   `M_θ = M_θ° × A_θ` is a direct product, the `A_θ`-component of
   `(g₁, g₂)` being `(|det g₁|^{1/n} I_n, |det g₂|^{1/m} I_m)`. Already for
   `GL_1(ℝ) × GL_1(ℝ)` the two groups differ: `M_θ° = {±1} × {±1}`.
   The two descriptions correspond as follows.
   - From the full Levi subgroup to Shahidi's data: if `σ` satisfies the
     predicate, then the central group `A_θ` acts on it by scalars
     (Schur's lemma for irreducible admissible representations,
     Harish-Chandra), through a continuous character `e^μ` for a unique
     `μ ∈ (𝔞_θ)*_ℂ`, and `σ = σ₀ ⊗ e^μ` with `σ₀ = σ|M_θ°`. The
     restriction `σ₀` satisfies Shahidi's hypothesis on `M_θ°`: the space
     and the closed invariant subspaces are the same, because `A_θ` acts
     by scalars; the compact subgroup `K_n × K_m` and the unipotent
     subgroup `N_n × N_m` lie in `M_θ°`, so the `K`-intertwiners and the
     Whittaker functionals are the same; the orbit map of `σ` is
     `(m, a) ↦ e^{μ(log a)} σ₀(m) v`, so the smooth vectors are the same,
     and derivatives along `𝔞_θ` only multiply by the scalars `μ(H)`, so
     the seminorm conditions agree.
   - Conversely, from `σ₀` satisfying Shahidi's hypothesis and any
     `μ ∈ (𝔞_θ)*_ℂ`, the representation
     `σ₀ ⊗ e^μ : (m, a) ↦ e^{μ(log a)} σ₀(m)` of `M_θ` satisfies the
     predicate, by the same comparisons.
   The character of `A_θ` is therefore kept inside `σ`, not discarded.
   Shahidi's `I(ν, σ₀, θ) = Ind σ₀ ⊗ e^ν` is the induction of the
   full-Levi representation `σ₀ ⊗ e^ν`. When the later induction unit
   twists `σ` by an additional spectral variable `s`, through a character
   of `M_θ` that is trivial on `M_θ°` (a product of powers of `|det g₁|`
   and `|det g₂|`, that is `e^{sϖ}` for some `ϖ ∈ (𝔞_θ)*`), the result is
   Shahidi's `I(μ + sϖ, σ₀, θ)`: the `A_θ`-character `μ` of `σ` is the base
   point of Shahidi's parameter and `s` moves it along the line through
   `μ` in the direction `ϖ`. Taking `σ` with trivial `A_θ`-character
   recovers `ν = sϖ`.
2. **The character.** Every nondegenerate unitary character of `U` is
   conjugate, by an element of the diagonal torus, to the standard
   character of a fixed nontrivial `ψ`: every unitary character of `F`
   (as a real vector group) is `x ↦ ψ(a x)` for a unique `a ∈ F`, and
   conjugation by
   `diag(t₁, …, t_N)` multiplies `u_{i,i+1}` by `t_i / t_{i+1}`. Since
   `σ(t)` transports Whittaker functionals between conjugate characters,
   genericity does not depend on the choice, and the standard character
   of an arbitrary `ψ` loses no generality. Shahidi fixes
   `ψ_ℝ(x) = exp(2πix)` only for the explicit formulas of §§1 and 3.
3. **Compact subgroup.** The unitary group is the standard maximal
   compact subgroup, and `K_M = K ∩ M = K_n × K_m`. Admissibility does not
   depend on the choice of maximal compact subgroup because all are
   conjugate.
4. The equivalences of the generic module (strong versus joint
   continuity, the seminorm description of Shahidi's Schwartz topology,
   finite multiplicities of irreducible `K`-types) are explained in
   `Langlands/Representation/Archimedean/SmoothVectors.md`.

## Relation to other Library units

`upperUnipotent` (from `Langlands.Group.GL.UpperUnipotent`) and
`Whittaker.standardCharacter` (from
`Langlands.Representation.Whittaker.GeneralLinear`) are the Library's
field-general objects, reused without change; they are also the objects
of the Library's nonarchimedean Whittaker and Shahidi modules. The
Library's archimedean Weil-group side (`Langlands.LocalFactor`
archimedean modules) supplies the gamma factors that Shahidi's
Theorem 3.1 compares with local coefficients; that comparison is planned
as a later statement.
