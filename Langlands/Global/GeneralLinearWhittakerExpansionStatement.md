# The Whittaker expansion of cusp forms on `GL_{r+1}`

Module `Langlands.Global.GeneralLinearWhittakerExpansionStatement` states
`Langlands.Global.WhittakerExpansionStatement` as a proposition definition.
It supplies no proof. The Whittaker function, the generic characters, the
coset space `N_r(F) \ GL_r(F)` and the points `diag(γ, 1)` are defined in
`Langlands.Global.GeneralLinearGlobalWhittaker` (see its Markdown). The two
local instances supply `IsAffine` and `Smooth` for the general linear group
scheme, as in that module.

## Sources

- J. Getz and H. Hahn, *An introduction to automorphic representations*
  (2024), registered as `getz-hahn-2024-automorphic-representations`
  (PDF page = printed page + 11 in Chapter 11):
  - Theorem 11.3.6, p.298 (PDF page 309): "Let `φ ∈ L²_cusp([GL_n])` be a
    smooth vector in the space of a cuspidal automorphic representation `π`
    of `A_{GL_n} \ GL_n(𝔸_F)`. If `ψ : N_n(𝔸_F) → ℂ^×` is a generic character
    then one has that `φ(g) = ∑_{γ ∈ N_{n-1}(F) \ GL_{n-1}(F)} W_ψ^φ((γ 1) g)`
    (11.8) for a unique choice of invariant measure on `[N_n]`. The sum
    converges absolutely and uniformly on compact subsets of `[G]`."
  - (11.6), p.297 (PDF page 308): `W_ψ^φ(g) = ∫_{[N]} φ(ng) conj(ψ(n)) dn`.
    Example 11.1, pp.294–295 (PDF pages 305–306): the generic characters of
    `N_n(𝔸)` trivial on `N_n(F)`.
  - pp.298–299 (PDF pages 309–310): the proof for `n = 2` by Fourier
    expansion on `F \ 𝔸`, (11.9)–(11.11). For `n ≥ 3` the book refers to
    Cogdell, §1.1.
- J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in: An
  Introduction to the Langlands Program (2004), registered as
  `cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3), §1:
  - p.198 (PDF page 201): automorphic forms are "smooth (of uniform moderate
    growth)", not necessarily `K_∞`-finite. `V_π` is the space of smooth
    vectors of an irreducible unitary cuspidal automorphic representation. A
    cuspidal function is a smooth function `φ` on `GL_n(k) \ GL_n(𝔸)` with
    `∫_{U(k) \ U(𝔸)} φ(ug) du = 0` for every unipotent radical `U` of a
    standard parabolic subgroup.
  - p.199 (PDF page 202): `ψ` and `W_φ`.
  - Theorem 1.1, p.200 (PDF page 203): for a cusp form `φ ∈ V_π`,
    `φ(g) = ∑_{γ ∈ N_{n-1}(k) \ GL_{n-1}(k)} W_φ((γ 1) g)`, "with convergence
    absolute and uniform on compact subsets". The proof sketch on the same
    page proves, by induction on `n`, the analogous expansion for every
    cuspidal function on the mirabolic subgroup `P_n(𝔸)`. It then applies
    this to `p ↦ φ(pg)`, with uniformity for `g` in a compact subset `Ω` of
    `GL_n(𝔸)`.
- J. A. Shalika, *The multiplicity one theorem for GL_n*, Ann. of Math. 100
  (1974), registered as `shalika-1974-multiplicity-one` (PDF page = printed
  page − 169), §5, Theorem 5.9, p.188 (PDF page 19): the same expansion at
  `x = e` for every smooth function `f` on `GL_n(𝔸)` that is left invariant
  under the rational mirabolic subgroup and satisfies (5.4) for the standard
  parabolic subgroups. The proof is omitted there.

## Statement

The data, for a number field `F : Type u` and `r : ℕ`, with `G = GL_{r+1}`
the actual general linear group scheme over `Spec F`:

- a closed matrix embedding `rho : MatrixRepresentation G (Fin N)`
  (`IsClosedSubgroup rho`), `hsmooth : SmoothOfRelativeDimension d G.X.hom`
  and `hcalc : AdelicDifferentialCommutator F G hsmooth`. These are the data
  of the uniform growth predicate. `hcalc` is a proposition that the Library
  proves (`adelicDifferentialCommutator_of_smooth`), and `GL_{r+1}` is smooth
  of relative dimension `(r + 1)²`, so neither restricts the statement;
- `ψ : AddChar (Adeles F) ℂ`, continuous, with `ψ(x) = 1` for `x ∈ F`, and
  `ψ ≠ 1`;
- `m : Fin r → F` with every `m i ≠ 0`;
- `φ : FinitePlotSmoothRationalFunctions F G` with
  `HasAdelicUniformModerateGrowth F G rho hsmooth hcalc φ`;
- `φ` cuspidal: `φ.val ∈ generalLinearStandardBlockVanishingSubrepresentation F (r + 1)`.
  The `haveI` supplies the published `compactSpace_adeleQuotient`, which this
  subrepresentation requires.

Write `term q g = W(diag(γ_q, 1) g)`, where `W` is
`generalLinearWhittakerFunction F r ψ m` applied to the function
`evaluate F G φ.val` and `γ_q = q.out` represents the class
`q ∈ N_r(F) \ GL_r(F)`. The conclusion has two parts:

1. for every `g ∈ G(𝔸)`, `q ↦ ‖term q g‖` is summable and `q ↦ term q g` has
   sum `φ(g)`;
2. for every compact `C ⊆ G(𝔸)`, the finite partial sums
   `∑_{q ∈ s} ‖term q g‖` converge to `∑' q, ‖term q g‖` uniformly for
   `g ∈ C`, along the directed set of finite sets `s`.

## Correspondence with the sources

- The group. `n = r + 1`. The case `r = 0` is included and is trivial:
  `N_1` is trivial, `N_0(F) \ GL_0(F)` has one point, `W = φ`, and `GL_1` has
  no proper standard parabolic, so every `φ` is cuspidal.
- The functions. `FinitePlotSmoothRationalFunctions F G` consists of the
  continuous functions on `G(𝔸)` that are left invariant under `G(F)`. Each
  is smooth in the archimedean variable (plot-smooth on every archimedean
  slice) and right invariant under a common open subgroup of `G(𝔸_f)`.
  `HasAdelicUniformModerateGrowth` (module
  `Langlands.Automorphic.GroupSchemeAdelicUniformGrowth`) says that there is one exponent `R` such that every element of the
  enveloping algebra of the archimedean Lie algebra sends `φ` to a function
  bounded by `C ‖g‖^R`, where `‖·‖` is the adelic norm of `rho`. This is
  uniform moderate growth. `generalLinearStandardBlockVanishingSubrepresentation`
  asks for vanishing constant terms along the unipotent radicals of the
  standard maximal parabolics (block sizes `a + b = r + 1`, `a, b > 0`). By
  `mem_generalLinearStandardBlockVanishingSubrepresentation_iff` this is the
  Library's original `IsCuspidal`. It implies vanishing along the unipotent
  radical of every standard parabolic (integrate in stages: `U_P ⊇ U_Q` when
  `P ⊆ Q`). So it is Cogdell's and Shalika's cuspidality.
- Which `φ` are covered. Cogdell's cusp forms, the elements of `V_π`, are
  smooth vectors. They are fixed by an open compact subgroup of `GL_n(𝔸_f)`,
  smooth in the archimedean variable, of uniform moderate growth (his
  convention on p.198) and cuspidal, so they lie in the class above. Getz–Hahn
  state the theorem for the smooth vectors of a cuspidal `π ⊆ L²_cusp([GL_n])`,
  `[G] = A_G G(F) \ G(𝔸)`, and refer to Cogdell for the proof. A function on
  `[G]` is a function on `G(F) \ G(𝔸)` invariant under `A_G`. The class
  does not depend on the closed embedding `rho`. This is the published
  `ClosedImmersionAdelicGrowthIndependenceStatement`, proved as
  `closedImmersionAdelicGrowthIndependence`.
- Generalization. The statement covers every smooth cuspidal function of
  uniform moderate growth. It requires no irreducible representation, no
  square integrability and no central character. Cogdell's proof does not use
  irreducibility or unitarity: it restricts `φ` to the mirabolic subgroup and
  proves the expansion there for arbitrary cuspidal functions. Shalika's
  Theorem 5.9 is likewise stated for all smooth cuspidal functions. The
  uniform moderate growth hypothesis, Cogdell's standing convention for
  automorphic forms, is kept. This explanation is not proved here.
- The character. Getz–Hahn's generic characters of `N_n(𝔸)` trivial on
  `N_n(F)` are, by Example 11.1, exactly the characters
  `ψ(m_1 x_{12} + ⋯ + m_{n-1} x_{(n-1)n})` with `ψ` a nontrivial character of
  `F \ 𝔸` and all `m_i ∈ F^×`. The hypotheses on `ψ` and `m` say precisely
  this. A continuous character of the compact group `F \ 𝔸` is unitary, so
  `conj ψ = ψ⁻¹` and the integrand agrees with Cogdell's. Cogdell uses the
  standard character, `m_i = 1`. The expansion for general `m` reduces to it.
  Let `t = diag(t_0, …, t_{r-1}, 1)` be rational with `t_i / t_{i+1} = m_i`.
  Then `W_{ψ,m}(g) = W_{ψ,1}(tg)`, by the substitution `n ↦ tnt⁻¹` on
  `N(F) \ N(𝔸)` (it preserves the measure of total mass one) and left
  invariance under `t`. Moreover `γ ↦ t'γ`, with `t'` the upper-left block
  of `t`, permutes `N_r(F) \ GL_r(F)`.
- The measure. Getz–Hahn's `W` depends on the measure on `[N_n]` up to a
  positive scalar. Theorem 11.3.6 holds "for a unique choice". That choice is
  total mass one: their proof for `n = 2` is Fourier inversion on the compact
  group `F \ 𝔸`, with characters indexed by `F` and counted once. That
  requires the Haar probability measure. Cogdell's proof uses the same
  normalization on all the compact quotients. Here the measure is
  `normalizedRationalQuotientHaarMeasure`. It has total mass one because
  `N_{r+1}(F) \ N_{r+1}(𝔸)` is compact (`N_{r+1}` is a smooth connected
  unipotent group, compare the Library's
  `compactSpace_rationalQuotient_range_unipotent`). This module does not use
  compactness as a hypothesis and does not prove it.
- The index set and the terms. The sum runs over the right cosets
  `N_r(F)γ`, read at the representative `q.out`. For `ν ∈ N_r(F)`,
  `diag(ν, 1) ∈ N_{r+1}(F)`. Also `W(uh) = ψ_N(u)W(h)` for `u ∈ N_{r+1}(𝔸)`,
  because right translation preserves the quotient measure, and `ψ_N` is
  trivial on `N_{r+1}(F)`. So the terms do not depend on the representative.
- The convergence. Part 1 is absolute convergence, as an unconditional sum
  over the countable set `N_r(F) \ GL_r(F)`. Part 2 is "uniform on compact
  subsets": the tails `∑_{q ∉ s} ‖term q g‖` tend to `0` uniformly on `C`.
  Together with part 1, it makes the partial sums of the terms converge to
  `φ` uniformly on `C`. The individual terms are not left `G(F)`-invariant,
  so the compact sets are taken in `G(𝔸)`, as in Cogdell's proof
  (`g ∈ Ω`). Every compact subset of `[G]` is the image of a compact subset
  of `G(𝔸)`.

## Scope

The statement has no proof. It does not state the consequences that
Getz–Hahn draw on p.298, namely that every cuspidal automorphic
representation of `GL_n` is generic. It also does not state the mirabolic
version used in Cogdell's induction, or properties of `W` such as continuity
or the transformation law under `N_{r+1}(𝔸)`. Multiplicity one (Getz–Hahn
Theorem 11.4.3, Shalika Theorem 5.5) is a separate statement.
