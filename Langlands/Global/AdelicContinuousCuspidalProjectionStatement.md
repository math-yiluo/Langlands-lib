# Continuous cuspidal projections on parabolic quotients

Module `Langlands.Global.AdelicContinuousCuspidalProjectionStatement` states the proposition
`Langlands.Global.ContinuousCuspidalProjectionExistenceStatement` (universe `u`) and proves
nothing.

## Statement

The data and hypotheses are those of `CuspidalProjectionExistenceStatement` (module
`Langlands.Global.AdelicCuspidalProjectionExistenceStatement`). Let `F` be a number field and `G`
an affine group scheme over `Spec F`, locally of finite type, with a compatible standard parabolic
family `fam : StandardParabolicFamily F G` (module `Langlands.Global.AdelicLeadingCuspidalComponents`).
Let `K` be a subgroup of `G(𝔸)` such that

- `K` is a maximal compact subgroup (`IsMaximalCompactSubgroup F G K`);
- `P₀(𝔸) K = G(𝔸)` for the minimal standard parabolic `P₀ = P_∅`
  (`IsIwasawaCompact (fam.p ⟨∅, _⟩) K`);
- for every standard index `J`, the inverse image of `K` in `M_J(𝔸)` is a maximal compact
  subgroup of `M_J(𝔸)`.

Let `rho : G → GL_N` be a closed matrix embedding (`IsClosedSubgroup rho`), `hsmooth` a smooth
structure of relative dimension `d`, and `Kinf = K ∩ G(F_∞)` (`K.comap (ofInfinite F G)`). Then
for every standard index `Q` and every `φ : G(𝔸) → ℂ` with
`fam.IsAutomorphicOn hsmooth Kinf rho Q φ`, there is `ψ : G(𝔸) → ℂ` such that

- `fam.IsModerateContinuousOnParabolic rho Q ψ` (module `Langlands.Global.AdelicCuspidalAnnihilator`):
  `ψ` is left invariant under `U_Q(𝔸) M_Q(F)` (`parabolicQuotientSubgroup`), continuous, and of
  moderate growth for the source norm of `rho` (`HasModerateGrowthFunction`);
- `fam.IsCuspidalAlong Q ψ`: the constant terms of `ψ` along all standard `Q' < Q` vanish;
- for every cusp form `t` on `M_Q(F) \ M_Q(𝔸)` (`fam.IsLeviCuspForm Kinf rho Q t`) and every
  `g ∈ G(𝔸)`, the functions `m ↦ φ(mg) \overline{t(m)}` and `m ↦ ψ(mg) \overline{t(m)}`
  (`fam.leviPairingIntegrand`) are integrable on `M_Q(F) \ M_Q(𝔸)^1` for
  `normOneRationalQuotientHaarMeasure`, and their integrals (`fam.leviPairing`) are equal.

## Correspondence and scope

The conclusion is that of `CuspidalProjectionExistenceStatement`, the relation
`fam.IsCuspidalProjection hsmooth Kinf rho Q φ ψ`, with the automorphy of `ψ`
(`fam.IsAutomorphicOn`: smoothness, finite level, `Kinf`-finiteness, `𝔷`-finiteness and moderate
growth) replaced by continuity and moderate growth. An automorphic function is continuous and of
moderate growth, so `CuspidalProjectionExistenceStatement` implies this proposition. The module
`Langlands.Global.AdelicCuspidalProjectionExistenceReductionStatement` states the converse
implication, with three further premises: the weighted majorants of Levi cusp forms, the
parabolic cuspidal vanishing criterion and Harish-Chandra's reproducing kernel on parabolic
quotients.

The pairing integrals are required to converge absolutely for the input `φ` and for `ψ`, for every
test cusp form and every `g`, as in `IsCuspidalProjection`.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), §6.2, p. 202: the cuspidal projection `φ ↦ φ^{cusp}` from `𝒜_P` to
  `𝒜_P^{cusp}` and its characterization (6.8):
  `(φ(·g), ψ)_{X^1_M} = (φ^{cusp}(·g), ψ)_{X^1_M}` for every cusp form `ψ` on `M(F)\M(𝔸)` and
  every `g ∈ G(𝔸)`, with the pairing on the norm-one quotient `M(F)\M(𝔸)^1`.
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  I.2.18, pp. 39–40, and I.3.5, pp. 47–48: the construction of the cuspidal form `φ_{cusp}` in a
  fixed central character eigenspace, by finite dimension and duality of the spaces of cusp forms
  of fixed `𝔷`-eigencharacter and `K`-type, and its application to the fixed-character summands
  of an automorphic form.

Both sources produce an automorphic cuspidal projection, so the proposition is a derived
weakening of their existence assertion. It keeps the invariance, cuspidality and fibrewise
pairings of (6.8), and of the regularity of the projection only continuity and moderate growth,
the hypotheses of the parabolic cuspidal vanishing criterion `ParabolicCuspidalVanishingStatement`.
