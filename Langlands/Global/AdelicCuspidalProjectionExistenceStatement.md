# Existence of cuspidal projections on parabolic quotients

Module `Langlands.Global.AdelicCuspidalProjectionExistenceStatement` states the proposition
`Langlands.Global.CuspidalProjectionExistenceStatement` (universe `u`) and proves nothing.

## Statement

Let `F` be a number field and `G` an affine group scheme over `Spec F`, locally of finite type,
with a compatible standard parabolic family `fam : StandardParabolicFamily F G` (module
`Langlands.Global.AdelicLeadingCuspidalComponents`). Let `K` be a subgroup of `G(𝔸)` such that

- `K` is a maximal compact subgroup (`IsMaximalCompactSubgroup F G K`);
- `P₀(𝔸) K = G(𝔸)` for the minimal standard parabolic `P₀ = P_∅`
  (`IsIwasawaCompact (fam.p ⟨∅, _⟩) K`);
- for every standard index `J`, the inverse image of `K` in `M_J(𝔸)` is a maximal compact
  subgroup of `M_J(𝔸)`.

Let `rho : G → GL_N` be a closed matrix embedding (`IsClosedSubgroup rho`), `hsmooth` a smooth
structure of relative dimension `d`, and `Kinf = K ∩ G(F_∞)` (`K.comap (ofInfinite F G)`). Then
for every standard index `Q` and every `φ : G(𝔸) → ℂ` with
`fam.IsAutomorphicOn hsmooth Kinf rho Q φ`, there is `ψ : G(𝔸) → ℂ` with
`fam.IsCuspidalProjection hsmooth Kinf rho Q φ ψ`.

The relation `IsCuspidalProjection` (module `AdelicLeadingCuspidalComponents`) requires:

- `ψ` is automorphic on `U_Q(𝔸) M_Q(F) \ G(𝔸)` for `Kinf` and `rho`;
- `ψ` is cuspidal along `Q`: its constant terms along all standard `Q' < Q` vanish;
- for every cusp form `t` on `M_Q(F) \ M_Q(𝔸)` (`IsLeviCuspForm`: automorphic on
  `M_Q(F) \ M_Q(𝔸)` for `Kinf ∩ M_Q(F_∞)` and the restriction of `rho`, with vanishing constant
  terms along every proper parabolic subgroup of `M_Q`) and every `g ∈ G(𝔸)`, the functions
  `m ↦ φ(mg) \overline{t(m)}` and `m ↦ ψ(mg) \overline{t(m)}` are integrable on
  `M_Q(F) \ M_Q(𝔸)^1` for its Haar measure `normOneRationalQuotientHaarMeasure`, and
  \[
    (\varphi(\cdot g), t)_{X^1_{M_Q}} = (\psi(\cdot g), t)_{X^1_{M_Q}} .
  \]

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), §6.2, p. 202: the linear projection `φ ↦ φ^{cusp}` from `𝒜_P` to
  `𝒜_P^{cusp}`, with reference to Mœglin–Waldspurger I.3.5, characterized by the pairings on
  `X_P` against `(f ∘ H_P)ψ'`, `f ∈ C_c^∞(𝔞_P)`, `ψ' ∈ 𝒜_P^{cusp}`, and equivalently by (6.8):
  `(φ(·g), ψ)_{X^1_M} = (φ^{cusp}(·g), ψ)_{X^1_M}` for every cusp form `ψ` on `M(F)\M(𝔸)` and
  every `g ∈ G(𝔸)`.
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  I.2.18, pp. 39–40: the construction in a fixed central character eigenspace. For a character
  `ξ` of `Z_M` and an automorphic form `φ ∈ 𝒜(U(𝔸)M(k)\G)_ξ`, there is a unique cuspidal
  `φ_{cusp} ∈ 𝒜₀(U(𝔸)M(k)\G)_ξ` with `(φ₀, φ_{cusp}) = (φ₀, φ)` for every cuspidal test
  form `φ₀ ∈ 𝒜₀(U(𝔸)M(k)\G)_{ξ*}`, `ξ* = \overline{ξ}^{-1}`. The pairing is the integral over
  `Z_M U(𝔸)M(k)\G` defined there, which the central character condition on the test form makes
  well defined. The projection is obtained from the finite dimension and duality of the spaces
  of cusp forms of a fixed `𝔷`-eigencharacter and `K`-type. I.3.2–I.3.3, pp. 41–45, give the
  decomposition of automorphic forms by the characters of `Z_M`, and I.3.5, pp. 47–48, the
  cuspidal component along `P` and the cuspidal form representing it, obtained by applying
  this projection to the fixed-character summands.

The proposition does not fix a central character. It uses the fibrewise formulation (6.8) of
Bernstein–Lapid: the test forms range over all cusp forms on `M(F)\M(𝔸)`, and the pairing is
taken on the norm-one quotient `M(F)\M(𝔸)^1`, at every `g ∈ G(𝔸)`.

## Correspondence and scope

The proposition is the existence half of the cuspidal projection of Bernstein–Lapid §6.2 in
the fibrewise form (6.8), for the Library's automorphy predicate. The pairing integrals are
required to converge absolutely for every test cusp form and every `g`; Bernstein–Lapid
assert this for automorphic forms because cusp forms on `M(F)\M(𝔸)^1` decay rapidly and `φ` has
moderate growth (Mœglin–Waldspurger I.2.12 and I.2.18). The compact `K` is in the position
used by both sources (Mœglin–Waldspurger I.1.4), expressed by the Iwasawa and Levi hypotheses.

Uniqueness of the projection is not part of this proposition. The Library's
`ParabolicCuspidalVanishingStatement` (module `AdelicCuspidalAnnihilator`) is a vanishing
criterion from which uniqueness follows for a positive-size embedding; the module
`AdelicCuspidalProjectionDecompositionReductionStatement` combines the two.
