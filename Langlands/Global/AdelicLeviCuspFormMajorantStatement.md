# Weighted majorants of cusp forms on standard Levi subgroups

Module `Langlands.Global.AdelicLeviCuspFormMajorantStatement` states the
proposition `Langlands.Global.LeviCuspFormPairingMajorantStatement` and proves
nothing.

## Statement

Let `F` be a number field and `G` a group scheme over `Spec F` with
`IsAffineHom G.X.hom`, `IsAffine G.X.left` and `LocallyOfFiniteType G.X.hom`.
Let `𝓕 : StandardParabolicFamily F G` be a standard parabolic family (a maximal
split torus, a generic cocharacter, and the standard parabolics `P_J = M_J U_J`,
`J ⊆ Δ₀`; module `Langlands.Global.AdelicLeadingCuspidalComponents`), and let
`K` be a subgroup of `G(𝔸)` such that

- `K` is a maximal compact subgroup (`IsMaximalCompactSubgroup F G K`);
- `P₀(𝔸) K = G(𝔸)` for the minimal standard parabolic `P₀ = P_∅`
  (`IsIwasawaCompact (𝓕.p ⟨∅, _⟩) K`);
- for every standard index `J`, the inverse image of `K` in `M_J(𝔸)` is a
  maximal compact subgroup of `M_J(𝔸)`.

Then for every closed matrix embedding `rho : G → GL_N`
(`IsClosedSubgroup rho`), every standard index `J`, every cusp form `ψ` on
`M_J(F) \ M_J(𝔸)` (`𝓕.IsLeviCuspForm Kinf rho J ψ` with
`Kinf = K.comap (ofInfinite F G)`: an automorphic form on `M_J(F) \ M_J(𝔸)` for
`K_∞ ∩ M_J(F_∞)` and the restriction of `rho`, whose constant terms along all
proper parabolics of `M_J` vanish), every `g ∈ G(𝔸)` and every real `R`, the
predicate `𝓕.HasLeviPairingMajorant J ψ g rho R` of module
`Langlands.Global.AdelicLeviConstantTermPairing` holds: there is an integrable
real function `b` on the norm-one quotient `M_J(F) \ M_J(𝔸)^1` (for its
quotient Haar measure `normOneRationalQuotientHaarMeasure`) such that for almost
every class `q` some representative `x ∈ M_J(𝔸)^1` of `q` satisfies

`‖ι(x) g‖^R · |ψ(x)| ≤ b(q)`,

where `ι : M_J(𝔸) → G(𝔸)` is the Levi embedding and `‖·‖` is the adelic source
norm `RepresentationGrowth.adelicSourceNorm F G rho` of `rho`.

## Source and correspondence

C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
series* (1995), registered as `moeglin-waldspurger-1995-spectral-decomposition`
(chapter file `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`):
I.2.12 (Corollary, p.35) and I.2.18 (p.39). Cuspidal automorphic forms are
rapidly decreasing on Siegel domains: on a Siegel set of `M_J(𝔸)^1`, `|ψ|` is
bounded by every negative power of the height. The height of `ι(x) g` is
bounded by a power of the height of `x`, with a constant depending on `g`, and
a negative power of the height that is large enough is integrable on a Siegel
set. Taking representatives in a Siegel set gives the majorant for `R ≥ 0`;
for `R < 0` the weight is bounded and cusp forms are bounded. The setting of
MW, a maximal compact subgroup in good position with respect to a minimal Levi
subgroup (MW I.1.4, file `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`,
pp.4–5), is expressed by the two Iwasawa and Levi hypotheses on `K`.

The predicate is the integrability hypothesis of the continuous norm-one Levi
pairing `StandardParabolicFamily.constantTermLeviPairingCLM`,
`v ↦ ∫_{M_J(F) \ M_J(𝔸)^1} (C_J v)(ι(m) g) \overline{ψ(m)} dm`, on the
uniform-growth spaces `𝔉^R_L`. These are the pairings of J. Bernstein and
E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), §6.2, (6.8), p.202, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`. The proposition
asserts the hypothesis for all cusp forms, adelic points and exponents at once.
That is how the pole-detection arguments for Eisenstein series (BL §8.6) use
it.

## Scope

Only the number field case is stated. The statement asserts integrability
only. It does not assert the decay estimate itself, or uniformity in `g` or in
`ψ`.
