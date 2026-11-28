# Proof of the boundedness of forms with only negative maximal cuspidal exponents

Module `Langlands.Global.AdelicCuspidalExponentBoundednessProof`. It proves
`Langlands.Global.CuspidalExponentBoundednessStatement` (module
`Langlands.Global.AdelicCuspidalExponentBoundednessStatement`) at an arbitrary universe `u`:

- `cuspidalExponentBoundedness_of_parabolicCuspidalVanishing` derives the statement from the
  vanishing criterion `ParabolicCuspidalVanishingStatement`;
- `cuspidalExponentBoundedness` is the statement itself, obtained from the published
  `parabolicCuspidalVanishing` (module `Langlands.Global.AdelicParabolicCuspidalVanishingProof`).

The statement is the first step of the proof of the lemma of Bernstein–Lapid §6.4, for an
automorphic function `f` on `U_R(𝔸) M_R(F) \ G(𝔸)`. Suppose every nonzero component `c(Q, μ)`,
`Q ⊆ R`, of the supplied cuspidal projections and exponent decompositions has `R = Q ∪ {β}` with
`β ∉ Q` and `⟨Re μ, β^∨⟩ < 0`. Then for every `Q ⊆ R` and `g ∈ G(𝔸)` the function
`m ↦ C_Q f(m g)` is bounded on `M_R(𝔸)^1`.

## Auxiliary lemmas

- Rank zero (private). A closed subgroup of the general linear group of rank zero has at most
  one point over every base, so `G(𝔸)` is a subsingleton when `N = 0`.
- `isIwasawaCompact_of_minimal''`, `not_maximal_of_lt'`, `leviPairingIntegrand_sub''` and
  `isCuspidalProjection_sub''` (private). They are copies of private lemmas of the published
  module `Langlands.Global.AdelicCuspidalExponentNonexistenceReduction`:
  - `P_0(𝔸) K = G(𝔸)` gives `P_Q(𝔸) K = G(𝔸)` for every standard `Q`;
  - below a maximal parabolic `Q` of `M_R` no standard parabolic is maximal in `R`, by counting
    simple roots;
  - cuspidal projections are compatible with differences.
- `height_radical_mul`: for `Q ⊆ R`, left translation by `U_Q(𝔸)` does not change the Iwasawa
  height `H_{P_R}`. `U_Q → G` factors through `P_R` (`SubgroupFunctor.rangeFactor`), and
  points of the unipotent group `U_Q` have zero logarithm (published
  `characterLog_eq_zero_of_isUnipotent`).
- `height_leviNormOne_mul`: left translation by `M_R(𝔸)^1` does not change `H_{P_R}`, because
  points of the norm-one subgroup have zero logarithm (published `characterLog_eq_zero_iff`).
- `norm_constantTerm_le`: if `|φ(u x)| ≤ C` for all `u ∈ U_Q(𝔸)`, then `|C_Q φ(x)| ≤ C`. The
  normalized measure on the compact quotient `U_Q(F) \ U_Q(𝔸)` is a probability measure.
- `insert_removeSimpleRoot`: for `α ∈ R`, `{α} ∪ (R \ {α}) = R`.

## The proof

**Rank zero.** If `N = 0`, then `G(𝔸)` has at most one point. Hence `C_Q f(m g) = C_Q f(g)`
for every `m`, and `|C_Q f(g)|` is a bound.

**The maximal constant terms.** Let `N > 0`. If `Q ⊆ R` is not maximal in `R`, all components
`c(Q, μ)` vanish by hypothesis, so the cuspidal projection `φc(Q)` is `0`. By the defining pairing
identity of a cuspidal projection, `C_Q f` then lies in the cuspidal annihilator along `Q`. Fix
`α ∈ R` and put `Q₀ = R \ {α}`, a maximal parabolic of `M_R`. Let `Q' < Q₀`. Every `Q'' ⊆ Q'` is
not maximal in `R` (`not_maximal_of_lt'`). Moreover `C_{Q''} C_{Q'} f = C_{Q''} f` (published
`constantTerm_constantTerm_of_parabolicQuotient`), and `C_{Q'} f` is automorphic (published
`constantTermAutomorphy`). So the vanishing criterion gives `C_{Q'} f = 0`. Therefore `C_{Q₀} f`
is cuspidal along `Q₀` and is its own cuspidal projection. Subtracting the two cuspidal
projections of `C_{Q₀} f` (`isCuspidalProjection_sub''`) shows that `C_{Q₀} f − φc(Q₀)` is a
cuspidal projection of the zero function. It therefore vanishes by the published
`eq_zero_of_isCuspidalProjection_zero`, which uses the vanishing criterion. Hence
`C_{Q₀} f = φc(Q₀)`, which has the exponent decomposition `∑_{μ ∈ s(Q₀)} c(Q₀, μ)` supplied by
`IsRelativeCuspidalExponentFamily`. This argument is the one of the published
`cuspidalExponentNonexistence_of_boundedness`.

**The bound on a fibre.** `Kinf`, the preimage of `K` in `G(F_∞)`, is a maximal compact subgroup
of `G(F_∞)` (published `isMaximalCompact_comap_ofInfinite`), and `P_R(𝔸) K = G(𝔸)`. The decompositions just
obtained and the hypothesis on the exponents are those of
`CuspidalExponentFibreBoundStatement`. Hence `cuspidalExponentFibreBound` (module
`Langlands.Global.AdelicCuspidalExponentFibreBound`) gives `C` with `|f(x)| ≤ C` whenever
`H_{P_R}(x) = H_{P_R}(g)`.

**Averaging.** Let `m ∈ M_R(𝔸)^1` and `u ∈ U_Q(𝔸)`. By `height_radical_mul` and
`height_leviNormOne_mul`, `H_{P_R}(u m g) = H_{P_R}(g)`, so `|f(u m g)| ≤ C`. By
`norm_constantTerm_le`, `|C_Q f(m g)| ≤ C`.

## Sources and provenance

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series* (2024),
  registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`: §6.4 (p. 204). The
  first step of the proof of the lemma says that any right translate of the form is bounded on
  `G(𝔸)^1`, by Mœglin–Waldspurger I.4.1 and the assumptions on the form, and hence so is any
  right translate of each constant term. For the vanishing of the constant terms along the
  non-maximal proper parabolics the source cites its Proposition 6.2. The Lean proof uses instead
  the vanishing criterion (8.1) (§8.1, p. 221; published `parabolicCuspidalVanishing`), both for
  that vanishing and to identify the constant terms along the maximal parabolics of `M_R` with
  their cuspidal projections.
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: I.4.1 (p. 49).

The analytic input does not go through the general statement of I.4.1. It comes from
`cuspidalExponentFibreBound`, which rests on `cuspidalExponentRegionBound` (module
`Langlands.Global.AdelicCuspidalExponentRegionBound`) and `cuspidalExponentLineBound` (module
`Langlands.Global.AdelicCuspidalExponentLineBound`). The source deduces the boundedness of
constant terms from that of right translates. Here both follow at once from the bound on the
fibres of `H_{P_R}`, since these fibres contain `U_Q(𝔸) M_R(𝔸)^1 g`.
