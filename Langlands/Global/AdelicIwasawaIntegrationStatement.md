# The Iwasawa integration formula on `G(𝔸_F)`

Author: Worker 3659.

`Langlands.Global.AdelicGroupPoints.AdelicIwasawaIntegrationStatement` is a
proposition definition. It asserts no proof and is a target for a
separate proof task.

## Statement

Let `F` be a number field in universe `u`, let `G` be a connected
reductive group scheme over `Spec F`, and let `χ : 𝔾_m ⟶ G` be a
cocharacter. Let the following inclusions represent the published dynamic
subgroup functors:

- `iP : P ⟶ G` represents `Dynamic.parabolic χ`, the parabolic
  `P = P_G(χ)`;
- `iM : M ⟶ G` represents `Dynamic.centralizer χ`, the Levi factor
  `M = Z_G(χ)`;
- `iU : U ⟶ G` represents `Dynamic.unipotent χ`, the unipotent radical
  `U = U_G(χ)`.

Let `K` be a compact subgroup of `G(𝔸_F)` with `P(𝔸_F) · K = G(𝔸_F)`.
In Lean this is `Set.range (map F P G iP) * K = Set.univ`, the second
conjunct of the published `IsParabolicIwasawaCompact`. Then there is a
real constant `c > 0` such that for every compactly supported continuous
`f : G(𝔸_F) → ℂ`

`∫_{G(𝔸_F)} f(g) dg = c · ∫_K ∫_{M(𝔸_F)} ∫_{U(𝔸_F)} δ_P(m)⁻¹ f(u m k) du dm dk`.

The ingredients are these:

- `dg`, `dm` and `du` are Mathlib's `Measure.haar` on the published adelic
  point groups `AdelicGroupPoints F G`, `F M` and `F U`.
- `dk` is `compactHaarProbability F G K hK`, the Haar probability measure
  on `K` from `AdelicParabolicModulus.lean`.
- `u m k` stands for `map F U G iU u * map F M G iM m * k` in `G(𝔸_F)`.
- `δ_P(m)` is `parabolicModulus F hP hU` evaluated at the image of `m`
  under `Dynamic.centralizerToParabolic hP hM : M ⟶ P`. This is the Haar
  modulus of conjugation by `m` on `U(𝔸_F)`, `μ(m E m⁻¹) = δ_P(m) μ(E)`.
- The integrals are iterated Bochner integrals: `dk` outermost, `du`
  innermost.

The constant `c` only absorbs the three independent Haar normalizations
of `dg`, `dm` and `du`. Every Haar measure on `K` with `meas(K) = 1`
equals `dk` (`eq_compactHaarProbability`).

The `haveI` lines only install the instances that the published lemmas
prove for these data. `G` is affine and smooth. `P`, `M` and `U` are
affine, and `M` and `U` are locally of finite type, so their adelic points
are locally compact. No hypothesis is added.

## Relation to the source

Mœglin–Waldspurger I.1.13, printed p. 18, fix Haar measures on `U(𝔸)` and
`M`, give `K` measure 1, and state the compatibility formula

`∫_G f(g) dg = ∫_{U(𝔸) × M × K} f(u m k) m^{-2ρ_P} dk dm du`,

with `m^{2ρ_P} = δ_P(m)` (see `AdelicParabolicModulusStatement`). Here
`G` and `M` denote the adelic groups. In the source, the measure `dg` on
`G` is defined by this formula for `P_0`. With independently normalized
`Measure.haar` the formula therefore holds up to a positive constant,
which the statement records as `c`. There are three further differences
from the source.

- Mœglin–Waldspurger take `K` maximal compact. They take `P` standard,
  for a fixed minimal parabolic and Levi. Here `K` is any compact subgroup
  with `P(𝔸_F) K = G(𝔸_F)`, and `P` is any dynamic parabolic. The
  standard argument still applies. `G(𝔸_F)` is unimodular. The left Haar
  measure on `P(𝔸_F) = U(𝔸_F) ⋊ M(𝔸_F)` is `δ_P(m)⁻¹ du dm` in the
  coordinates `p = u m`. The map `(p, k) ↦ p k` integrates `d_l p dk` to
  a Haar measure on `G(𝔸_F) = P(𝔸_F) K`.
- Getz–Hahn (8.25), printed p. 229, record the local analogue
  `dg = δ_P(m) dk dm dn` for `g = k m n`, with `G(F) = K M(F) N(F)`.
- The source integrates a product measure, while the statement uses
  iterated integrals. For compactly supported continuous `f` these agree
  by Fubini. Every integrand involved is continuous with compact support,
  because `U(𝔸_F)` and `M(𝔸_F)` embed as closed subgroups.

A `K` from the published `IsParabolicIwasawaCompact F G P iP K` satisfies
the hypotheses: it is compact, and `P(𝔸_F) K = G(𝔸_F)`.

## Sources

- Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*
  (`moeglin-waldspurger-1995-spectral-decomposition`), chapter file
  `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, I.1.13, printed
  p. 18 (PDF p. 18).
- Getz–Hahn, *An Introduction to Automorphic Representations* (2024)
  (`getz-hahn-2024-automorphic-representations`), §8.6, (8.25), printed
  p. 229 (PDF p. 242). Local analogue, for context.
