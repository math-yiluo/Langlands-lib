# `Ξ` through a Levi subgroup (Waldspurger, Lemma II.1.6)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalLevi`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.Spherical`, which defines
`IsIwasawaPair`, `iwasawaFactor`, `iwasawaWeight`, `normalizedHaar` and the spherical
function `xi`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333.

- Section I.1, printed p. 240 (PDF p. 6): for a semi-standard parabolic subgroup
  `P = M U`, `G = P K`, and `M ∩ K` has, relative to `M`, the same properties as `K`
  relative to `G`. For `g ∈ G` one chooses `u_P(g) ∈ U`, `m_P(g) ∈ M` and
  `k_P(g) ∈ K` with `g = u_P(g) m_P(g) k_P(g)`. Every closed subgroup `H` carries
  the Haar measure with `mes(H ∩ K) = 1`.
- Section II.1, printed p. 252 (PDF p. 18): for a semi-standard parabolic subgroup
  `P = M U`, a function `Ξ^M` on `M` is defined "as `Ξ` was just defined on `G`".
- Lemma II.1.6, printed pp. 252–253 (PDF pp. 18–19): for every `g ∈ G`,

  `Ξ(g) = ∫_K δ_P(m_P(kg))^{1/2} Ξ^M(m_P(kg)) dk`.

The function `Ξ` of Spherical is defined by the integral formula
`Ξ(g) = ∫_K δ₀(m₀(kg))^{1/2} dk` of II.1 (see `Spherical.md`), from data
`(P₀, K, δ₀)` with `G = P₀ K`. Accordingly `Ξ^M` here is `xi` on the group `M`,
built from the data `(P₀ ∩ M, K ∩ M, δ₀^M)`.

## Scope

The module works with abstract data of the shape used in Waldspurger's lemma:

- `G` is a topological group with a Borel measurable structure; `K`, `P₀`, `P`, `M`
  are subgroups of `G`.
- `G = P₀ K` (`hP₀K : IsIwasawaPair P₀ K`); `δ₀ : P₀ →* ℝ≥0ˣ` is trivial on
  `P₀ ∩ K`. As in Spherical, `δ₀` plays the role of `δ₀ ∘ m₀` on `P₀`.
- `mP : P →* M` plays the Levi projection `P = M U → M`; its kernel plays `U`.
- `δP : M →* ℝ≥0ˣ` plays the modulus character `δ_P` of `P`, as a character of `M`.
- `δ₀M` is a character of `P₀ ∩ M` (the type `P₀.subgroupOf M`); it plays the modulus
  character `δ₀^M` of the minimal parabolic subgroup `P₀ ∩ M` of `M`. It is assumed
  trivial on `P₀ ∩ M ∩ K`.
- `M = (P₀ ∩ M)(K ∩ M)` (`hM : IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M)`).
  `LeviData.isIwasawaPair` derives it from the other data when `m_P` maps `P₀` into
  `P₀` and `P ∩ K` into `K`.

The relations between these data are the fields of the Prop structure `LeviData`
(below). They are standard properties of a parabolic subgroup `P ⊇ P₀`, its Levi
decomposition and the modulus characters. The module does not construct a reductive
group, its parabolic subgroups, `K` or the modulus characters, and it does not
verify these properties for them; that is done when the generic data are specialized
to a reductive group.

Waldspurger states the lemma for semi-standard `P` and begins the proof by replacing
`P₀`, using that `Ξ` does not depend on the minimal parabolic subgroup (they are
conjugate under `K`). The Lean statement is the case `P₀ ≤ P` that the proof then
treats. The independence of `Ξ` from `P₀` is not stated or proved here.

## Definitions

- `leviComponent hPK mP g : M` is `mP (iwasawaFactor hPK g)`: the image under the
  Levi projection of the `P`-component chosen in `g ∈ p K`. Writing
  `p = u m` with `m = mP p` and `u = p m⁻¹` in the kernel of `mP` gives
  `g = u m k`, so `leviComponent` is one choice of Waldspurger's `m_P(g)`.
- `LeviData K P₀ P M δ₀ δP δ₀M mP : Prop`, with fields:
  - `le_P₀ : P₀ ≤ P` and `le_M : M ≤ P`;
  - `apply_inclusion`: `mP m = m` for `m ∈ M` (`m_P` is a retraction onto `M`);
  - `mem_of_apply_eq_one`: the kernel of `mP` lies in `P₀` (for Waldspurger,
    `U ⊆ U₀ ⊆ P₀`);
  - `δ₀_of_apply_eq_one`: `δ₀` is trivial on the kernel of `mP` inside `P₀` (the
    modulus character `δ₀` is trivial on `U ⊆ U₀`);
  - `δ₀_of_mem`: `δ₀(p) = δ_P(p) δ₀^M(p)` for `p ∈ P₀ ∩ M = M₀ (U₀ ∩ M)` (on `M₀`
    because the Lie algebra of `U₀` is the direct sum of those of `U` and of
    `U₀ ∩ M`; all three characters are trivial on `U₀ ∩ M`);
  - `δP_of_mem`: `δ_P` is trivial on `K ∩ M` (a continuous positive character is
    trivial on a compact group).

## Results

- `IsIwasawaPair.mono`: `G = P₀ K` and `P₀ ≤ P` give `G = P K`.
- `LeviData.isIwasawaPair`: under `LeviData`, if `G = P₀ K`, `m_P` maps `P₀` into
  `P₀` and maps `P ∩ K` into `K`, then `M = (P₀ ∩ M)(K ∩ M)`.
- `LeviData.iwasawaWeight_mul` (pointwise form of the lemma): under `LeviData`,
  `hM`, and `δ₀` trivial on `P₀ ∩ K`, for `p ∈ P` and `k_M ∈ K ∩ M`,

  `φ₀(k_M p) = δ_P(m_P(p))^{1/2} φ₀^M(k_M m_P(p))`,

  where `φ₀ = iwasawaWeight hP₀K δ₀` and `φ₀^M = iwasawaWeight hM δ₀M` are the
  integrands of `Ξ` and `Ξ^M`. No topology is used.
- `LeviData.sqrt_mul_xi_leviComponent_mul`: the integrand of the lemma does not
  depend on the factorization. Under `LeviData`, `δ₀^M` trivial on
  `P₀ ∩ M ∩ K`, and `m_P` mapping `P ∩ K` into `K`, for `p ∈ P` and `k ∈ K`,
  `δ_P(m_P(pk))^{1/2} Ξ^M(m_P(pk)) = δ_P(m_P(p))^{1/2} Ξ^M(m_P(p))`. It assumes
  `K ∩ M` compact (needed to define `Ξ^M`).
- `LeviData.xi_eq_integral` (Lemma II.1.6): assume `LeviData`, `G = P₀ K`, `hM`,
  `δ₀` trivial on `P₀ ∩ K`, `K` compact and open, `K ∩ M` compact, and `G` second
  countable. Then for every `g ∈ G`,

  `xi hP₀K δ₀ g = ∫_K δ_P(m_P(kg))^{1/2} · xi hM δ₀M (m_P(kg)) dk`,

  with `m_P(kg) = leviComponent (hP₀K.mono le_P₀) mP (k g)` and the integral taken
  for `normalizedHaar K`. The measure on `K ∩ M` defining `Ξ^M` is
  `normalizedHaar (K.subgroupOf M)`, of total mass one, as in Waldspurger's
  normalization `mes(M ∩ K) = 1`. This theorem does not use triviality of `δ₀^M` on
  `P₀ ∩ M ∩ K` or `m_P(P ∩ K) ⊆ K`.

For a Levi subgroup `M`, which is closed in `G`, `K ∩ M` is compact when `K` is.
Openness of `K` makes the integrands continuous. Second countability makes the
Borel σ-algebra of `(K ∩ M) × K` the product σ-algebra, so that Fubini's theorem
applies.

## Proof notes

Waldspurger's proof is representation-theoretic. He identifies `π = I_{P₀}^G 1`
with `I_P^G π^M`, where `π^M = I_{P₀ ∩ M}^M 1` (induction in stages), and the
spherical vector `e` with the function `k ↦ e^M`. Then
`Ξ(g) = ⟨π(g)e, e⟩ = ∫_K ⟨e(kg), e(k)⟩ dk`, and
`⟨e(kg), e(k)⟩ = δ_P(m_P(kg))^{1/2} Ξ^M(m_P(kg))`.

The Lean proof uses the integral formulas for `Ξ` and `Ξ^M` instead.

1. Pointwise identity (`LeviData.iwasawaWeight_mul`). Let `m = m_P(p)`. Factor
   `k_M m = a k'` in `M` with `a ∈ P₀ ∩ M`, `k' ∈ K ∩ M`, so
   `φ₀^M(k_M m) = δ₀^M(a)^{1/2}`. Then `k_M p = a v k'` with
   `v = k' m⁻¹ p k'⁻¹ ∈ P`. Since `m_P` is a retraction onto `M`, `m_P(v) = 1`, so
   `v ∈ P₀` and `δ₀(v) = 1`. Hence
   `φ₀(k_M p) = δ₀(a v)^{1/2} = δ₀(a)^{1/2} = (δ_P(a) δ₀^M(a))^{1/2}`, and
   `δ_P(a) = δ_P(k_M m k'⁻¹) = δ_P(m)`.
2. Integrating step 1 over `k_M ∈ K ∩ M` gives
   `∫_{K ∩ M} φ₀(k_M x) dk_M = δ_P(m_P(x))^{1/2} Ξ^M(m_P(x))` for `x ∈ G`, with
   `m_P(x) = leviComponent`. Here `x = q k''` with `q = iwasawaFactor x`, and
   `φ₀` is right `K`-invariant.
3. The right side of the lemma is then `∫_K ∫_{K ∩ M} φ₀(k_M k g) dk_M dk`.
   Exchanging the integrals (`integral_integral_swap`), the inner integral over `K`
   equals `Ξ(g)` for each `k_M`, by left invariance of the Haar measure of `K`
   (`k_M ∈ K`). Since `K ∩ M` has measure one, the result is `Ξ(g)`.
