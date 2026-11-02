# The pairing on `I_P^G 1` and `Ξ(g⁻¹) = Ξ(g)`

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalInverse`,
namespace `Langlands.HarishChandraSchwartz`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333.

- I.1 (printed p. 240, PDF p. 6): every closed subgroup `H` gets the left invariant
  measure with `mes(H ∩ K) = 1`. From it one gets a positive functional, written
  `∫_{H\G}`, on the locally constant functions `f` that are compactly supported
  modulo `H` and satisfy `f(h g) = δ_H(h) f(g)`, where `δ_H` is the modulus of `H`.
  The same page records `G = P K` for every semi-standard parabolic `P`.
- I.3 (printed p. 243, PDF p. 9): the bilinear form
  `⟨f, f̌⟩ = ∫_{P\G} ⟨f(g), f̌(g)⟩ dg` on `I_P^G V × I_P^G V̌`. It identifies
  `I_P^G V̌` with the contragredient of `I_P^G V`.
- II.1 (printed pp. 250–251, PDF pp. 16–17): `π = I_{P₀}^G 1`, and `e` is the
  `K`-invariant vector with `e(1) = 1`. Waldspurger notes `π̌ = π`, defines
  `Ξ(g) = ⟨π(g)e, e⟩`, and records `Ξ(g) = ∫_K δ₀(m₀(kg))^{1/2} dk`.
- Lemma II.1.4 (printed p. 252, PDF p. 18): `Ξ(g) = Ξ(g⁻¹)` for every `g ∈ G`.
  Waldspurger's whole proof is: "Cela résulte de l'égalité `π = π̌`."

The published module `Langlands.HarmonicAnalysis.HarishChandraSchwartz.Spherical`
defines `Ξ` by the integral formula, as `xi hPK δ`, for abstract data `G = P K` and a
positive character `δ` of `P`. That module lists II.1.4 as not proved. This module
proves it when `δ` is the modular character of `P` and `G` is unimodular.

## Conventions and hypotheses

`modularCharacter` is Mathlib's `MeasureTheory.Measure.modularCharacter`. For a
locally compact group `H` it is the factor in `map (· * q) haar = Δ(q) • haar`, so
`μ(E q⁻¹) = Δ(q) μ(E)`. Worker 235's module
`Langlands.Analysis.Local.ModularCompactAverage` shows that the compact average is
right invariant on functions with `φ(q x) = Δ_P(q) φ(x)`. This is the covariance
condition of the I.1 functional with `H = P`, so `Δ_P` plays the role of
Waldspurger's `δ_P`. As a check of the convention (a hand computation, not
formalized here): for the group of matrices `(a b; 0 1)` over a local field,
`Δ(q) = |a(q)|`, the modulus of the action on the unipotent radical.

The results use some of these hypotheses on the data:

- `G` is a topological group that is locally compact and second countable, with
  its Borel σ-algebra. The two definitions need only a topological group with a
  measurable structure and a compact subgroup `K`.
- `hG : ∀ g : G, modularCharacter g = 1`: `G` is unimodular. Waldspurger does not
  state this. It holds for reductive groups over a local field, but it is not proved
  in this module. It must be supplied when the data are specialized to a reductive
  group.
- `P` is a closed subgroup with `[LocallyCompactSpace P]`.
- `K` is a compact open subgroup, and `hPK : IsIwasawaPair P K` says `G = P K`.
- `δ : P →* ℝ≥0ˣ`, with `hδ : ∀ p, δ p = modularCharacter p`. For `P = P₀` this says
  that `δ` is the modulus `δ₀ ∘ m₀` of `P₀`.
- Functions are assumed continuous rather than locally constant. Locally constant
  functions are continuous, so this is weaker than Waldspurger's condition.

## Definitions

- `compactAverage K φ = ∫_K φ(k) dk`, for `φ : G → ℂ`, where the integral is taken
  for `normalizedHaar K`, the Haar measure of `K` of total mass one. This module uses
  it in place of the functional `∫_{P\G}` of I.1 on functions with
  `φ(p x) = δ_P(p) φ(x)`. With Waldspurger's normalizations `mes(K) = 1` and
  `mes(P ∩ K) = 1`, `G = P K` gives `∫_{P\G} φ = ∫_K φ(k) dk`. That identification
  is **not** proved here: the quotient functional is not constructed, and the
  module takes the average over `K` as the definition. Waldspurger writes `Ξ` with
  this average in II.1.
- `inducedPairing K f₁ f₂ = compactAverage K (f₁ f₂)`: the bilinear form
  `⟨f₁, f₂⟩ = ∫_{P\G} f₁(g) f₂(g) dg` of I.3, for the trivial representation of the
  Levi factor, written as the average over `K`. Both definitions are defined for all
  functions. The invariance results below need the covariance and continuity
  hypotheses.

## Results

Section `Haar`:

- `isMulRightInvariant_haar hG`: if the modular character of `G` is trivial, the Haar
  measure `haar` of `G` is right invariant.
- `comap_subtype_eq_smul_normalizedHaar hK μ`: for a compact open subgroup `K` and a
  Haar measure `μ` of `G`, the restriction of `μ` to `K` equals
  `μ(K) • normalizedHaar K`.
- `modularCharacter_eq_one_of_mem_compactOpen hP hK p hp`: for closed `P` and compact
  open `K`, the modular character of `P` is `1` on `P ∩ K`.

Section `Average`:

- `inducedPairing_comm` (no hypothesis): `⟨f₁, f₂⟩ = ⟨f₂, f₁⟩`.
- `compactAverage_mul_right hG hP hK hPK φ hφ hcov g`: let `G` be unimodular, `P`
  closed, `K` compact open and `G = P K`. If `φ : G → ℂ` is continuous and
  `φ(q x) = Δ_P(q) φ(x)` for all `q ∈ P`, then `∫_K φ(k g) dk = ∫_K φ(k) dk` for every
  `g`. This is the right invariance of the I.1 functional on `P\G`, in its
  compact-average form.
- `inducedPairing_mul_right hG hP hK hPK f₁ f₂ hf₁ hf₂ hcov₁ hcov₂ g`: under the same
  hypotheses on `G`, `P` and `K`, if `f₁, f₂ : G → ℂ` are continuous and
  `f_i(q x) = Δ_P(q)^{1/2} f_i(x)`, then `⟨ρ(g) f₁, ρ(g) f₂⟩ = ⟨f₁, f₂⟩`, where
  `ρ(g) f = f(· g)` is right translation. This is the invariance
  `⟨π(g) f, π(g) f̌⟩ = ⟨f, f̌⟩` of the I.3 pairing, for the trivial representation of
  the Levi factor.

Section `Spherical`, with `δ : P →* ℝ≥0ˣ`:

- `modular_eq_one_of_mem hP hK hδ`: if `δ` equals the modular character of the
  closed subgroup `P` and `K` is compact open, then `δ` is trivial on `P ∩ K`. This
  is the hypothesis that the results of `Spherical` need.
- `xi_eq_inducedPairing hδ g` (`δ` trivial on `P ∩ K`; no other hypothesis):
  `Ξ(g) = ⟨ρ(g) e, e⟩` for `inducedPairing`, where `e = iwasawaWeight hPK δ` is the
  function `e(p k) = δ(p)^{1/2}`. This is Waldspurger's definition of `Ξ` in II.1,
  with the pairing written as the average over `K`.
- `xi_inv hG hP hK hδ g` (**Lemma II.1.4**): if `G` is unimodular, `P` is closed,
  `K` is compact open, `G = P K`, and `δ` is the modular character of `P`, then
  `Ξ(g⁻¹) = Ξ(g)`.

The function `e` and the pairing are functions on `G`. The module does not compare
`inducedPairing` with a pairing of an induced representation from the
representation framework, nor `Ξ` with a matrix coefficient of such a
representation. That comparison remains an open proof obligation, as stated in
`Spherical`.

## Proof notes

`comap_subtype_eq_smul_normalizedHaar`: the restriction of `μ` to the open subgroup
`K` is a Haar measure on `K` (`IsHaarMeasure.comap`). It has total mass `μ(K)`.
Uniqueness of Haar measure (`haarMeasure_unique`) gives the formula.

`modularCharacter_eq_one_of_mem_compactOpen`: `P ∩ K` is a compact open subgroup of
`P`. It is compact because `P` is closed. Worker 235's
`ModularCompactAverage.modularCharacter_eq_one_of_mem` applies.

`compactAverage_mul_right`: by `isMulRightInvariant_haar`, `haar` is right
invariant. Worker 235's `ModularCompactAverage.setIntegral_mul_right_eq` gives
`∫_K φ(x g) dμ = ∫_K φ(x) dμ` for the set integrals over `K` with `μ = haar`. Both
sides are integrals for the restriction of `μ` to `K`. That restriction is
`μ(K) • normalizedHaar K`. Cancel the factor `μ(K)`, which is positive and finite.

`inducedPairing_mul_right`: apply `compactAverage_mul_right` to `φ = f₁ f₂`, using
`Δ_P(q)^{1/2} Δ_P(q)^{1/2} = Δ_P(q)`.

`xi_eq_inducedPairing`: unfold the definitions. On `K`, `e(k) = 1`, so the integrand
`e(k g) e(k)` is `e(k g)`, the integrand of `xi`.

`xi_inv`: this is Waldspurger's argument with the pairing written as an average
over `K`. The function `e` is continuous because `K` is open, and
`e(q x) = Δ_P(q)^{1/2} e(x)` by `hδ`. The same holds for `ρ(g) e`. So
`inducedPairing_mul_right`, applied with the element `g⁻¹`, gives
`⟨ρ(g) e, e⟩ = ⟨e, ρ(g⁻¹) e⟩`. By `xi_eq_inducedPairing` the left side is `Ξ(g)`.
By `inducedPairing_comm` and `xi_eq_inducedPairing` the right side is `Ξ(g⁻¹)`.
In Waldspurger's terms, the invariant pairing identifies `π̌` with `π`.
