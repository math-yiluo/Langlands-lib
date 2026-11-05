# The family `(p_χ φ)_{χ ∈ Â_G}` and the end of the proof of Theorem VIII.1.1 (Waldspurger)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralProjectionFamily`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.Representation.Plancherel.UnramifiedCharacters`: `unitaryCharacters A`, the
  subgroup of continuous homomorphisms `A →ₜ* ℂˣ` of absolute value one (read in namespace
  `Langlands.Plancherel`);
- `CentralFourierInversion`: `HasFGCompactOpenQuotients` and
  `eq_zero_of_forall_centralProjection_eq_zero` (Fourier inversion on `A_G` for `p_χ`); through
  it `CentralProjection` (`centralProjection`, `Space.centralProjection`, `IsUnitaryCharacter`,
  `CentralWeights`) and `Basic` (`Space`, `Space.ext`, `Space.coe_mem`);
- `CentralProjectionVanishing`: `centralProjection_eq_zero_of_schwartzAction_eq_zero` (the
  vanishing of `p_χ φ` for one `χ`); through it `SchwartzAction` (`schwartzAction`,
  `HasTemperedCoefficients`), `L2` (`L2Weights`, `Space.check`), `DiscreteCoefficientSpace`
  (`subrepresentationCoefficientSpace`), `Langlands.Representation.Unitary.Basic`
  (`InvariantPositiveForm`) and `Langlands.Analysis.Local.QuotientMeasure` (`IsCompatible`,
  read in namespace `Langlands.QuotientIntegration`).

From Mathlib it uses `LinearMap.pi`, `injective_iff_map_eq_zero`, `Units.continuous_iff`,
`Units.val_inv_eq_inv_val`, `Units.continuous_val`, `Continuous.inv₀` and
`Continuous.measurable`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus 234.

- VIII.4, printed p. 327 (PDF p. 93): "Notons `Â_G` l'ensemble des caractères unitaires de
  `A_G`, i.e. `Â_G = {χ ∈ Hom(A_G, ℂ^×); Re(χ) = 0}`", and for `χ ∈ Â_G` "On définit une
  application `p_χ : C(G) → C_lisse(G)_χ` par la formule `(p_χ f)(g) = ∫_{A_G} χ⁻¹(a) f(ag) da`.
  L'intégrale est absolument convergente."
- I.1, printed p. 239 (PDF p. 5): "On note `Hom(G, ℂ*)` le groupe des homomorphismes continus
  de `G` dans `ℂ*`". So `Â_G` is the set of continuous characters of `A_G` of absolute value
  one, which is the Library's `unitaryCharacters A_G`.
- End of VIII.5, proof of Theorem VIII.1.1, printed p. 332 (PDF p. 98): "Posons
  `φ = f − κ(ψ)`. On va montrer que `φ = 0`. Il est clair que `φ ∈ °C(G)`. [...] Donc
  `φ̂(ω, G) = 0` pour tout `ω ∈ E₂(G)`, i.e. `ω(ˇφ) = 0` pour tout `ω ∈ E₂(G)`. Supposons
  `φ ≠ 0`. Par inversion de Fourier sur le groupe `A_G`, il existe `χ ∈ Â_G` tel que
  `p_χ φ ≠ 0`. D'après le Théorème VIII.4.2, on peut alors trouver [...]
  `(ω, E) ∈ E₂(G)_χ` [...] `v₁, v₂ ∈ E` de sorte que l'intégrale [...] soit non nulle. [...]
  Or `ω(ˇφ) = 0`. Contradiction qui démontre le Théorème VIII.1.1."

This module packages the two halves of that argument. The first half (Fourier inversion) is
`eq_zero_of_forall_centralProjection_eq_zero`; the second half (for a fixed `χ`, `p_χ φ = 0`
when `ω(ˇφ) = 0` for the `ω ∈ E₂(G)_χ` and `p_χ φ` lies in the span of their coefficients) is
`centralProjection_eq_zero_of_schwartzAction_eq_zero`. Waldspurger argues by contradiction; the
Lean statement is the direct form: `p_χ φ = 0` for every `χ ∈ Â_G`, hence `φ = 0`.

## Scope: abstract data and explicit hypotheses

The module does not construct `A_G`, its Haar measure, `E₂(G)_χ` or Waldspurger's `Ξ, σ`; it
does not prove `HasFGCompactOpenQuotients A_G`, the inclusion of Theorem VIII.4.2, or
`ω(ˇφ) = 0`. These enter as hypotheses.

**Section `Family`.** `G` is a group with a topology and `A` a subgroup of `G`.

- `unitaryCharacterOfContinuous χ h1 hc` (definition) and `unitaryCharacterOfContinuous_apply`:
  no further hypotheses; `χ : A →* ℂˣ`, `h1 : ∀ a, ‖(χ a : ℂ)‖ = 1` and
  `hc : Continuous fun a => (χ a : ℂ)`.

Then `A` carries a measurable structure in which open sets are measurable.

- `isUnitaryCharacter_of_mem_unitaryCharacters χ`: `χ : unitaryCharacters A`.

Then `G` is moreover a topological group with a compact open subgroup
(`[Nonempty (CompactOpenSubgroup G)]`), `μA` is a measure on `A` and `Ξ, σ : G → ℝ`.

- `Space.centralProjectionFamily hw` (definition) and `Space.centralProjectionFamily_apply`:
  `hw : CentralWeights μA Ξ σ` (the published hypotheses of `CentralProjection` under which
  `p_χ` converges absolutely on `C(G)`).
- `Space.centralProjectionFamily_injective`: `[MeasurableMul A]`, `[μA.IsMulLeftInvariant]`,
  `[μA.IsOpenPosMeasure]`, `[IsFiniteMeasureOnCompacts μA]`, `hw`,
  `hA : IsClosed (A : Set G)`, `hAc : A ≤ Subgroup.center G` and
  `hFG : HasFGCompactOpenQuotients A`.

**Section `EndOfProof`.** `G` is a Hausdorff, locally compact, second countable topological
group with a Borel measurable structure and a compact open subgroup; `A` is a subgroup of `G`
with a Borel measurable structure, and the left quotient `LeftQuotient A` (`A \ G`) carries a
Borel measurable structure.

- `Space.eq_zero_of_forall_schwartzAction_eq_zero`: `[MeasurableMul A]`; a measure `μA` on `A`
  with `[μA.IsHaarMeasure]`, `[μA.IsMulRightInvariant]` and `[SFinite μA]`; a measure `μG` on
  `G` with `[IsFiniteMeasureOnCompacts μG]`, `[μG.IsMulLeftInvariant]` and
  `[μG.IsInvInvariant]`; a measure `ν` on `LeftQuotient A`; `hA : IsClosed (A : Set G)`,
  `hAc : A ≤ Subgroup.center G`, `hFG : HasFGCompactOpenQuotients A`,
  `hν : IsCompatible A μG μA ν` (the quotient measure satisfies the Weil formula);
  `Ξ, σ : G → ℝ` with `hwA : CentralWeights μA Ξ σ`, `hw : L2Weights μG Ξ σ`,
  `hΞ : ∀ g, Ξ g⁻¹ = Ξ g` and `hσ : ∀ g, σ g⁻¹ = σ g`; for each `χ : unitaryCharacters A` a
  complex vector space `V χ`, a representation `ρ χ : Representation ℂ G (V χ)`, a form
  `b χ : InvariantPositiveForm (ρ χ)`, smoothness `hs χ : IsSmooth (ρ χ)` and a predicate
  `p χ` on the subrepresentations of `ρ χ`; `φ : Space Ξ σ`;
  `hS : ∀ χ S, p χ S → ∃ (hSa : IsAdmissible S.toRepresentation)
  (hT : HasTemperedCoefficients Ξ σ S.toRepresentation),
  schwartzAction hw hSa hT (Space.check hΞ hσ φ) = 0` (each `S` in the class `p χ` is
  admissible with tempered coefficients and `π_S(ˇφ) = 0`); and
  `hmem : ∀ χ, ∃ c ∈ subrepresentationCoefficientSpace (hs χ) (p χ),
  ⇑c = centralProjection μA (χ : A →ₜ* ℂˣ).toMonoidHom φ` (`p_χ φ ∈ Σ_S A(S)`).

In Waldspurger's situation `A = A_G` is closed and central; `μA` is a Haar measure on `A_G`
(which is commutative, so `μA` is also right invariant, and σ-finite since `A_G` is
σ-compact); `μG` is a Haar measure on the unimodular group `G`; `ν` is the quotient measure on
`A_G \ G`; `Ξ, σ` are his functions of II.1 and I.1; `φ ∈ °C(G)`; for each `χ ∈ Â_G`, `p χ`
is "irreducible, square integrable modulo `A_G`, with central character `χ`" inside a
representation `ρ χ` built from coefficients; `hS` is `ω(ˇφ) = 0` for `ω ∈ E₂(G)_χ` (together
with their admissibility and tempered coefficients); and `hmem` is the inclusion of Theorem
VIII.4.2.

## Definitions

- `unitaryCharacterOfContinuous χ h1 hc`: the homomorphism `χ : A →* ℂˣ` with
  `|χ(a)| = 1` and `a ↦ χ(a) ∈ ℂ` continuous, as an element of `unitaryCharacters A`. The
  continuity of `χ` into `ℂˣ` (with its units topology) is derived from the continuity of
  `a ↦ χ(a)` and `a ↦ χ(a)⁻¹`.
- `Space.centralProjectionFamily hw : Space Ξ σ →ₗ[ℂ] (unitaryCharacters A → G → ℂ)`:
  `f ↦ (χ ↦ p_χ f)`, the linear map `LinearMap.pi` of the published `Space.centralProjection`
  over all `χ ∈ unitaryCharacters A` (for `A = A_G`, all `χ ∈ Â_G`). This is Waldspurger's
  family of projections `p_χ` (VIII.4) applied to one `f ∈ C(G)`.

## Results

- `unitaryCharacterOfContinuous_apply`: `unitaryCharacterOfContinuous χ h1 hc a = χ a`.
- `isUnitaryCharacter_of_mem_unitaryCharacters`: every `χ ∈ unitaryCharacters A` satisfies the
  published `IsUnitaryCharacter` (absolute value one and measurable), so `p_χ` of
  `CentralProjection` is defined for it.
- `Space.centralProjectionFamily_apply`: the `χ`-component is
  `centralProjection μA χ f`.
- `Space.centralProjectionFamily_injective` (**Fourier inversion on `A_G`**, indexed by `Â_G`):
  `f ↦ (p_χ f)_{χ ∈ Â_G}` is injective on `C(G)`.
- `Space.eq_zero_of_forall_schwartzAction_eq_zero` (**end of the proof of Theorem VIII.1.1**,
  abstract form): under `hS` and `hmem` for every `χ ∈ Â_G`, `φ = 0`.

## Proof notes

1. `unitaryCharacterOfContinuous`: `Units.continuous_iff` reduces continuity into `ℂˣ` to
   continuity of `a ↦ χ(a)` and `a ↦ χ(a)⁻¹ = (χ(a))⁻¹` (`Units.val_inv_eq_inv_val`); the
   latter is `Continuous.inv₀` since `χ(a) ≠ 0`.
2. `isUnitaryCharacter_of_mem_unitaryCharacters`: the norm condition is the membership
   condition of `unitaryCharacters`; measurability follows from continuity of
   `a ↦ χ(a) ∈ ℂ` (composition with `Units.continuous_val`) and `Continuous.measurable`.
3. `Space.centralProjectionFamily_injective`: by `injective_iff_map_eq_zero` it suffices that
   `p_χ f = 0` for all `χ ∈ unitaryCharacters A` implies `f = 0`. The published
   `eq_zero_of_forall_centralProjection_eq_zero` requires `p_χ f = 0` for every
   `χ : A →* ℂˣ` with `|χ| = 1` and `a ↦ χ(a)` continuous; such a `χ` is
   `unitaryCharacterOfContinuous χ h1 hc`, and the corresponding component of the family is
   `p_χ f` by definition. Then `f = 0` as functions, hence in `Space Ξ σ` (`Space.ext`).
4. `Space.eq_zero_of_forall_schwartzAction_eq_zero`: by step 3 it suffices that every
   component `p_χ φ` vanishes. For `χ ∈ unitaryCharacters A`, the published
   `centralProjection_eq_zero_of_schwartzAction_eq_zero` with the unitary character of step 2,
   `b χ`, `hs χ`, `hS χ` and `hmem χ` gives `p_χ φ = 0`. The instances of step 3 for `μA`
   come from `[μA.IsHaarMeasure]`.

## Relation to the Library

- `CentralFourierInversion` proves Fourier inversion with the characters quantified as
  homomorphisms `A →* ℂˣ` with explicit norm and continuity conditions; this module restates it
  over the Library's subgroup `unitaryCharacters A` of continuous characters, which is the
  indexing set `Â_G` used elsewhere in `Langlands.Plancherel` (for example by
  `unitaryUnramifiedCharacters`).
- `CentralProjectionVanishing` proves the vanishing for one `χ`; no earlier statement combined
  it with Fourier inversion.
- `DiscreteCoefficientSpace` and `CentralCoefficientFormula` are the route to `hmem`
  (Theorem VIII.4.2).

## Open obligations

The hypothesis `hFG` for Waldspurger's `A_G` is not proved in this module (it is the subject
of the separately submitted module `CentralQuotientGeneration`). The existence of Haar measures
on `G` and `A_G` and of the compatible quotient measure on `A_G \ G`, `CentralWeights` and
`L2Weights` for his `Ξ, σ`, the inclusion `hmem` (Theorem VIII.4.2) and the vanishing `hS`
(from Theorem VII.2.5) are also inputs here.
