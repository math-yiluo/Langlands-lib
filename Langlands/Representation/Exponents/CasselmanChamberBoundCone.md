# Positive root cones and strict bounds on the closed restricted-root chamber

Author: Worker 4712. Module
`Langlands.Representation.Exponents.CasselmanChamberBoundCone`. Its one new
definition is `Langlands.GroupScheme.ParabolicRootPresentation.latticePair`, the
pairing of a real character with integral cocharacters; the remaining
declarations are theorems about it and about normalized exponents.

This supporting unit proves the last step of the proof of Casselman's criterion,
Renard 2026, VII.1.2 (printed p.224 / PDF p.230): from strict bounds
`|χ(t)| < 1` at the split-component points of the closed chamber, "en utilisant
V.3.21, on retrouve la condition de l'énoncé". In the formulation of the
published `ArbitraryParabolicCasselmanCriterionStatement` that condition is
membership of the `q^(-s)` real part in the strictly positive root cone
`pres.positiveCone`. The unit proves this conversion, and its converse, for every
normalized exponent of a representation with a unitary central character. It does
not prove either analytic implication of the criterion.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`. PDF page numbers equal
printed page numbers plus six. V.3.21 (printed p.116 / PDF p.122) defines the closed
chamber `A_M^+ = {a ∈ A_M | v_F(α(a)) ≥ 0, α ∈ Δ(P)}` used below; V.3.14–V.3.15
(printed p.113 / PDF p.119) define `Δ(P)` and the root cone.

## Main results

`Langlands.Aubert.General.RepresentedParabolic.normalizedRealPart_mem_positiveCone_iff_norm_lt_one`
fixes a nonarchimedean local field `k` (Hausdorff), a connected reductive `G` over
`k` with local finite type, the canonical topology on `rationalPoints G` assumed
locally compact and nonarchimedean, an actual represented parabolic `p : P ⟶ G`
with rational Levi `l`, geometric unipotent radical `r`, multiplication
isomorphism and split component `a : A.toGrp ⟶ M`, a compatible presentation
`pres : ParabolicRootPresentation p l a`, a smooth complex representation `π` with
a `UnitaryCentralCharacter`, and a normalized Jacquet exponent `χ`. Write
`v(t) = (Plancherel.SplitTorus.valuation _ t).toAdd` for the valuation of
`t ∈ A(k)` in the real cocharacter space. Then

```text
normalizedRealPart χ ∈ pres.positiveCone  ↔
  ∀ t : A(k), (∀ β ∈ pres.restrictedRoots, 0 ≤ ⟨β, v(t)⟩) →
              (∃ β ∈ pres.restrictedRoots, 0 < ⟨β, v(t)⟩) → ‖χ t‖ < 1.
```

The right side quantifies over the points of `A_M^+` with at least one strict
inequality, that is, `A_M^+` with the central directions removed. Neither
admissibility nor irreducibility of `π` is assumed, and the field and carrier
universes are independent.

The reverse implication is the separately stated
`normalizedRealPart_mem_positiveCone_of_norm_lt_one`. The forward implication is
the published `norm_lt_one_of_normalizedRealPart_mem_positiveCone`
(`CasselmanConeNormBounds`); it needs no unitary central character.

## Presentation-level algebra

These results are in namespace `Langlands.GroupScheme.ParabolicRootPresentation`,
for any compatible presentation `r` of maps `p, l, a` into an affine `G` over an
arbitrary field. Write `Δ` for the simple relative roots of the presentation's
torus `T` and generic cocharacter, `J ⊆ Δ` for the selected roots and `f : A ⟶ T`
for the factor map.

- `latticePair y` is the additive map `m ↦ pair A y (1 ⊗ m)` on integral
  cocharacters. `latticePair_restrictedRootVector` evaluates it on a restricted
  root as the integer pairing `⟨f ≫ α, m⟩`.
  `eq_zero_of_latticePair_eq_zero` shows that a real character of a split torus
  vanishing on all integral cocharacters is zero: the published
  `characterDualEquiv` identifies `Vstar A` with the dual of `V A`, and `V A` is
  spanned by the pure tensors `t ⊗ m = t • (1 ⊗ m)`.
- `exists_lift_of_selected_pairing_eq_zero`: assuming rational independence of `Δ`
  and local finite type, every cocharacter `ζ` of `T` vanishing on `J` lifts
  integrally through `f`. The published `exists_scaled_pairings` gives a
  cocharacter `ξ` with pairing `d > 0` on `Δ \ J` and `0` on `J`. With
  `N = ∑_{α ∈ Δ} |⟨α, ζ⟩| + 1`, both `N • ξ` and `ζ + N • ξ` are standard for `J`,
  so both lift by the published `exists_standardCocharacter_lift`; their
  difference lifts `ζ`.
- `exists_dual_cocharacters`: under the same assumptions there are `D > 0` and
  component cocharacters `ν α` with `⟨f ≫ β, ν α⟩ = D` if `β = α` and `0`
  otherwise, for all `α, β ∈ Δ \ J`. For each `α`, `exists_scaled_pairings`
  supplies a cocharacter `ζ_α` of `T` with pairings `d_α δ_{αβ}` on `Δ`; it vanishes
  on `J` because `α ∉ J`. Rescaling by `D / d_α` with `D = ∏ d_α` gives a common
  factor, and the previous lemma lifts the result.
- `mem_positiveCone_of_latticePair` is the cone criterion. Let `x ∈ Vstar A`.
  Assume `latticePair x m = 0` for every `m` with `⟨f ≫ α, m⟩ = 0` for all
  `α ∈ Δ \ J`, and `latticePair x m > 0` for every `m` with all these pairings
  nonnegative and one positive. Then `x ∈ r.positiveCone`. The proof sets
  `c α = latticePair x (ν α) / D`, positive by the second hypothesis applied to
  `ν α`, and shows that `y = x - ∑_{α ∈ Δ \ J} c α • (1 ⊗ (f ≫ α))` vanishes. Indeed
  `latticePair y (ν α) = 0` by the choice of `c`; for any `m`, the cocharacter
  `m' = D • m - ∑_α ⟨f ≫ α, m⟩ • ν α` is orthogonal to `Δ \ J`, so
  `latticePair y m' = 0` by the first hypothesis; and `D • m` is `m'` plus a
  combination of the `ν α`. Hence `D · latticePair y m = 0` for every `m`, and
  `y = 0`. The published `mem_restrictedRootPositiveCone_iff_roots` then gives
  membership, indexing the coefficients by the simple roots outside `J`.
- `linearIndependent_simpleRoots`: for a connected reductive `G`, `Δ` is
  rationally independent. This combines the published proof `standardCocharacter`
  of `StandardCocharacterStatement`,
  `linearIndependent_simpleRelativeRoots_of_standardCocharacter_exists` and flat
  base change to `ℚ`.
- `isCentral_of_pairing_eq_zero`: for a connected reductive `G`, a component
  cocharacter `m` orthogonal to `Δ \ J` has central image
  `CommGroupScheme.groupHom m ≫ a ≫ l ≫ p`. Its image `f ∘ m` in `T` pairs to zero
  with `J` (published `selectedRoot_restrict_eq_zero`) and with `Δ \ J`, hence with
  all positive roots (`positiveRelativeRoots_induction`) and, by genericity and the
  published `relativeRootNegation`, with all relative roots. The published
  `rootAnnihilatorCentrality` gives centrality, transported along the
  presentation's `factor_comp`.

## Proof of the exponent results

`normalizedRealPart_mem_positiveCone_of_norm_lt_one` applies
`mem_positiveCone_of_latticePair` to `x = normalizedRealPart χ`.

- Central directions: for `m` orthogonal to `Δ \ J`, `isCentral_of_pairing_eq_zero`
  and the published `normalizedJacquetExponent_realPart_restrict_eq_zero`
  (`CasselmanCentralDirections`, applied to the split torus `𝔾_m` and the morphism
  `m`) give zero restricted real part. Naturality `pair_cocharacterMapReal`, with
  `m` the image of the identity cocharacter of `𝔾_m`, gives
  `latticePair x m = 0`. This is where the unitary central character is used.
- Chamber directions: for `m` in the closed chamber with one positive pairing,
  the test point is the uniformizer point
  `t = CocharacterUniformizer.latticeSection k A (ofAdd m)`, whose valuation is
  `1 ⊗ m` by `valuation_latticeSection`. Its restricted-root pairings are the
  integers `⟨f ≫ α, m⟩`, so the hypothesis gives `‖χ t‖ < 1`. The published
  all-point formula `norm_eq_rpow_normalizedRealPart` writes
  `‖χ t‖ = q ^ (-latticePair x m)` with `q > 1`, using the exponent's open kernel;
  hence `latticePair x m > 0`.

The iff theorem combines this with `norm_lt_one_of_normalizedRealPart_mem_positiveCone`.

## Scope and provenance

This is a derived formulation of the final step of the proof of Renard VII.1.2
together with V.3.21, for the published represented-parabolic interface and its
`q^(-s)` normalization. Renard tests the specific points `t_{α_i}` of a basis with
`|α(t_α)| < 1` and `|β(t_α)| = 1` for `β ≠ α`; the unit tests all points of the
closed chamber with a positive valuation, which includes points of that type (the
uniformizer points of the dual cocharacters `ν α`). Under a unitary central
character the root cone and the coroot chamber condition of the printed theorem
differ, as explained in the statement Markdown `ArbitraryParabolicCasselmanStatement.md`;
this unit concerns only the root cone `pres.positiveCone`.

Nothing here constructs presentations, Iwahori decompositions, power-cell volumes
or Casselman's asymptotics. The analytic implications of the criterion remain
separate obligations.
