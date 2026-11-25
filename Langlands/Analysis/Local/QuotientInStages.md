# Quotients in stages for a discrete subgroup of a closed subgroup

Module `Langlands.Analysis.Local.QuotientInStages`, namespace `Langlands.QuotientIntegration`.

For a discrete subgroup `Λ` of a closed subgroup `H` of `G`, the integral of a left `H`-invariant
function over `Λ \ G` is the volume of `(Λ ∩ H) \ H` times its integral over `H \ G`. In the simple
trace formula this turns the integral over `(Γ ∩ C_γ) \ G` produced by the unfolding
(`TwistedGeometricUnfolding`) into `vol((Γ ∩ C_γ) \ C_γ) · TO_γ(f)` (`TwistedGeometricSide`).

## Statements

Common hypotheses: `G` a topological group, Hausdorff, locally compact, second countable, with its
Borel σ-algebra; `H : Subgroup G` with `hH : IsClosed (H : Set G)`, `[MeasurableSpace H] [BorelSpace H]`,
`μH : Measure H` with `[μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]`; `Λ : Subgroup G` with
`[DiscreteTopology Λ]` and `hΛH : Λ ≤ H`; `Λ' : Subgroup H` with
`hΛ' : ∀ x : H, x ∈ Λ' ↔ (x : G) ∈ Λ` (for instance `Λ' = Λ.subgroupOf H`); measurable Borel
structures on `LeftQuotient Λ`, `LeftQuotient H`, `LeftQuotient Λ'`; `μG` finite on compacts;
`hνΛ : IsCompatible Λ μG Measure.count νΛ`, `hνH : IsCompatible H μG μH νH`,
`hνΛ' : IsCompatible Λ' μH Measure.count νΛ'` and `hfin : νΛ' Set.univ ≠ ⊤`.

- `descend_invariant_of_le hΛH hF : ∀ l : Λ, ∀ g, F (l.val * g) = F g` for
  `hF : ∀ h : H, ∀ g, F (h.val * g) = F g` (no topology): the invariance by which `F` descends to
  `Λ \ G`.

- `IsCompatible.isNormalizingFunction_div_measure_univ hH hΛH hΛ' hνΛ' hfin hρ`, for
  `hρ : IsNormalizingFunction Λ Measure.count ρ` (without right invariance of `μH`):

  `IsNormalizingFunction H μH (fun g => ρ g / νΛ' Set.univ)`.

- For `E` a real normed space, second countable with its Borel σ-algebra, and `F : G → E`
  measurable with `hF`:

  `IsCompatible.integrable_descend_iff_of_le hH hΛH hΛ' hνΛ hνH hνΛ' hfin F hFm hF :
    Integrable (descend Λ F (descend_invariant_of_le hΛH hF)) νΛ ↔ Integrable (descend H F hF) νH`,

  `IsCompatible.integral_descend_eq_smul_of_le hH hΛH hΛ' hνΛ hνH hνΛ' hfin F hFm hF :
    ∫ q, descend Λ F (descend_invariant_of_le hΛH hF) q ∂νΛ = (νΛ' Set.univ).toReal • ∫ q, descend H F hF q ∂νH`.

- `IsCompatible.integral_descend_stages hH hΛH hνΛ hνH hνΛH hfin F hFm hF`, for `Λ' = Λ.subgroupOf H`
  with `hνΛH : IsCompatible (Λ.subgroupOf H) μH Measure.count νΛH`, `hfin : νΛH Set.univ ≠ ⊤` and
  `F : G → ℂ` measurable and left `H`-invariant:

  `(Integrable (descend Λ F (descend_invariant_of_le hΛH hF)) νΛ ↔ Integrable (descend H F hF) νH) ∧
    ∫ q, descend Λ F (descend_invariant_of_le hΛH hF) q ∂νΛ =
      ((νΛH Set.univ).toReal : ℂ) * ∫ q, descend H F hF q ∂νH`.

A continuous `F` is measurable, so the statement covers the continuous functions of the twisted
trace formula.

## Proofs

`Λ` is closed (discrete) and countable, the counting measure on it is finite on compacts and
positive on open sets, so `exists_continuous_isNormalizingFunction` gives a normalizing function `ρ`
of `Λ`: `∑' l : Λ, ρ (l g) = 1`. `Λ'` is discrete in `H` (the preimage of `Λ`), hence closed, and `H`
is locally compact and second countable. Weil's formula on `H` for the pair `(μH, count)`
(`IsCompatible.lintegral_eq_lintegral_quotientAverageENNReal`) applied to `h ↦ ρ (h g)` gives

`∫⁻ h, ρ (h g) ∂μH = ∫⁻_{Λ' \ H} ∑' l ∈ Λ', ρ (l h g) dνΛ' = ∫⁻_{Λ' \ H} 1 dνΛ' = νΛ'(univ)`,

because `Λ' ≃ Λ`. As `0 < νΛ'(univ) < ⊤` (`IsCompatible.nonzero`, `hfin`), `ρ / νΛ'(univ)` is a
normalizing function of `H`. The rule of `QuotientNormalizingFunction` writes both sides as integrals
over `G`: `∫_{Λ \ G} F = ∫ ρ F dμG` and `∫_{H \ G} F = νΛ'(univ)⁻¹ ∫ ρ F dμG`, and similarly for
integrability (`integrable_smul_iff`).

## Declarations, in order

- `descend_invariant_of_le`
- `toReal_div_smul` (private)
- `subgroupOfEquiv` (private): `Λ' ≃ Λ`.
- `isDiscrete_of_iff` (private)
- `IsCompatible.isNormalizingFunction_div_measure_univ`
- `IsCompatible.integrable_descend_iff_of_le`
- `IsCompatible.integral_descend_eq_smul_of_le`
- `IsCompatible.integral_descend_stages`

## Literature

- Deligne–Kazhdan–Vignéras, in *Représentations des groupes réductifs sur un corps local* (1984),
  A.1.c, printed p. 44: the integral over `Z*_γ(F) \ G*(𝔸)` is written
  `vol(Z_γ(F) Z(𝔸) \ Z_γ(𝔸)) · ∫_{Z_γ(𝔸) \ G(𝔸)} f(x⁻¹ γ x) dx`, the measures on `Z(𝔸)`, `Z_γ(𝔸)` and
  `Z_γ(𝔸) \ G(𝔸)` being chosen to satisfy the product formula.
- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), §17.8, proof of Theorem 17.8.7,
  printed p. 469: the second equality, `∫_{AH_γ(F) \ H(𝔸_F)} = ∫_{AH_γ(F) \ H_γ(𝔸_F)} · RO_γ(f)`, and
  Definition 17.8.4 and Lemma 17.8.5, printed pp. 465–466, for the volume `τ(H_γ)`.
- G. B. Folland, *A Course in Abstract Harmonic Analysis*, second edition (2015), §2.6, Theorem 2.51
  and formula (2.52), printed p. 62: the quotient formula for one closed subgroup, which is applied
  twice here.
- N. Bourbaki, *Intégration, chapitres 7 et 8* (1963), Chapter VII, §2, no. 8, "Une propriété de
  transitivité", printed pp. 61–64. Setting (p. 61): a locally compact group `H` acts on the right,
  continuously and properly, on a locally compact space `X`; `H'` is a closed subgroup of `H`; `β`,
  `β'` are left Haar measures on `H`, `H'` such that the modular functions `Δ_H` and `Δ_{H'}` agree on
  `H'`, so that the `H`-invariant measure `β/β'` on `H/H'` exists; `μ` is a positive measure on `X`
  with `δ(ξ) μ = Δ_H(ξ) μ` for `ξ ∈ H`. Proposition 12, formula (22), printed p. 63:
  `μ/β' = ∫_{X/H} (β/β')_u d(μ/β)(u)`. Corollary 1, printed p. 64: for `f` on `X/H'` integrable for
  `μ/β'`, `∫_{X/H'} f d(μ/β') = ∫_{X/H} d(μ/β)(ẋ) ∫_{H/H'} f(π'(x ξ)) d(β/β')(ξ̇)` (a)), the same for
  measurable `f ≥ 0` with upper integrals (b)), and finiteness of the right-hand side for `|f|` as a
  sufficient condition of integrability (c)). For `X = G`, `H' = Λ` and `f` induced by an
  `H`-invariant `F`, the inner integral is `F(x) · (β/β')(H/H')`, which gives the theorem here, in the
  mirror image (`H` acting on `G` on the left, cosets `H g`, right-invariant measures). Bourbaki's
  condition on the modular functions does not appear here: the measures `νΛ`, `νH`, `νΛ'` are
  supposed compatible instead, and `Λ` is discrete with the counting measure.

## Source and licence

This file contains no text of the repository `leanprover-community/riemann-hypothesis`. Its main
theorem has the content of that repository's statement `PositivityTheory.Rg.Tf.Geo.U2`
(`src/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/SelmerRankBounds/EllipticityFromProductFormula.lean`,
lines 118–127), proved there as `UpperTheory.ConvolutionTheory.G.unitaryGroupGeometricSide_of_quotient_identities`
(`src/Development/AutomorphicArithmetic/Foundations/Convolution/LocalGroupAnalysis/UnitaryGroupGeometricSideOfQuotientIdentities.lean`)
by comparing measurable fundamental domains of `Λ` and `Γ₀ = i(Λ)` and its integral `quotInt` defined
by choice. The proof here is new: it uses compatible quotient measures and normalizing functions only.
