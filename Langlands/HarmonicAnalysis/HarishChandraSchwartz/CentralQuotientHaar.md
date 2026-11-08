# Compatible measures on `A \ G` and Haar measures on `G ⧸ A` for central `A`

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralQuotientHaar`, namespace
`Langlands.QuotientIntegration`. It imports
`Langlands.Analysis.Local.NormalSubgroupHaarModulus` and uses, from it and its imports:
`normalLeftQuotientHomeomorph` and `normalLeftQuotientHomeomorph_mk` (the identification of
`A \ G` with the quotient group `G ⧸ A` for normal `A`), `IsCompatible` (`QuotientMeasure`),
`IsCompatible.integral_quotientAverageReal` (`QuotientAutomorphismProof`),
`realQuotientPositiveLifting` (`QuotientPositiveLifting`), `quotientAverageReal` and
`quotientAverageReal_mk` (`QuotientAverageReal`), `leftQuotient_t2Space` and
`leftQuotient_locallyCompactSpace` (`QuotientTopology`); from Mathlib
`Measure.ext_of_integral_eq_on_compactlySupported`, `isMulLeftInvariant_eq_smul` (uniqueness of
Haar measure), `MeasurableEquiv.memLp_map_measure_iff`, `MemLp.smul_measure` and
`integral_mul_left_eq_self`.

## Provenance

Derived. J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`), integrates over `A_G \ G`:

- III.1, printed p. 263 (PDF p. 29): "On dit que `π` est de carré intégrable si tous les
  coefficients de `π` sont de carré intégrable sur `A_G \ G`."
- Proof of Theorem VIII.4.2, printed p. 331 (PDF p. 97): "`(f₁, ρ(g)f₂)_{A_G\G} =
  (p_χ(\check{\bar φ}₁ ∗ φ₂))(g)`. (2) En particulier cette fonction est de carré intégrable sur
  `A_G \ G`. Donc toute sous-représentation irréductible de `(ρ, V)` est de carré intégrable."

The Library writes integrals over `A \ G` for a measure `ν` compatible with the measures of `G`
and `A` (`IsCompatible`, read through representatives in `KernelQuotient`), while
`DiscreteCoefficientSpace` and `IsSquareIntegrableModCentralSubgroup` use the quotient group
`G ⧸ A` with an arbitrary Haar measure. The source does not distinguish the two (for central
`A_G` the quotient `A_G \ G` is a group and its measures are Haar measures). This module
supplies the comparison; the statements and proofs are internal to this project.

## Contents

Section `Packaging` (a group `G` with `[TopologicalSpace G] [IsTopologicalGroup G]`):

- `quotientLeftTranslate A h` (definition), for a normal subgroup `A` (`[A.Normal]`) and
  `h : G`: the homeomorphism of `LeftQuotient A` sending the class of `g` to the class of `h g`.
- `quotientLeftTranslate_mk`: its value on `Quotient.mk _ g` is `Quotient.mk _ (h * g)`.

Section `Measure`: `G` moreover `[T2Space G] [LocallyCompactSpace G] [MeasurableSpace G]
[BorelSpace G]`; a subgroup `A` with `hA : IsClosed (A : Set G)`, `[A.Normal]`,
`hAc : A ≤ Subgroup.center G`, `[MeasurableSpace A] [BorelSpace A]`; a measure `μG` with
`[μG.IsMulLeftInvariant]`; `μA` with `[IsHaarMeasure μA] [μA.Regular] [IsMulRightInvariant μA]`;
`[MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]` and
`ν : Measure (LeftQuotient A)` (the Borel structure on `LeftQuotient A` is not used by the
first result).

- `IsCompatible.integral_comp_quotientLeftTranslate hA hAc`: for `hν : IsCompatible A μG μA ν`,
  `h : G` and a compactly supported continuous `φ : LeftQuotient A → ℝ`,
  `∫ q, φ (quotientLeftTranslate A h q) ∂ν = ∫ q, φ q ∂ν`.
- `IsCompatible.map_quotientLeftTranslate hA hAc`: `Measure.map (quotientLeftTranslate A h) ν = ν`.

With moreover `[MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]`:

- `IsCompatible.isMulLeftInvariant_map_normalLeftQuotientHomeomorph hA hAc`: the image
  `Measure.map (normalLeftQuotientHomeomorph A) ν` on `G ⧸ A` is left invariant.
- `IsCompatible.exists_smul_eq_map hA hAc`: for `[SecondCountableTopology G]`, `hν` and a Haar
  measure `μ` on `G ⧸ A` (`[μ.IsHaarMeasure]`), there is `c : ℝ≥0` with `c ≠ 0` and
  `Measure.map (normalLeftQuotientHomeomorph A) ν = c • μ`.
- `IsCompatible.memLp_of_memLp_comp hA hAc`: for `[SecondCountableTopology G]`, `hν`, a Haar
  `μ` on `G ⧸ A`, a normed group `E`, `F : G ⧸ A → E`, `p : ℝ≥0∞` and
  `hF : MemLp (fun q => F (normalLeftQuotientHomeomorph A q)) p ν`: `MemLp F p μ`.
- `IsCompatible.exists_memLp_quotientGroup hA hAc`: for `[SecondCountableTopology G]`, `hν`, a
  Haar `μ` on `G ⧸ A`, a normed group `E`, `F₀ : LeftQuotient A → E` and `p` with
  `hF₀ : MemLp F₀ p ν`: there is `F : G ⧸ A → E` with `MemLp F p μ` and
  `F (g : G ⧸ A) = F₀ (Quotient.mk _ g)` for every `g : G`.

With `F₀` the descent to `A \ G` of the absolute value of a coefficient (for Waldspurger, of
`|p_χ(\check{\bar φ}₁ ∗ φ₂)|`), the conclusion of the last result has the form of the
hypothesis `hL2` of `DiscreteCoefficientSpace`; the square integrability of `F₀` itself is not
proved here.

## Proof

`integral_comp_quotientLeftTranslate`: write `φ` as the average `q ↦ ∫_A f(a q)` of a compactly
supported continuous `f` on `G` (`realQuotientPositiveLifting`). Since `A` is central,
`φ(A h g) = ∫_A f(a h g) da = ∫_A f(h a g) da`, the average of `x ↦ f(h x)`. The Weil formula
for compactly supported continuous functions (`IsCompatible.integral_quotientAverageReal`) and
the left invariance of `μ_G` give
`∫ φ(A h ·) dν = ∫_G f(h x) dμ_G(x) = ∫_G f dμ_G = ∫ φ dν`.

`map_quotientLeftTranslate`: both measures are regular (`ν` by compatibility, its image by a
homeomorphism), and they agree on compactly supported continuous real functions by the previous
result (`integral_map_equiv`); `Measure.ext_of_integral_eq_on_compactlySupported` concludes.

`isMulLeftInvariant_map_normalLeftQuotientHomeomorph`: left multiplication by the class of `h` on
`G ⧸ A` corresponds to `quotientLeftTranslate A h` under `normalLeftQuotientHomeomorph A`.

`exists_smul_eq_map`: the image of `ν` is left invariant and finite on compact sets (regular),
so it is `haarScalarFactor • μ` (`isMulLeftInvariant_eq_smul`, `G ⧸ A` being second countable and
locally compact); the factor is nonzero because `ν ≠ 0` (`IsCompatible.nonzero`).

`memLp_of_memLp_comp`: `MemLp` passes to the image measure through the measurable equivalence
(`MeasurableEquiv.memLp_map_measure_iff`) and to `μ = c⁻¹ • (image of ν)` by
`MemLp.smul_measure`.

`exists_memLp_quotientGroup`: take `F = F₀ ∘ (normalLeftQuotientHomeomorph A)⁻¹`.
