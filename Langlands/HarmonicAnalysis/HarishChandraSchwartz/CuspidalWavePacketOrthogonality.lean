import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedConstantTermFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketPairing

/-! # Functions with vanishing constant term are orthogonal to wave packets

Waldspurger, proof of Lemma VIII.2.3 (printed p. 322): for a cuspidal `f ∈ °C(G)` and a proper
`P`, `f̂(ω, P) = 0` for every `ω` (via Lemma VIII.2.1, whose easy direction is Lemma VII.1.2), so
`(f, f_ψ)_G = ∫_O µ(ω) (f̂(ω, P), ψ_ω) dω = 0` for every wave packet `f_ψ`, `ψ ∈ C^∞(O, P)`.

* `ConstantTermIndVanishes`: the condition `f^{(P),Ind} = 0` of Lemma VIII.2.1 for one `P`.
* `constantTermInducedFourierTransform_eq_zero`: `f̂^{(P),Ind}(ω) = 0` when `f^{(P),Ind} = 0`.
* `inducedFourierTransform_eq_zero_of_constantTermInd_eq_zero`: `f̂(ω, P) = 0` when
  `f^{(P),Ind} = 0` (with Lemma VII.1.2).
* `fourierOrbitSection_eq_zero_of_constantTermInd_eq_zero`: `ψ_f[O, P] = 0`.
* `pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero`: `(f_ψ, f)_G = 0`.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped ComplexConjugate NNReal ENNReal TensorProduct

namespace Langlands.HarishChandraSchwartz

universe uG uV uI uJ

section Vanishing

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)] {M U : Subgroup G}
  {ν : Measure U} {δ : M →* ℝ≥0ˣ} {Ξ σ : G → ℝ} {ΞM σM : M → ℝ}
  (hD : ConstantTermData ν δ) (hE : ConstantTermEstimate ν δ Ξ σ ΞM σM)
  (ht : TranslationWeights Ξ σ) (htM : TranslationWeights ΞM σM)

/-- **Vanishing constant term along `P`**: `f^{(P),Ind}(g₁, g₂) = (ρ(g₁)λ(g₂)f)^{(P)} = 0` for
all `(g₁, g₂) ∈ G × G` (the condition of Waldspurger's Lemma VIII.2.1, for one parabolic
subgroup `P`). -/
def ConstantTermIndVanishes (f : Space Ξ σ) : Prop :=
  ∀ x : G × G, Space.constantTermInd hD hE ht htM f x = 0

end Vanishing

section Definition

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδU : IsUnimodularModulus U hU) (A : SmoothRep.{0, uG, uV} ℂ M)
  [Nonempty (CompactOpenSubgroup M)]
  {μL : Measure M} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] {ΞM σM : M → ℝ}
  (hwM : L2Weights μL ΞM σM) (hA : IsAdmissible A.representation)
  (hTM : HasTemperedCoefficients ΞM σM A.representation)
  (hΞM : ∀ m, ΞM m⁻¹ = ΞM m) (hσM : ∀ m, σM m⁻¹ = σM m) (d : ℝ)
  {ν : Measure U} [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (hD : ConstantTermData ν (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
  (hν : IsConjModulus h.levi_le_normalizer ν
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
  (hE : ConstantTermEstimate ν (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer)
    Ξ σ ΞM σM)
  (ht : TranslationWeights Ξ σ) (htM : TranslationWeights ΞM σM)

/-- `f̂^{(P),Ind}(ω) = 0` when the constant term `f^{(P),Ind}(g₁, g₂)` vanishes for all
`(g₁, g₂)`. -/
theorem constantTermInducedFourierTransform_eq_zero (f : Space Ξ σ)
    (h0 : ConstantTermIndVanishes hD hE ht htM f) :
    constantTermInducedFourierTransform h hU hδU A hwM hA hTM hΞM hσM d hD hν hE ht htM f = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change coefficientFourierTransform A hwM hA hTM hΞM hσM d
    (Space.constantTermInd hD hE ht htM f x) = 0
  rw [h0 x, map_zero]

end Definition

section Main

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (A : SmoothRep.{0, uG, uV} ℂ M) (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μM : Measure (M ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM)
  (hi : A.representation.IsIrreducible)
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (hw : L2Weights μ Ξ σ)
  (hT : HasTemperedCoefficients Ξ σ ((normalizedInductionFunctor h hU).obj A).representation)
  (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)
  (hδU : IsUnimodularModulus U hU) [Nonempty (CompactOpenSubgroup M)]
  {μL : Measure M} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] {ΞM σM : M → ℝ}
  (hwM : L2Weights μL ΞM σM) (hTM : HasTemperedCoefficients ΞM σM A.representation)
  (hΞM : ∀ m, ΞM m⁻¹ = ΞM m) (hσM : ∀ m, σM m⁻¹ = σM m)
  {ν : Measure U} [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
  (hD : ConstantTermData ν (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
  (hν : IsConjModulus h.levi_le_normalizer ν
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
  (hE : ConstantTermEstimate ν (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer)
    Ξ σ ΞM σM)
  (ht : TranslationWeights Ξ σ) (htM : TranslationWeights ΞM σM)

include hδU hwM hTM hΞM hσM hν in
/-- **`f̂(ω, P) = 0` for `f` with vanishing constant term along `P`** (Lemma VII.1.2 and the
easy direction of Lemma VIII.2.1 of Waldspurger): under the hypotheses of
`inducedFourierTransform_eq_constantTermInducedFourierTransform`, if
`f^{(P),Ind}(g₁, g₂) = 0` for all `(g₁, g₂)`, then `f̂(ω, P) = 0`. -/
theorem inducedFourierTransform_eq_zero_of_constantTermInd_eq_zero
    [MeasurableInv G] [μ.IsInvInvariant] [SigmaFinite μ] (hμK : μ (K : Set G) = 1)
    [MeasurableInv M] [μL.IsInvInvariant] [SFinite μL] [SFinite ν]
    (hPKiw : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μL {m : M | (m : G) ∈ K} = 1) (hUK : ν {u : U | (u : G) ∈ K} = 1)
    (f : Space Ξ σ)
    (hint : ∀ ψ : productInducedCoefficientObject h hU A,
      Integrable (fun x : G × K => conj (CompactInduction.integrand h hU A K x.1 ψ x.2) * f x.1)
        (μ.prod (CompactInduction.measure K hK)))
    (h0 : ConstantTermIndVanishes hD hE ht htM f) :
    inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ f = 0 := by
  rw [inducedFourierTransform_eq_constantTermInducedFourierTransform h hU hP hm K hK hPK hG hδ A
    hcof C hC μM hsq hi hw hT hΞ hσ hδU hwM hTM hΞM hσM hD hν hE ht htM hμK hPKiw hMK hUK f hint]
  exact constantTermInducedFourierTransform_eq_zero h hU hδU A hwM hsq.1 hTM hΞM hσM _ hD hν hE
    ht htM f h0

end Main

section Orbit

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M)) (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μM : Measure (M ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : ∀ A : UnitaryOrbitRepresentative ν π,
    IsSquareIntegrableModCentralSubgroup C hC A.val.obj.representation μM)
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (hw : L2Weights μ Ξ σ)
  (hT : ∀ A : UnitaryOrbitRepresentative ν π,
    HasTemperedCoefficients Ξ σ ((normalizedInductionFunctor h hU).obj A.val.obj).representation)
  (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)
  (hδU : IsUnimodularModulus U hU) [Nonempty (CompactOpenSubgroup M)]
  {μL : Measure M} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] {ΞM σM : M → ℝ}
  (hwM : L2Weights μL ΞM σM)
  (hTM : ∀ A : UnitaryOrbitRepresentative ν π,
    HasTemperedCoefficients ΞM σM A.val.obj.representation)
  (hΞM : ∀ m, ΞM m⁻¹ = ΞM m) (hσM : ∀ m, σM m⁻¹ = σM m)
  {νU : Measure U} [νU.IsMulLeftInvariant] [νU.IsMulRightInvariant]
  (hD : ConstantTermData νU (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
  (hνU : IsConjModulus h.levi_le_normalizer νU
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
  (hE : ConstantTermEstimate νU (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer)
    Ξ σ ΞM σM)
  (ht : TranslationWeights Ξ σ) (htM : TranslationWeights ΞM σM)

include hδU hwM hTM hΞM hσM hνU in
/-- **`ψ_f[O, P] = 0` for `f` with vanishing constant term along `P`**: under the hypotheses of
Lemma VII.1.2 at every representative of the orbit, if `f^{(P),Ind} = 0` then the section
`ω ↦ f̂(ω, P)` vanishes. -/
theorem fourierOrbitSection_eq_zero_of_constantTermInd_eq_zero
    [MeasurableInv G] [μ.IsInvInvariant] [SigmaFinite μ] (hμK : μ (K : Set G) = 1)
    [MeasurableInv M] [μL.IsInvInvariant] [SFinite μL] [SFinite νU]
    (hPKiw : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μL {m : M | (m : G) ∈ K} = 1) (hUK : νU {u : U | (u : G) ∈ K} = 1)
    (f : Space Ξ σ)
    (hint : ∀ (A : UnitaryOrbitRepresentative ν π)
      (ψ : productInducedCoefficientObject h hU A.val.obj),
      Integrable (fun x : G × K =>
          conj (CompactInduction.integrand h hU A.val.obj K x.1 ψ x.2) * f x.1)
        (μ.prod (CompactInduction.measure K hK)))
    (h0 : ConstantTermIndVanishes hD hE ht htM f) :
    fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f = 0 := by
  funext A
  rw [fourierOrbitSection_apply]
  exact inducedFourierTransform_eq_zero_of_constantTermInd_eq_zero h hU hP hm K hK hPK hG hδ
    A.val.obj hcof C hC μM (hsq A) A.val.property.1 hw (hT A) hΞ hσ hδU hwM (hTM A) hΞM hσM hD
    hνU hE ht htM hμK hPKiw hMK hUK f (hint A) h0

end Orbit

section Pairing

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)]
  (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)] (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)
  [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))]
  (ρ : Measure (unitaryUnramifiedCharacters ν))
  (w : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq) → ℂ)
  (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
  {μG : Measure G} [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [MeasurableInv G]
  [μG.IsInvInvariant] {σ : G → ℝ} (hwt : L2Weights μG (xi hP₀K δ₀) σ)
  (hT : ∀ A : UnitaryOrbitRepresentative ν π, HasTemperedCoefficients (xi hP₀K δ₀) σ
    ((normalizedInductionFunctor h hU).obj A.val.obj).representation)
  (hΞ : ∀ g, xi hP₀K δ₀ g⁻¹ = xi hP₀K δ₀ g) (hσ : ∀ g, σ g⁻¹ = σ g)

include hcof hwt hT hΞ hσ in
/-- **Wave packets are orthogonal to functions with vanishing constant term** (Waldspurger,
proof of Lemma VIII.2.3, for one orbit `O` and one parabolic `P`): under the hypotheses of
`pairing_inducedOrbitWavePacket_eq_zero` and of Lemma VII.1.2 at every representative of the
orbit, if `f^{(P),Ind}(g₁, g₂) = 0` for all `(g₁, g₂)`, then `(f_ψ, f)_G = 0` for every wave
packet `f_ψ` on the orbit. -/
theorem pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero
    [SigmaFinite μG] [IsFiniteMeasure ρ]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ))
    {b : ℝ} (hwb : ∀ ω, ‖w ω‖ ≤ b)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    [Nonempty (CompactOpenSubgroup M)]
    {μL : Measure M} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] {ΞM σM : M → ℝ}
    (hwM : L2Weights μL ΞM σM)
    (hTM : ∀ A : UnitaryOrbitRepresentative ν π,
      HasTemperedCoefficients ΞM σM A.val.obj.representation)
    (hΞM : ∀ m, ΞM m⁻¹ = ΞM m) (hσM : ∀ m, σM m⁻¹ = σM m)
    {νU : Measure U} [νU.IsMulLeftInvariant] [νU.IsMulRightInvariant]
    (hD : ConstantTermData νU (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
    (hνU : IsConjModulus h.levi_le_normalizer νU
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
    (hE : ConstantTermEstimate νU
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) (xi hP₀K δ₀) σ ΞM σM)
    (ht : TranslationWeights (xi hP₀K δ₀) σ) (htM : TranslationWeights ΞM σM)
    (hμK : μG (K : Set G) = 1) [MeasurableInv M] [μL.IsInvInvariant] [SFinite μL]
    [SFinite νU]
    (hPKiw : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMKμ : μL {m : M | (m : G) ∈ K} = 1) (hUK : νU {u : U | (u : G) ∈ K} = 1)
    (f : Space (xi hP₀K δ₀) σ)
    (hint : ∀ (A : UnitaryOrbitRepresentative ν π)
      (ψ : productInducedCoefficientObject h hU A.val.obj),
      Integrable (fun x : G × K =>
          conj (CompactInduction.integrand h hU A.val.obj K x.1 ψ x.2) * f x.1)
        (μG.prod (CompactInduction.measure K hK)))
    (h0 : ConstantTermIndVanishes hD hE ht htM f) :
    pairing μG (inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q) f =
      0 :=
  pairing_inducedOrbitWavePacket_eq_zero h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC μ hsq ρ w
    hP₀K hwt hT hΞ hσ hLaurent he hwm hwb hδU hL hMK hδ₀ hcoeff q f
    (fourierOrbitSection_eq_zero_of_constantTermInd_eq_zero h hU hP hr K hK
      (factorization_mem_of_subtype hPK) hG hδ ν π hcof C hC μ
      (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq) hwt hT hΞ hσ hδU hwM hTM hΞM
      hσM hD hνU hE ht htM hμK hPKiw hMKμ hUK f hint h0)

end Pairing

end Langlands.HarishChandraSchwartz
