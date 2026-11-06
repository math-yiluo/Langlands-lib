import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierOrbitSmoothness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LaurentExponent

/-! # Proposition VII.1.3 with the lattice map of Laurent coordinates

`FourierOrbitSmoothness` proves that `ψ_f[O, P]` lies in `C^∞(O, P)` (Waldspurger, Proposition
VII.1.3) for torus coordinates `e` on the unitary unramified characters of `M` and a supplied
lattice map `n` with `χ_z(m) = ∏ⱼ zⱼ^{n(m)ⱼ}`. When `e` satisfies Worker 200's Laurent condition
`HasLaurentUnitaryCoordinates ν e`, the lattice map `laurentExponent ν e he` of `LaurentExponent`
satisfies all hypotheses on `n` except the growth bound `‖n(m)‖ ≤ C (1 + σ_M(m))`. This module
states Proposition VII.1.3 in that form.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel
open Langlands.HarmonicAnalysis.TorusFourier
open scoped ComplexConjugate NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uV uI

/-- For continuous norm characters the common norm kernel contains every compact open subgroup,
so it is open when a compact open subgroup exists. -/
theorem isOpen_commonNormKernel_of_continuous {M : Type*} [Group M] [TopologicalSpace M]
    [IsTopologicalGroup M] [Nonempty (CompactOpenSubgroup M)] {I : Type*}
    (ν : I → (M →* ℝ≥0ˣ)) (hνc : ∀ i, Continuous (ν i)) :
    IsOpen (commonNormKernel ν : Set M) := by
  let K₀ : CompactOpenSubgroup M := Classical.arbitrary _
  refine Subgroup.isOpen_mono (H₁ := K₀.toSubgroup) (fun k hk => ?_) K₀.1.isOpen
  exact (mem_commonNormKernel ν k).mpr fun i =>
    RankinSelberg.LastRowReduction.eq_one_of_isCompact (ν i) (hνc i) _ K₀.2 hk

section Smooth

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

set_option maxHeartbeats 1000000 in
/-- **Proposition VII.1.3, smoothness, with Laurent coordinates**: if the torus coordinates `e`
satisfy `HasLaurentUnitaryCoordinates ν e` and the lattice map `laurentExponent ν e he` satisfies
the growth bound `hnσ`, then `ψ_f[O, P]` lies in `C^∞(O, P)`. -/
theorem fourierOrbitSection_mem_smooth_of_hasLaurent {J : Type*} [Fintype J]
    (e : unitaryUnramifiedCharacters ν ≃* (J → Circle)) (hνc : ∀ i, Continuous (ν i))
    (hPK' : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
    (hsqπ : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μM)
    [MeasurableInv G] [μ.IsInvInvariant] [SigmaFinite μ] (hμK : μ (K : Set G) = 1)
    (hδU : IsUnimodularModulus U hU) [Nonempty (CompactOpenSubgroup M)]
    {μL : Measure M} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] [MeasurableInv M]
    [μL.IsInvInvariant] [SFinite μL] {ΞM σM : M → ℝ} (hwM : L2Weights μL ΞM σM)
    (hTπ : HasTemperedCoefficients ΞM σM π.obj.representation)
    (hTM : ∀ A : UnitaryOrbitRepresentative ν π,
      HasTemperedCoefficients ΞM σM A.val.obj.representation)
    (hΞM : ∀ m, ΞM m⁻¹ = ΞM m) (hσM : ∀ m, σM m⁻¹ = σM m)
    {νU : Measure U} [νU.IsMulLeftInvariant] [νU.IsMulRightInvariant] [SFinite νU]
    (hD : ConstantTermData νU (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
    (hνU : IsConjModulus h.levi_le_normalizer νU
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
    (hE : ConstantTermEstimate νU
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) Ξ σ ΞM σM)
    (ht : TranslationWeights Ξ σ) (htM : TranslationWeights ΞM σM)
    (hPKiw : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μL {m : M | (m : G) ∈ K} = 1) (hUK : νU {u : U | (u : G) ∈ K} = 1)
    (he : HasLaurentUnitaryCoordinates ν e) {Cn : ℝ}
    (hnσ : ∀ m, ‖laurentExponent ν e he m‖ ≤ Cn * (1 + σM m))
    (f : Space Ξ σ)
    (hint : ∀ (A : UnitaryOrbitRepresentative ν π)
      (ψ : productInducedCoefficientObject h hU A.val.obj),
      Integrable
        (fun x : G × K => conj (CompactInduction.integrand h hU A.val.obj K x.1 ψ x.2) * f x.1)
        (μ.prod (CompactInduction.measure K hK))) :
    fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f ∈
      productInducedSmoothOrbitSections ν π e h hU K hP hK hνc hm hPK' :=
  fourierOrbitSection_mem_smooth h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ
    e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK
    (laurentExponent_mul ν e he) (K₀ := Classical.arbitrary (CompactOpenSubgroup M))
    (fun _ hk => laurentExponent_eq_zero_of_isCompact ν e he hνc
      (Classical.arbitrary (CompactOpenSubgroup M)).2 hk)
    (measurable_laurentExponent ν e he (isOpen_commonNormKernel_of_continuous ν hνc)) hnσ
    (fun z m => (torusCharacter_laurentExponent ν e he m z).symm) f hint

set_option maxHeartbeats 1000000 in
/-- The linear map `f ↦ ψ_f[O, P]` into `C^∞(O, P)` for Laurent coordinates. -/
def fourierOrbitLaurentSmoothSectionLinear {J : Type*} [Fintype J]
    (e : unitaryUnramifiedCharacters ν ≃* (J → Circle)) (hνc : ∀ i, Continuous (ν i))
    (hPK' : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
    (hsqπ : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μM)
    [MeasurableInv G] [μ.IsInvInvariant] [SigmaFinite μ] (hμK : μ (K : Set G) = 1)
    (hδU : IsUnimodularModulus U hU) [Nonempty (CompactOpenSubgroup M)]
    {μL : Measure M} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] [MeasurableInv M]
    [μL.IsInvInvariant] [SFinite μL] {ΞM σM : M → ℝ} (hwM : L2Weights μL ΞM σM)
    (hTπ : HasTemperedCoefficients ΞM σM π.obj.representation)
    (hTM : ∀ A : UnitaryOrbitRepresentative ν π,
      HasTemperedCoefficients ΞM σM A.val.obj.representation)
    (hΞM : ∀ m, ΞM m⁻¹ = ΞM m) (hσM : ∀ m, σM m⁻¹ = σM m)
    {νU : Measure U} [νU.IsMulLeftInvariant] [νU.IsMulRightInvariant] [SFinite νU]
    (hD : ConstantTermData νU (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
    (hνU : IsConjModulus h.levi_le_normalizer νU
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
    (hE : ConstantTermEstimate νU
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) Ξ σ ΞM σM)
    (ht : TranslationWeights Ξ σ) (htM : TranslationWeights ΞM σM)
    (hPKiw : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μL {m : M | (m : G) ∈ K} = 1) (hUK : νU {u : U | (u : G) ∈ K} = 1)
    (he : HasLaurentUnitaryCoordinates ν e) {Cn : ℝ}
    (hnσ : ∀ m, ‖laurentExponent ν e he m‖ ≤ Cn * (1 + σM m))
    (hint : ∀ (f : Space Ξ σ) (A : UnitaryOrbitRepresentative ν π)
      (ψ : productInducedCoefficientObject h hU A.val.obj),
      Integrable
        (fun x : G × K => conj (CompactInduction.integrand h hU A.val.obj K x.1 ψ x.2) * f x.1)
        (μ.prod (CompactInduction.measure K hK))) :
        Space Ξ σ →ₗ[ℂ] productInducedSmoothOrbitSections ν π e h hU K hP hK hνc hm hPK' :=
  fourierOrbitSmoothSectionLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ
    e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK
    (laurentExponent_mul ν e he) (K₀ := Classical.arbitrary (CompactOpenSubgroup M))
    (fun _ hk => laurentExponent_eq_zero_of_isCompact ν e he hνc
      (Classical.arbitrary (CompactOpenSubgroup M)).2 hk)
    (measurable_laurentExponent ν e he (isOpen_commonNormKernel_of_continuous ν hνc)) hnσ
    (fun z m => (torusCharacter_laurentExponent ν e he m z).symm) hint

theorem fourierOrbitLaurentSmoothSectionLinear_apply {J : Type*} [Fintype J]
    (e : unitaryUnramifiedCharacters ν ≃* (J → Circle)) (hνc : ∀ i, Continuous (ν i))
    (hPK' : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
    (hsqπ : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μM)
    [MeasurableInv G] [μ.IsInvInvariant] [SigmaFinite μ] (hμK : μ (K : Set G) = 1)
    (hδU : IsUnimodularModulus U hU) [Nonempty (CompactOpenSubgroup M)]
    {μL : Measure M} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] [MeasurableInv M]
    [μL.IsInvInvariant] [SFinite μL] {ΞM σM : M → ℝ} (hwM : L2Weights μL ΞM σM)
    (hTπ : HasTemperedCoefficients ΞM σM π.obj.representation)
    (hTM : ∀ A : UnitaryOrbitRepresentative ν π,
      HasTemperedCoefficients ΞM σM A.val.obj.representation)
    (hΞM : ∀ m, ΞM m⁻¹ = ΞM m) (hσM : ∀ m, σM m⁻¹ = σM m)
    {νU : Measure U} [νU.IsMulLeftInvariant] [νU.IsMulRightInvariant] [SFinite νU]
    (hD : ConstantTermData νU (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
    (hνU : IsConjModulus h.levi_le_normalizer νU
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
    (hE : ConstantTermEstimate νU
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) Ξ σ ΞM σM)
    (ht : TranslationWeights Ξ σ) (htM : TranslationWeights ΞM σM)
    (hPKiw : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μL {m : M | (m : G) ∈ K} = 1) (hUK : νU {u : U | (u : G) ∈ K} = 1)
    (he : HasLaurentUnitaryCoordinates ν e) {Cn : ℝ}
    (hnσ : ∀ m, ‖laurentExponent ν e he m‖ ≤ Cn * (1 + σM m))
    (hint : ∀ (f : Space Ξ σ) (A : UnitaryOrbitRepresentative ν π)
      (ψ : productInducedCoefficientObject h hU A.val.obj),
      Integrable
        (fun x : G × K => conj (CompactInduction.integrand h hU A.val.obj K x.1 ψ x.2) * f x.1)
        (μ.prod (CompactInduction.measure K hK)))
    (f : Space Ξ σ) :
    (fourierOrbitLaurentSmoothSectionLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw
      hT hΞ hσ e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK he
      hnσ hint f).val =
      fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f :=
  rfl

end Smooth

end Langlands.HarishChandraSchwartz
