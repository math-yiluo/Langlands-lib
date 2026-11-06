import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedConstantTermFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientConvergence
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierOrbitSmoothness

/-! # Lemma VII.1.2 and Proposition VII.1.3 for the spherical function `Ξ`

In Waldspurger's setting `C(G)` is defined with the spherical function `Ξ` of II.1. For that
`Ξ` (`xi hP₀K δ₀`), the absolute convergence assumed in `InducedConstantTermFourier` (hypothesis
`hint`) is `integrable_coefficientPairingIntegrand` of `InducedCoefficientConvergence`, which
uses Corollary III.1.2 for `M` and Lemma II.1.5 (`L2Weights`). This module records Lemma VII.1.2
(`inducedFourierTransform_eq_constantTermInducedFourierTransform_xi`) and the map
`f ↦ ψ_f[O, P]` into `C^∞(O, P)` of Proposition VII.1.3 (`fourierOrbitSmoothSectionLinearXi`)
without that hypothesis.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel
open Langlands.HarmonicAnalysis.TorusFourier
open scoped ComplexConjugate NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uV

section Xi

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
  {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)]
  (hL : LeviData (K : Subgroup G) P₀ P M δ₀
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
  (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
  (hMKiw : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
  (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
  (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
    ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * xi hMKiw δ₀M m)
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {σ : G → ℝ}
  (hw : L2Weights μ (xi hP₀K δ₀) σ)
  (hT : HasTemperedCoefficients (xi hP₀K δ₀) σ
    ((normalizedInductionFunctor h hU).obj A).representation)
  (hΞ : ∀ g, xi hP₀K δ₀ g⁻¹ = xi hP₀K δ₀ g) (hσ : ∀ g, σ g⁻¹ = σ g)
  (hδU : IsUnimodularModulus U hU) [Nonempty (CompactOpenSubgroup M)]
  {μL : Measure M} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] {ΞM σM : M → ℝ}
  (hwM : L2Weights μL ΞM σM) (hTM : HasTemperedCoefficients ΞM σM A.representation)
  (hΞM : ∀ m, ΞM m⁻¹ = ΞM m) (hσM : ∀ m, σM m⁻¹ = σM m)
  {ν : Measure U} [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
  (hD : ConstantTermData ν (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
  (hν : IsConjModulus h.levi_le_normalizer ν
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
  (hE : ConstantTermEstimate ν (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer)
    (xi hP₀K δ₀) σ ΞM σM)
  (ht : TranslationWeights (xi hP₀K δ₀) σ) (htM : TranslationWeights ΞM σM)

include hL hδ₀ hcoeff in
/-- **Lemma VII.1.2 for Waldspurger's `Ξ`**: with `Ξ` the spherical function `xi hP₀K δ₀` and
Corollary III.1.2 for `M` (hypothesis `hcoeff`), `f̂(ω, P) = f̂^{(P),Ind}(ω)` for every
`f ∈ C(G)`; the absolute convergence of the proof is `integrable_coefficientPairingIntegrand`. -/
theorem inducedFourierTransform_eq_constantTermInducedFourierTransform_xi
    [MeasurableInv G] [μ.IsInvInvariant] [SigmaFinite μ] (hμK : μ (K : Set G) = 1)
    [MeasurableInv M] [μL.IsInvInvariant] [SFinite μL] [SFinite ν]
    (hPKiw : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μL {m : M | (m : G) ∈ K} = 1) (hUK : ν {u : U | (u : G) ∈ K} = 1)
    (f : Space (xi hP₀K δ₀) σ) :
    inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ f =
      constantTermInducedFourierTransform h hU hδU A hwM hsq.1 hTM hΞM hσM
        (representationFormalDegree C hC μM hcof hsq hi) hD hν hE ht htM f :=
  inducedFourierTransform_eq_constantTermInducedFourierTransform h hU hP hm K hK hPK hG hδ A
    hcof C hC μM hsq hi hw hT hΞ hσ hδU hwM hTM hΞM hσM hD hν hE ht htM hμK hPKiw hMK hUK f
    fun ψ => integrable_coefficientPairingIntegrand h hU A K hK hδU hL hP₀K hMKiw hδ₀ hcoeff hw
      ψ f

end Xi

section SmoothXi

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
  {I : Type*} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M)) (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μM : Measure (M ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : ∀ A : UnitaryOrbitRepresentative ν π,
    IsSquareIntegrableModCentralSubgroup C hC A.val.obj.representation μM)
  {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)]
  (hL : LeviData (K : Subgroup G) P₀ P M δ₀
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
  (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
  (hMKiw : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
  (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
  (hcoeff : ∀ (A : UnitaryOrbitRepresentative ν π) (v : A.val.obj)
    (ℓ : SmoothDual A.val.obj.representation),
    ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.val.obj.representation m v)‖ ≤ C * xi hMKiw δ₀M m)
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {σ : G → ℝ}
  (hw : L2Weights μ (xi hP₀K δ₀) σ)
  (hT : ∀ A : UnitaryOrbitRepresentative ν π,
    HasTemperedCoefficients (xi hP₀K δ₀) σ
      ((normalizedInductionFunctor h hU).obj A.val.obj).representation)
  (hΞ : ∀ g, xi hP₀K δ₀ g⁻¹ = xi hP₀K δ₀ g) (hσ : ∀ g, σ g⁻¹ = σ g)

include hL hδ₀ hcoeff in
/-- **Waldspurger's map `f ↦ ψ_f[O, P]` for the spherical function `Ξ`** (Proposition VII.1.3,
first assertion): with `Ξ = xi hP₀K δ₀` and Corollary III.1.2 for every representative of the
orbit (hypothesis `hcoeff`), `f ↦ ψ_f[O, P]` is a linear map from `C(G)` into the smooth sections
`C^∞(O, P)`; the absolute convergence of Lemma VII.1.2 is supplied by
`integrable_coefficientPairingIntegrand`. -/
def fourierOrbitSmoothSectionLinearXi {J : Type*} [Fintype J]
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
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) (xi hP₀K δ₀) σ ΞM σM)
    (ht : TranslationWeights (xi hP₀K δ₀) σ) (htM : TranslationWeights ΞM σM)
    (hPKiw : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μL {m : M | (m : G) ∈ K} = 1) (hUK : νU {u : U | (u : G) ∈ K} = 1)
    {n : M → J → ℤ} (hn : ∀ g h, n (g * h) = n g + n h) {K₀ : CompactOpenSubgroup M}
    (hK₀ : ∀ k ∈ K₀.toSubgroup, n k = 0) (hnm : Measurable n) {Cn : ℝ}
    (hnσ : ∀ m, ‖n m‖ ≤ Cn * (1 + σM m))
    (hne : ∀ z m, (((unitaryTorusParameter ν e z).val m : ℂˣ) : ℂ) = torusCharacter (n m) z) :
    Space (xi hP₀K δ₀) σ →ₗ[ℂ]
      productInducedSmoothOrbitSections ν π e h hU K hP hK hνc hm hPK' :=
  fourierOrbitSmoothSectionLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ e
    hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm hnσ hne
    fun f A ψ => integrable_coefficientPairingIntegrand h hU A.val.obj K hK hδU hL hP₀K hMKiw hδ₀
      (hcoeff A) hw ψ f

end SmoothXi

end Langlands.HarishChandraSchwartz
