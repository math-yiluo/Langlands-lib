import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalWavePacketOrthogonality

/-! # Convolution of a cuspidal function with a wave packet

Waldspurger, proof of Lemma VIII.2.3 (printed p. 322): for `f₁ ∈ °𝒞(G)`, a proper `P` and
`ψ ∈ C^∞(𝒪, P)`, `f₁ ∗ f_ψ = f_ψ ∗ f₁ = 0`. With `f'₁(h) = \overline{f₁(g h⁻¹)}`,
`(f₁ ∗ f_ψ)(g) = (f'₁, f_ψ)_G`, and `f'₁` has vanishing constant term along `P`.

* `Space.complexConj`: the complex conjugate `f̄` of `f ∈ 𝒞(G)`.
* `IsUnipotentCuspidal ν f`: `∫_U f(x u y) dν(u) = 0` for all `x, y ∈ G`.
* `constantTermIndVanishes_of_isUnipotentCuspidal`, `isUnipotentCuspidal_of_constantTermIndVanishes`:
  this is equivalent to `f^{(P),Ind} = 0`.
* `convolution_eq_conj_pairing`, `convolution_eq_conj_pairing_right`: the convolutions with `F`
  as pairings.
* `convolution_inducedOrbitWavePacket_eq_zero`, `convolution_inducedOrbitWavePacket_left_eq_zero`:
  `f₁ ∗ f_ψ = 0` and `f_ψ ∗ f₁ = 0`.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped ComplexConjugate NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe uG uV uI uJ

section ComplexConj

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Nonempty (CompactOpenSubgroup G)] {Ξ σ : G → ℝ}

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Nonempty (CompactOpenSubgroup G)] in
theorem nu_complexConj (r : ℝ) (f : G → ℂ) :
    nu Ξ σ r (fun g => conj (f g)) = nu Ξ σ r f := by
  simp only [nu, RCLike.enorm_conj]

omit [TopologicalSpace G] [IsTopologicalGroup G] [Nonempty (CompactOpenSubgroup G)] in
theorem complexConj_mem_levelSubmodule {H : Subgroup G} {f : G → ℂ}
    (hf : f ∈ levelSubmodule Ξ σ H) : (fun g => conj (f g)) ∈ levelSubmodule Ξ σ H :=
  ⟨fun h₁ h₁m h₂ h₂m g => by simp only [hf.1 h₁ h₁m h₂ h₂m g], fun r => by
    rw [nu_complexConj]
    exact hf.2 r⟩

theorem complexConj_mem_schwartzSubmodule {f : G → ℂ} (hf : f ∈ schwartzSubmodule Ξ σ) :
    (fun g => conj (f g)) ∈ schwartzSubmodule Ξ σ := by
  obtain ⟨K, hK⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp hf
  exact (mem_schwartzSubmodule_iff Ξ σ).mpr ⟨K, complexConj_mem_levelSubmodule hK⟩

/-- The complex conjugate `f̄ : g ↦ \overline{f(g)}` of `f ∈ 𝒞(G)`. -/
def Space.complexConj (f : Space Ξ σ) : Space Ξ σ :=
  (⟨fun g => conj (f g), complexConj_mem_schwartzSubmodule (Space.coe_mem f)⟩ :
    schwartzSubmodule Ξ σ)

@[simp] theorem Space.complexConj_apply (f : Space Ξ σ) (g : G) :
    Space.complexConj f g = conj (f g) :=
  rfl

end ComplexConj

section Cusp

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)] {M U : Subgroup G}
  {ν : Measure U} {δ : M →* ℝ≥0ˣ} {Ξ σ : G → ℝ} {ΞM σM : M → ℝ}

variable (ν) in
/-- **Cuspidality along `U`**: `∫_U f(x u y) dν(u) = 0` for all `x, y ∈ G`. For the unipotent
radical `U` of a parabolic subgroup this is the vanishing of all constant terms of all two-sided
translates of `f` along `P`. -/
def IsUnipotentCuspidal (f : G → ℂ) : Prop :=
  ∀ x y : G, ∫ u : U, f (x * u * y) ∂ν = 0

/-- A cuspidal `f` has vanishing constant term `f^{(P),Ind}`. -/
theorem constantTermIndVanishes_of_isUnipotentCuspidal (hD : ConstantTermData ν δ)
    (hE : ConstantTermEstimate ν δ Ξ σ ΞM σM) (ht : TranslationWeights Ξ σ)
    (htM : TranslationWeights ΞM σM) {f : Space Ξ σ} (hf : IsUnipotentCuspidal ν f) :
    ConstantTermIndVanishes hD hE ht htM f := by
  intro x
  apply Space.ext
  intro m
  change HarishChandraSchwartz.constantTermInd ν δ f x m = 0
  simp only [HarishChandraSchwartz.constantTermInd, constantTerm, translate_apply]
  have h := hf (x.2⁻¹ * m) x.1
  simp only [mul_assoc] at h ⊢
  rw [h, mul_zero]

/-- Conversely, `f^{(P),Ind} = 0` implies cuspidality along `U`. -/
theorem isUnipotentCuspidal_of_constantTermIndVanishes (hD : ConstantTermData ν δ)
    (hE : ConstantTermEstimate ν δ Ξ σ ΞM σM) (ht : TranslationWeights Ξ σ)
    (htM : TranslationWeights ΞM σM) {f : Space Ξ σ}
    (hf : ConstantTermIndVanishes hD hE ht htM f) : IsUnipotentCuspidal ν f := by
  intro x y
  have h := congrArg (fun φ : Space ΞM σM => φ 1) (hf (y, x⁻¹))
  change HarishChandraSchwartz.constantTermInd ν δ f (y, x⁻¹) 1 = (0 : Space ΞM σM) 1 at h
  simp only [HarishChandraSchwartz.constantTermInd, constantTerm, translate_apply, map_one,
    Units.val_one, NNReal.sqrt_one, NNReal.coe_one, Complex.ofReal_one, one_mul, inv_inv,
    OneMemClass.coe_one] at h
  simpa [mul_assoc] using h

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [Nonempty (CompactOpenSubgroup G)] in
/-- `h ↦ \overline{f(g h⁻¹)}` is cuspidal when `f` is, for an inversion-invariant `ν`. -/
theorem isUnipotentCuspidal_conj_mul_inv [MeasurableInv U] [ν.IsInvInvariant] (g : G)
    {f : G → ℂ} (hf : IsUnipotentCuspidal ν f) :
    IsUnipotentCuspidal ν (fun h => conj (f (g * h⁻¹))) := by
  intro x y
  have e : ∀ u : U, g * ((x * (u : G) * y))⁻¹ = (g * y⁻¹) * ((u⁻¹ : U) : G) * x⁻¹ := by
    intro u
    simp only [mul_inv_rev, Subgroup.coe_inv, mul_assoc]
  simp only [e]
  rw [integral_conj, integral_inv_eq_self (fun u : U => f ((g * y⁻¹) * (u : G) * x⁻¹)) ν,
    hf, map_zero]

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [Nonempty (CompactOpenSubgroup G)] in
/-- `h ↦ \overline{f(h⁻¹ g)}` is cuspidal when `f` is, for an inversion-invariant `ν`. -/
theorem isUnipotentCuspidal_conj_inv_mul [MeasurableInv U] [ν.IsInvInvariant] (g : G)
    {f : G → ℂ} (hf : IsUnipotentCuspidal ν f) :
    IsUnipotentCuspidal ν (fun h => conj (f (h⁻¹ * g))) := by
  intro x y
  have e : ∀ u : U, ((x * (u : G) * y))⁻¹ * g = y⁻¹ * ((u⁻¹ : U) : G) * (x⁻¹ * g) := by
    intro u
    simp only [mul_inv_rev, Subgroup.coe_inv, mul_assoc]
  simp only [e]
  rw [integral_conj, integral_inv_eq_self (fun u : U => f (y⁻¹ * (u : G) * (x⁻¹ * g))) ν,
    hf, map_zero]

end Cusp

section Convolution

variable {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]

/-- `(f₁ ∗ F)(g) = \overline{(F, f'₁)_G}` with `f'₁(h) = \overline{f₁(g h⁻¹)}`, for a left and
inversion invariant `μ`. -/
theorem convolution_eq_conj_pairing (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (f₁ F : G → ℂ) (g : G) :
    convolution μ f₁ F g = conj (pairing μ F fun h => conj (f₁ (g * h⁻¹))) := by
  rw [convolution_apply, pairing_apply, ← integral_conj]
  have h1 : ∫ h, f₁ h * F (h⁻¹ * g) ∂μ = ∫ h, f₁ (g * h) * F ((g * h)⁻¹ * g) ∂μ :=
    (integral_mul_left_eq_self (fun h => f₁ h * F (h⁻¹ * g)) g).symm
  have h2 : ∫ h, f₁ (g * h) * F ((g * h)⁻¹ * g) ∂μ = ∫ h, f₁ (g * h⁻¹) * F h ∂μ := by
    rw [← integral_inv_eq_self (fun h => f₁ (g * h⁻¹) * F h) μ]
    congr 1
    funext h
    simp only [inv_inv, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  rw [h1, h2]
  congr 1
  funext h
  simp only [map_mul, Complex.conj_conj]
  ring

omit [MeasurableMul G] [MeasurableInv G] in
/-- `(F ∗ f₁)(g) = \overline{(F, f''₁)_G}` with `f''₁(h) = \overline{f₁(h⁻¹ g)}`. -/
theorem convolution_eq_conj_pairing_right (μ : Measure G) (F f₁ : G → ℂ) (g : G) :
    convolution μ F f₁ g = conj (pairing μ F fun h => conj (f₁ (h⁻¹ * g))) := by
  rw [convolution_apply, pairing_apply, ← integral_conj]
  congr 1
  funext h
  simp only [map_mul, Complex.conj_conj]

end Convolution

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
/-- **Waldspurger, proof of Lemma VIII.2.3: `f₁ ∗ f_ψ = 0`** for `f₁ ∈ 𝒞(G)` cuspidal along `U`
(`IsUnipotentCuspidal`) and a wave packet `f_ψ` on an orbit of the Levi subgroup `M` of `P = M U`,
under the hypotheses of `pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero` for the
function `f'₁ : h ↦ \overline{f₁(g h⁻¹)}` and an inversion-invariant `ν_U`. -/
theorem convolution_inducedOrbitWavePacket_eq_zero
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
    [MeasurableInv U] [νU.IsInvInvariant]
    (f₁ : Space (xi hP₀K δ₀) σ) (hcusp : IsUnipotentCuspidal νU f₁) (g : G)
    (hint : ∀ (A : UnitaryOrbitRepresentative ν π)
      (ψ : productInducedCoefficientObject h hU A.val.obj),
      Integrable (fun x : G × K =>
          conj (CompactInduction.integrand h hU A.val.obj K x.1 ψ x.2) *
            (Space.complexConj (Space.translate ht g⁻¹ 1 (Space.check hΞ hσ f₁))) x.1)
        (μG.prod (CompactInduction.measure K hK))) :
    convolution μG f₁
      (inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q) g = 0 := by
  have hF : (((Space.complexConj (Space.translate ht g⁻¹ 1 (Space.check hΞ hσ f₁))) :
      Space (xi hP₀K δ₀) σ) : G → ℂ) =
      fun x => conj (f₁ (g * x⁻¹)) := by
    funext x
    simp [Space.complexConj_apply, Space.translate_apply, check_apply, mul_inv_rev]
  have hcusp' : IsUnipotentCuspidal νU
      ((Space.complexConj (Space.translate ht g⁻¹ 1 (Space.check hΞ hσ f₁))) :
        Space (xi hP₀K δ₀) σ) := by
    rw [hF]
    exact isUnipotentCuspidal_conj_mul_inv g hcusp
  rw [convolution_eq_conj_pairing, ← hF,
    pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero h hU hP K hK hPK hG hδ ν π
      hν hr e hcof C hC μ hsq ρ w hP₀K hwt hT hΞ hσ hLaurent he hwm hwb hδU hL hMK hδ₀ hcoeff q hwM
      hTM hΞM hσM hD hνU hE ht htM hμK hPKiw hMKμ hUK _ hint
      (constantTermIndVanishes_of_isUnipotentCuspidal hD hE ht htM hcusp'),
    map_zero]

include hcof hwt hT hΞ hσ in
/-- **Waldspurger, proof of Lemma VIII.2.3: `f_ψ ∗ f₁ = 0`**, under the same hypotheses for the
function `f''₁ : h ↦ \overline{f₁(h⁻¹ g)}`. -/
theorem convolution_inducedOrbitWavePacket_left_eq_zero
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
    [MeasurableInv U] [νU.IsInvInvariant]
    (f₁ : Space (xi hP₀K δ₀) σ) (hcusp : IsUnipotentCuspidal νU f₁) (g : G)
    (hint : ∀ (A : UnitaryOrbitRepresentative ν π)
      (ψ : productInducedCoefficientObject h hU A.val.obj),
      Integrable (fun x : G × K =>
          conj (CompactInduction.integrand h hU A.val.obj K x.1 ψ x.2) *
            (Space.complexConj (Space.translate ht 1 g (Space.check hΞ hσ f₁))) x.1)
        (μG.prod (CompactInduction.measure K hK))) :
    convolution μG
      (inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q) f₁ g = 0 := by
  have hF : (((Space.complexConj (Space.translate ht 1 g (Space.check hΞ hσ f₁))) :
      Space (xi hP₀K δ₀) σ) : G → ℂ) =
      fun x => conj (f₁ (x⁻¹ * g)) := by
    funext x
    simp [Space.complexConj_apply, Space.translate_apply, check_apply, mul_inv_rev]
  have hcusp' : IsUnipotentCuspidal νU
      ((Space.complexConj (Space.translate ht 1 g (Space.check hΞ hσ f₁))) :
        Space (xi hP₀K δ₀) σ) := by
    rw [hF]
    exact isUnipotentCuspidal_conj_inv_mul g hcusp
  rw [convolution_eq_conj_pairing_right, ← hF,
    pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero h hU hP K hK hPK hG hδ ν π
      hν hr e hcof C hC μ hsq ρ w hP₀K hwt hT hΞ hσ hLaurent he hwm hwb hδU hL hMK hδ₀ hcoeff q hwM
      hTM hΞM hσM hD hνU hE ht htM hμK hPKiw hMKμ hUK _ hint
      (constantTermIndVanishes_of_isUnipotentCuspidal hD hE ht htM hcusp'),
    map_zero]

end Pairing

end Langlands.HarishChandraSchwartz
