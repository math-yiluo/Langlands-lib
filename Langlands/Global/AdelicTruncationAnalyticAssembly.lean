import Langlands.Global.AdelicTruncationAffineDenominators
import Langlands.Global.AdelicTruncationSectorGeometry
import Langlands.Global.AdelicWeakPairingCentralTransfer

/-! # Assembly of the truncation comparison from unshifted spectral data -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set Filter Metric
open scoped CategoryTheory.MonObj ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints AdelicSiegelFactors
  ImaginaryAxis Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Param[" P "]" => ComplexCharacterParameter F (fam.P P)
local notation "Fun" => (AdelicGroupPoints F G → ℂ)
local notation "Z" => fam.positiveSplitComponent fam.top
local notation "QHaar" => normOneRationalQuotientHaarMeasure F G

/-- In positive relative rank, the unshifted data suffice for the analytic and estimate
conclusions of the characteristic-to-regularized comparison. The complex pole-free region
may be the intersection of the generic set with a common coefficient holomorphy domain. -/
def TruncationAnalyticAssemblyStatement : Prop :=
  (simpleRelativeRoots fam.i fam.ν).Nonempty →
  ∀ {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)
    (C : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅)
      (Standard.leviScheme fam.i fam.ν ∅))
    (T₀ : V fam.T) (vol : Idx → ℝ) (P : Idx) {N d n nT nZ : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (ec : (Fin n → ℂ) ≃ₗ[ℂ] Param[P]) (eT : V fam.T ≃ₗ[ℝ] (Fin nT → ℝ))
    (eZ : RealCharacterDual F (fam.P fam.top) ≃ₗ[ℝ] (Fin nZ → ℝ))
    (E : Param[P] → Fun) (Φ : Fun) (R₀ : ℝ) (L : ∀ Q : Idx, fam.AffineExponentLabels P Q)
    (e₀ : (Fin n → ℝ) → ∀ Q : Idx, fam.UnitaryPairingExpansion Q)
    (D : Set (Fin n → ℂ)) (f : V fam.T → (Fin n → ℂ) → ℂ)
    (a : Z → (Fin n → ℂ) → ℂ) (b : Z → ℂ),
    let Lm (x : Fin n → ℝ) := ec (imaginarySlice x)
    let U := {x | Lm x ∈ fam.genericParameterRegion P L}
    let A (T : V fam.T) (x : Fin n → ℝ) := fam.truncatedPairing hK C T₀ T 1 (E (Lm x)) Φ
    let Δ (t : Fin nT → ℝ) (x : Fin n → ℝ) := A (eT.symm t) x - f (eT.symm t) (imaginarySlice x)
    0 < R₀ →
    (∀ Q (k : Fin (L Q).size) (α : fam.relativeSimpleRoots Q), ∃ x : Fin n → ℝ,
      fam.corootValue Q ((L Q).label k (Lm x)) α ≠ 0) →
    IsOpen D → Dense D → imaginarySlice ⁻¹' D = U →
    (∀ z, Differentiable ℂ (a z) ∧ ∀ x,
      fam.centralTranslate z (E (Lm x)) = a z (imaginarySlice x) • E (Lm x) ∧
      fam.centralTranslate z Φ = b z • Φ ∧ ‖a z (imaginarySlice x) * starRingEnd ℂ (b z)‖ = 1) →
    (∀ x ∈ U, fam.IsWeakConstantTermPairingExpansion hsmooth hcalc rho hK 1 (E (Lm x)) Φ (e₀ x) ∧
      ∀ Q, (e₀ x Q).IsLabelledBy (L Q) (Lm x)) →
    (∀ T, fam.IsRegularTruncationParameter R₀ T → Continuous (A T) ∧
      ∀ x, IntegrableOn (fam.truncatedPairingIntegrand 1 (E (Lm x)) Φ) (fam.truncationRegion hK C T₀ T) QHaar) →
    (∀ T, fam.IsRegularTruncationParameter R₀ T → DifferentiableOn ℂ (f T) D ∧
      HasImaginaryHyperplanePresentation (f T) D ∧
      ∀ x ∈ U, f T (imaginarySlice x) = fam.regularizedPairing vol (e₀ x) T) →
    (∀ δ : ℝ, 0 < δ → ∀ B₀ ⊆ U, Bornology.IsBounded B₀ →
      ∃ B ε : ℝ, 0 ≤ B ∧ 0 < ε ∧ ∀ x ∈ B₀,
        ∀ t ∈ fam.truncationSector eT δ, ∀ s ∈ fam.truncationSector eT δ,
          fam.IsRegularTruncationParameter R₀ (eT.symm t) → ‖s‖ ≤ ‖t‖ →
          dist (Δ t x) (Δ (t + s) x) ≤ B * Real.exp (-ε * ‖t‖)) →
    (∀ δ : ℝ, 0 < δ → ∀ β : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ U →
      Tendsto (fun t => ∫ x, β x • Δ t x)
        (comap (fun t : Fin nT → ℝ => ‖t‖) atTop ⊓ 𝓟 (fam.truncationSector eT δ)) (𝓝 0)) →
    ∃ (R : ℝ) (expansion : (Fin n → ℝ) → Z → ∀ Q : Idx, fam.UnitaryPairingExpansion Q)
      (omegaExt : V fam.T → Z → (Fin n → ℂ) → ℂ) (Dω : V fam.T → Z → Set (Fin n → ℂ)),
    R₀ ≤ R ∧ 0 < R ∧ IsOpen U ∧ Dense U ∧
    (∀ x ∈ U, ∀ z,
      fam.IsWeakConstantTermPairingExpansion hsmooth hcalc rho hK z (E (Lm x)) Φ (expansion x z) ∧
      ∀ Q, (expansion x z Q).IsLabelledBy (L Q) (Lm x)) ∧
    (∀ T, fam.IsRegularTruncationParameter R T → ∀ z,
      IsOpen (Dω T z) ∧ Set.range (imaginarySlice (n := n)) ⊆ Dω T z ∧
      DifferentiableOn ℂ (omegaExt T z) (Dω T z) ∧
      ∀ x ∈ U, omegaExt T z (imaginarySlice x) = fam.regularizedPairing vol (expansion x z) T) ∧
    ∀ δ : ℝ, 0 < δ → ∀ Λ : Set (Fin n → ℝ), Bornology.IsBounded Λ →
      ∃ (B ε : ℝ) (k : ℕ), 0 < B ∧ 0 < ε ∧
      ∀ T, fam.IsRegularTruncationParameter R T →
      (∀ α ∈ simpleRelativeRoots fam.i fam.ν, δ * ‖eT T‖ ≤ eval fam.T α T) →
      ∀ z, ∀ x ∈ Λ,
        IntegrableOn (fam.truncatedPairingIntegrand z (E (Lm x)) Φ) (fam.truncationRegion hK C T₀ T) QHaar ∧
        ‖fam.truncatedPairing hK C T₀ T z (E (Lm x)) Φ - omegaExt T z (imaginarySlice x)‖ ≤
          B * Real.exp (-ε * ‖eT T‖) * (1 + ‖eZ (characterLog F (fam.P fam.top) z.val)‖ ^ k)

set_option maxHeartbeats 4200000 in
/-- First obtain the unshifted generic pointwise bound from the comparable increments and
smooth tests. Then divide out the local hyperplane denominators and use continuity. The
central phase transfers both the extended pairing and the error bound. -/
theorem truncationAnalyticAssembly : fam.TruncationAnalyticAssemblyStatement := by
  classical
  intro hroot K hK C T₀ vol P N d n nT nZ rho hsmooth hcalc ec eT eZ E Φ R₀ L e₀ D f a b Lm U A Δ
    hR₀ hne hD hDc hDU hcentral hexp hA hf hinc htest
  have hUo : IsOpen U := hDU ▸ hD.preimage continuous_imaginarySlice
  have hUmem {x : Fin n → ℝ} (hx : x ∈ U) : imaginarySlice x ∈ D := by
    change x ∈ imaginarySlice ⁻¹' D
    rwa [hDU]
  have hUd : Dense U := by
    obtain ⟨_, _, _, hd⟩ := fam.open_dense_genericParameterRegion P L ec hne
    exact hd
  obtain ⟨R, hR₀R, hR, hRnorm⟩ := fam.exists_rootCutoff_for_one_le_norm eT hroot R₀
  have hreg {T : V fam.T} (hT : fam.IsRegularTruncationParameter R T) :
      fam.IsRegularTruncationParameter R₀ T := ⟨hT.1, fun α hα => hR₀R.trans (hT.2 α hα)⟩
  let sector (δ : ℝ) (T : V fam.T) :=
    ∀ α ∈ simpleRelativeRoots fam.i fam.ν, δ * ‖eT T‖ ≤ eval fam.T α T
  have hbound (δ : ℝ) (hδ : 0 < δ) (Λ : Set (Fin n → ℝ)) (hΛ : Bornology.IsBounded Λ) :
      ∃ B ε : ℝ, 0 < B ∧ 0 < ε ∧ ∀ T, fam.IsRegularTruncationParameter R T → sector δ T →
        ∀ x ∈ Λ ∩ U, ‖A T x - f T (imaginarySlice x)‖ ≤ B * Real.exp (-ε * ‖eT T‖) := by
    let Cδ := fam.truncationSector eT δ
    let l := comap (fun t : Fin nT → ℝ => ‖t‖) atTop ⊓ 𝓟 Cδ
    have htreg : ∀ᶠ t in l, fam.IsRegularTruncationParameter R (eT.symm t) := by
      have hr : ∀ᶠ t : Fin nT → ℝ in comap (fun t : Fin nT → ℝ => ‖t‖) atTop, R / δ ≤ ‖t‖ :=
        eventually_comap.mpr ((eventually_ge_atTop (R / δ)).mono fun r hr t ht => ht.symm ▸ hr)
      filter_upwards [hr.filter_mono (inf_le_left : l ≤ _), (eventually_principal.mpr (subset_rfl : Cδ ⊆ Cδ)).filter_mono
        (inf_le_right : l ≤ 𝓟 Cδ)] with t ht hc
      exact fam.isRegularTruncationParameter_of_mem_truncationSector eT hδ hc ht
    have hc : ∀ᶠ t in l, ContinuousOn (Δ t) U := by
      filter_upwards [htreg] with t ht
      have hf' : ContinuousOn (fun x => f (eT.symm t) (imaginarySlice x)) U :=
        (hf _ (hreg ht)).1.continuousOn.comp continuous_imaginarySlice.continuousOn
          (fun _ hx => hUmem hx)
      exact (hA _ (hreg ht)).1.continuousOn.sub hf'
    obtain ⟨B, ε, k, hB, hε, H⟩ :=
      fam.norm_le_of_tested_truncationIncrements eT eZ (volume : Measure (Fin n → ℝ)) U hUo
        (fun t _ => Δ t) δ R hδ hR hRnorm (fun _ => hc)
        (fun S hSU hS => by
          obtain ⟨B, ε, hB, hε, H⟩ := hinc δ hδ S hSU hS
          refine ⟨B, ε, 0, hB, hε, fun z x hx t ht s hs hr hst => ?_⟩
          apply (H x hx t ht s hs (hreg hr) hst).trans
          exact le_mul_of_one_le_right (mul_nonneg hB (Real.exp_nonneg _)) (by simp))
        (fun _ => htest δ hδ) Λ hΛ
    let c := 1 + ‖eZ (characterLog F (fam.P fam.top) ((1 : Z).val))‖ ^ k
    have hpos : 0 < c := by dsimp only [c]; positivity
    refine ⟨B * c, ε, mul_pos hB hpos, hε, fun T hT hs x hx => ?_⟩
    have ht : eT T ∈ Cδ := by
      change eT.symm (eT T) ∈ fam.coroots.realCorootSpan ∧ _
      simp only [eT.symm_apply_apply]
      exact ⟨hT.1, hs⟩
    have hT' : fam.IsRegularTruncationParameter R (eT.symm (eT T)) := by
      simpa only [eT.symm_apply_apply] using hT
    have h := H 1 x hx (eT T) ht hT'
    simpa only [Δ, eT.symm_apply_apply, mul_right_comm B _ c, c] using h
  have hext (T : V fam.T) : ∃ (ω₀ : (Fin n → ℂ) → ℂ) (W : Set (Fin n → ℂ)),
      fam.IsRegularTruncationParameter R T →
      IsOpen W ∧ Set.range (imaginarySlice (n := n)) ⊆ W ∧ DifferentiableOn ℂ ω₀ W ∧ EqOn ω₀ (f T) (W ∩ D) := by
    by_cases hT : fam.IsRegularTruncationParameter R T
    · let q := ‖eT T‖ + 1
      let δ := R / q
      have hq : 0 < q := by dsimp only [q]; positivity
      have hδ : 0 < δ := div_pos hR hq
      have hs : sector δ T := by
        intro α hα
        calc
          δ * ‖eT T‖ ≤ δ * q := mul_le_mul_of_nonneg_left (by dsimp only [q]; linarith) hδ.le
          _ = R := div_mul_cancel₀ _ hq.ne'
          _ ≤ _ := hT.2 α hα
      have hB (Λ : Set (Fin n → ℝ)) (hΛ : Bornology.IsBounded Λ) :
          ∃ B : ℝ, ∀ x ∈ Λ ∩ imaginarySlice ⁻¹' D, ‖A T x - f T (imaginarySlice x)‖ ≤ B := by
        obtain ⟨B, ε, _, _, h⟩ := hbound δ hδ Λ hΛ
        exact ⟨B * Real.exp (-ε * ‖eT T‖), by rw [hDU]; exact h T hT hs⟩
      obtain ⟨ω₀, W, hW⟩ := exists_holomorphic_extension_of_generic_comparison hD hDc
        (hf T (hreg hT)).1 (hDU.symm ▸ hUd) (hf T (hreg hT)).2.1 (hA T (hreg hT)).1 hB
      exact ⟨ω₀, W, fun _ => hW⟩
    · exact ⟨fun _ => 0, ∅, fun h => (hT h).elim⟩
  choose ω₀ W hω using hext
  let factor (z : Z) (s : Fin n → ℂ) := a z s * starRingEnd ℂ (b z)
  let ex (x : Fin n → ℝ) (z : Z) (Q : Idx) := (e₀ x Q).scale (factor z (imaginarySlice x))
  let omegaExt (T : V fam.T) (z : Z) (s : Fin n → ℂ) := factor z s * ω₀ T s
  refine ⟨R, ex, omegaExt, fun T _ => W T, hR₀R, hR, hUo, hUd, ?_, ?_, ?_⟩
  · intro x hx z
    obtain ⟨hEa, hΦb, _⟩ := (hcentral z).2 x
    exact ⟨fam.weakPairingCentralTransfer hK rho hsmooth hcalc _ _ _ (hexp x hx).1 z _ _ hEa hΦb,
      (hexp x hx).2⟩
  · intro T hT z
    obtain ⟨ho, hr, hh, he⟩ := hω T hT
    have hfac : Differentiable ℂ (factor z) := (hcentral z).1.mul_const _
    refine ⟨ho, hr, hfac.differentiableOn.mul hh, fun x hx => ?_⟩
    change factor z (imaginarySlice x) * ω₀ T (imaginarySlice x) = fam.regularizedPairing vol (ex x z) T
    rw [he ⟨hr (mem_range_self x), hUmem hx⟩, (hf T (hreg hT)).2.2 x hx]
    exact (fam.regularizedPairing_scale vol (e₀ x) (factor z (imaginarySlice x)) T).symm
  · intro δ hδ Λ hΛ
    obtain ⟨r, hr⟩ := hΛ.subset_ball (0 : Fin n → ℝ)
    obtain ⟨B, ε, hB, hε, hb⟩ := hbound δ hδ (ball 0 r) isBounded_ball
    refine ⟨B, ε, 0, hB, hε, fun T hT hs z x hx => ?_⟩
    obtain ⟨_, hW, hWc, he⟩ := hω T hT
    obtain ⟨hAc, hAi⟩ := hA T (hreg hT)
    obtain ⟨hEa, hΦb, hnorm⟩ := (hcentral z).2 x
    have h0 := norm_sub_le_of_dense_imaginary (hDU.symm ▸ hUd) hW hWc.continuousOn he hAc hr
      (by rw [hDU]; exact hb T hT hs) x hx
    refine ⟨?_, ?_⟩
    · rw [fam.truncatedPairingIntegrand_central_factor hEa hΦb]
      exact (hAi x).smul _
    · rw [fam.truncatedPairing_central_factor hK C T₀ T hEa hΦb]
      change ‖factor z (imaginarySlice x) * A T x - factor z (imaginarySlice x) * ω₀ T (imaginarySlice x)‖ ≤ _
      rw [← mul_sub, norm_mul, show ‖factor z (imaginarySlice x)‖ = 1 from hnorm, one_mul]
      exact h0.trans (le_mul_of_one_le_right (mul_nonneg hB.le (Real.exp_nonneg _)) (by simp))

end Langlands.Global.StandardParabolicFamily
