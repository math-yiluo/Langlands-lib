import Langlands.Global.AdelicCharacteristicRegionCompact
import Langlands.Global.AdelicCharacteristicTruncationExhaustion
import Langlands.Global.AdelicEisensteinTemperedTruncationEstimate
import Langlands.Global.ImaginaryAxisLocalDivision
import Langlands.Global.LeftCosetUnfoldingBound

/-! # Compact spectral tests of characteristic truncated pairings -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter MeasureTheory Set
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints AdelicSiegelFactors ImaginaryAxis

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)
  (C : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅)
    (Standard.leviScheme fam.i fam.ν ∅)) (T₀ : V fam.T)

local notation "A" => AdelicGroupPoints F G
local notation "Y" => NormOneRationalQuotient F G
local notation "H" => normOneSubgroup F G
local notation "Γ" => rationalNormOneSubgroup F G
local notation "μ" => normOneRationalQuotientHaarMeasure F G

private theorem centralPoint_one : fam.centralPoint 1 = 1 := by
  simp [centralPoint]

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem normOne_invariant_of_rationalInvariant {f : A → ℂ}
    (hf : ∀ r ∈ rationalSubgroup F G, ∀ g : A, f (r * g) = f g) :
    ∀ r ∈ Γ, ∀ g : H, f (↑(r * g)) = f (g : A) := by
  intro r hr g
  apply hf _ _ g
  obtain ⟨a, ha⟩ := hr
  exact ⟨a, congrArg Subtype.val ha⟩

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem continuous_normOne_quotient_family {X : Type*} [TopologicalSpace X]
    {f : X → A → ℂ} (hf : Continuous fun z : X × A => f z.1 z.2)
    (hInv : ∀ x r, r ∈ rationalSubgroup F G → ∀ g : A, f x (r * g) = f x g) :
    Continuous fun z : X × Y => f z.1 (z.2.out : H).val := by
  have hq := (IsOpenQuotientMap.id (X := X)).prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)
  apply hq.continuous_comp_iff.mp
  change Continuous fun z : X × H => f z.1 ((LeftCosetSpace.mk Γ z.2).out : H).val
  have hout (x : X) (g : H) :
      f x ((LeftCosetSpace.mk Γ g).out : H).val = f x g.val :=
    LeftCosetSpace.apply_out_mk Γ (f := fun g : H => f x g.val)
      (normOne_invariant_of_rationalInvariant (hInv x)) g
  simp_rw [hout]
  exact hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

variable {σ : Type*} [Fintype σ] (spectral : Measure (σ → ℝ))
  [IsFiniteMeasureOnCompacts spectral] [SFinite spectral]

/-- Exchange a compact spectral test with the integral over a characteristic region.
The same compact product gives integrability of the tested truncated pairing. -/
theorem truncatedPairing_compactSpectralTest
    (hC : C.compactSubgroup = K) (hCov : ArthurTruncation.IsRationalCovering C)
    (Tp : V fam.T) {E : (σ → ℝ) → A → ℂ} {Φ : A → ℂ} {f : (σ → ℝ) → ℂ}
    (hE : Continuous fun z : (σ → ℝ) × A => E z.1 z.2)
    (hEInv : ∀ x r, r ∈ rationalSubgroup F G → ∀ g : A, E x (r * g) = E x g)
    (hΦ : Continuous Φ) (hΦInv : ∀ r ∈ rationalSubgroup F G, ∀ g : A, Φ (r * g) = Φ g)
    (hf : Continuous f) (hfs : HasCompactSupport f) :
    Integrable (fun x => f x * fam.truncatedPairing hK C T₀ Tp 1 (E x) Φ) spectral ∧
    (∫ x, f x * fam.truncatedPairing hK C T₀ Tp 1 (E x) Φ ∂spectral) =
      ∫ y in fam.truncationRegion hK C T₀ Tp,
        (∫ x, f x * E x (y.out : H).val ∂spectral) * starRingEnd ℂ (Φ (y.out : H).val) ∂μ := by
  let S := tsupport f
  let R := fam.truncationRegion hK C T₀ Tp
  let B (x : σ → ℝ) (y : Y) := f x * E x (y.out : H).val * starRingEnd ℂ (Φ (y.out : H).val)
  have hE' := continuous_normOne_quotient_family hE hEInv
  have hΦ' : Continuous fun y : Y => Φ (y.out : H).val := by
    rw [← (LeftCosetSpace.isOpenQuotientMap_mk Γ).continuous_comp_iff]
    change Continuous fun y : H => Φ ((LeftCosetSpace.mk Γ y).out : H).val
    have hout (g : H) : Φ ((LeftCosetSpace.mk Γ g).out : H).val = Φ g.val :=
      LeftCosetSpace.apply_out_mk Γ (f := fun g : H => Φ g.val)
        (normOne_invariant_of_rationalInvariant hΦInv) g
    simp_rw [hout]
    exact hΦ.comp continuous_subtype_val
  have hB : Continuous (Function.uncurry B) :=
    ((hf.comp continuous_fst).mul hE').mul (hΦ'.comp continuous_snd).star
  have hR : IsCompact R := ArthurTruncation.characteristicRegion_compact
    fam.connectedReductive fam.maximalSplit fam.coroots (fam.isIwasawaCompact_standardBot hK)
    fam.bijective_restrictToTorus_bot fam.generic C hC hCov T₀ Tp
  have hBInt : Integrable (Function.uncurry B) ((spectral.restrict S).prod (Measure.restrict μ R)) := by
    rw [Measure.prod_restrict]
    exact hB.continuousOn.integrableOn_compact (hfs.isCompact.prod hR)
  have hRight (x : σ → ℝ) :
      (∫ y in R, B x y ∂μ) = f x * fam.truncatedPairing hK C T₀ Tp 1 (E x) Φ := by
    unfold truncatedPairing truncatedPairingIntegrand centralTranslate
    simp only [fam.centralPoint_one, mul_one, B, mul_assoc, integral_const_mul, R]
  have hLeft (y : Y) :
      (∫ x in S, B x y ∂spectral) =
        (∫ x, f x * E x (y.out : H).val ∂spectral) * starRingEnd ℂ (Φ (y.out : H).val) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      simp [B, image_eq_zero_of_notMem_tsupport hx]), ← integral_mul_const]
  have htest : IntegrableOn (fun x => f x * fam.truncatedPairing hK C T₀ Tp 1 (E x) Φ) S spectral := by
    change Integrable _ (spectral.restrict S)
    convert hBInt.integral_prod_left using 1
    exact funext fun x => (hRight x).symm
  refine ⟨htest.integrable_of_forall_notMem_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]), ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])]
  simpa only [hLeft, hRight] using integral_integral_swap hBInt

variable {n m : ℕ} (u : (σ → ℝ) → (Fin n → ℝ))
  (eT : V fam.T ≃ₗ[ℝ] (Fin m → ℝ))

local notation "Δ" => ArthurTruncation.simpleFinset fam.ν fam.connectedReductive fam.maximalSplit

omit [NumberField F] in
private theorem truncationRayRegular {R : ℝ} {v : V fam.T}
    (hv : v ≠ 0) (hspan : v ∈ fam.coroots.realCorootSpan)
    (hpos : ∀ α ∈ simpleRelativeRoots fam.i fam.ν, 0 < eval fam.T α v) :
    ∃ δ > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      fam.IsRegularTruncationParameter R ((k : ℝ) • v) ∧
      ∀ α ∈ simpleRelativeRoots fam.i fam.ν,
        δ * ‖eT ((k : ℝ) • v)‖ ≤ eval fam.T α ((k : ℝ) • v) := by
  classical
  let values := insert 1 (Finset.image (fun α => eval fam.T α v) Δ)
  have hne : values.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let a := values.min' hne
  have hα (α) : α ∈ Δ ↔ α ∈ simpleRelativeRoots fam.i fam.ν :=
    ArthurTruncation.mem_simpleFinset fam.connectedReductive fam.maximalSplit
  have ha : 0 < a := by
    rcases Finset.mem_insert.mp (Finset.min'_mem values hne) with ha | ha
    · rw [show a = 1 from ha]
      exact zero_lt_one
    · obtain ⟨α, hαΔ, heq⟩ := Finset.mem_image.mp ha
      change eval fam.T α v = a at heq
      rw [← heq]
      exact hpos α ((hα α).mp hαΔ)
  have he : 0 < ‖eT v‖ := norm_pos_iff.mpr (fun h => hv (eT.map_eq_zero_iff.mp h))
  refine ⟨a / ‖eT v‖, div_pos ha he, ?_⟩
  have hRegular (α) (hαΔ : α ∈ Δ) :
      ∀ᶠ k : ℕ in atTop, R ≤ eval fam.T α ((k : ℝ) • v) := by
    simp only [map_smul, smul_eq_mul]
    exact ((tendsto_mul_const_atTop_of_pos (hpos α ((hα α).mp hαΔ))).mpr
      tendsto_natCast_atTop_atTop).eventually_ge_atTop R
  filter_upwards [(Filter.eventually_all_finset Δ).mpr hRegular] with k hk
  refine ⟨⟨Submodule.smul_mem _ _ hspan, fun α h => hk α ((hα α).mpr h)⟩, fun α h => ?_⟩
  have hle : a ≤ eval fam.T α v :=
    Finset.min'_le values _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ((hα α).mpr h)))
  rw [map_smul, map_smul, norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg k), smul_eq_mul,
    mul_comm (k : ℝ) ‖eT v‖, ← mul_assoc, div_mul_cancel₀ _ he.ne', mul_comm a]
  exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg k)

/-- Compact spectral testing commutes with the characteristic truncation limit.
An exponential comparison on bounded spectral sets gives the same limit for
the regularized pairing on the imaginary axis. -/
def CharacteristicSpectralTestLimitStatement : Prop :=
  C.compactSubgroup = K → ArthurTruncation.IsRationalCovering C →
  (∀ y : Y, ∃ Tp, y ∈ fam.truncationRegion hK C T₀ Tp) →
  Continuous u →
  ∀ (R : ℝ) (v : V fam.T), v ≠ 0 → v ∈ fam.coroots.realCorootSpan →
    (∀ α ∈ simpleRelativeRoots fam.i fam.ν, 0 < eval fam.T α v) →
    ∀ (E : (Fin n → ℝ) → A → ℂ) (Φ : A → ℂ)
      (ω : V fam.T → (Fin n → ℂ) → ℂ),
      (Continuous fun z : (Fin n → ℝ) × A => E z.1 z.2) →
      (∀ x r, r ∈ rationalSubgroup F G → ∀ g : A, E x (r * g) = E x g) →
      Continuous Φ → (∀ r ∈ rationalSubgroup F G, ∀ g : A, Φ (r * g) = Φ g) →
      (∀ T, fam.IsRegularTruncationParameter R T →
        Continuous fun x => ω T (imaginarySlice x)) →
      (∀ δ : ℝ, 0 < δ → ∀ Λ : Set (Fin n → ℝ), Bornology.IsBounded Λ →
        ∃ B ε : ℝ, 0 < B ∧ 0 < ε ∧
          ∀ T, fam.IsRegularTruncationParameter R T →
          (∀ α ∈ simpleRelativeRoots fam.i fam.ν, δ * ‖eT T‖ ≤ eval fam.T α T) →
          ∀ x ∈ Λ, ‖fam.truncatedPairing hK C T₀ T 1 (E x) Φ - ω T (imaginarySlice x)‖ ≤
            B * Real.exp (-ε * ‖eT T‖)) →
      ∀ f : (σ → ℝ) → ℂ, Continuous f → HasCompactSupport f →
        let pairing : Y → ℂ := fun y =>
          (∫ x, f x * E (u x) (y.out : H).val ∂spectral) * starRingEnd ℂ (Φ (y.out : H).val)
        Integrable pairing μ →
        let test : ℕ → (σ → ℝ) → ℂ := fun k x =>
          f x * ω ((k : ℝ) • v) (imaginarySlice (u x))
        (∀ᶠ k : ℕ in atTop, Integrable (test k) spectral) ∧
          Tendsto (fun k => ∫ x, test k x ∂spectral) atTop (𝓝 (∫ y, pairing y ∂μ))

theorem characteristicSpectralTestLimit :
    fam.CharacteristicSpectralTestLimitStatement hK C T₀ spectral u eT := by
  intro hC hCov hTotal hu R v hv hspan hpos E Φ ω hE hEInv hΦ hΦInv hω hEst f hf hfs
    pairing hPair test
  obtain ⟨δ, hδ, hReg⟩ := fam.truncationRayRegular eT hv hspan hpos (R := R)
  let S := tsupport f
  let d (ε : ℝ) (k : ℕ) := Real.exp (-ε * ‖eT ((k : ℝ) • v)‖)
  let testTruncated (k : ℕ) (x : σ → ℝ) :=
    f x * fam.truncatedPairing hK C T₀ ((k : ℝ) • v) 1 (E (u x)) Φ
  have hSwap (k : ℕ) : Integrable (testTruncated k) spectral ∧
      (∫ x, testTruncated k x ∂spectral) =
        ∫ y in fam.truncationRegion hK C T₀ ((k : ℝ) • v), pairing y ∂μ :=
    fam.truncatedPairing_compactSpectralTest hK C T₀ spectral hC hCov ((k : ℝ) • v)
      (hE.comp ((hu.comp continuous_fst).prodMk continuous_snd))
      (fun x => hEInv (u x)) hΦ hΦInv hf hfs
  have hTrun : Tendsto (fun k : ℕ => ∫ x, testTruncated k x ∂spectral) atTop
      (𝓝 (∫ y, pairing y ∂μ)) := by
    have hExh := ArthurTruncation.characteristicIntegralExhaustion
      fam.connectedReductive fam.maximalSplit fam.coroots (fam.isIwasawaCompact_standardBot hK)
      fam.bijective_restrictToTorus_bot C fam.generic T₀ v
      (fun α h => hpos α ((ArthurTruncation.mem_simpleFinset _ _).mp h)) hTotal
      (fun r => ArthurTruncation.measurableSet_characteristicRegion
        fam.connectedReductive fam.maximalSplit fam.coroots (fam.isIwasawaCompact_standardBot hK)
        fam.bijective_restrictToTorus_bot fam.generic C hC hCov T₀ (r • v))
      pairing hPair
    exact (hExh.comp tendsto_natCast_atTop_atTop).congr fun k => (hSwap k).2.symm
  have hTest : ∀ᶠ k : ℕ in atTop, Integrable (test k) spectral := hReg.mono fun k hk =>
    (hf.mul ((hω _ hk.1).comp hu)).integrable_of_hasCompactSupport
      (hfs.mul_right (f' := fun x => ω ((k : ℝ) • v) (imaginarySlice (u x))))
  refine ⟨hTest, ?_⟩
  obtain ⟨B, ε, hB, hε, hBound⟩ :=
    hEst δ hδ (u '' S) (hfs.isCompact.image hu).isBounded
  obtain ⟨M, hM⟩ := hfs.isCompact.bddAbove_image hf.norm.continuousOn
  have hd : Tendsto (d ε) atTop (𝓝 0) := by
    have he : 0 < ‖eT v‖ := norm_pos_iff.mpr (fun h => hv (eT.map_eq_zero_iff.mp h))
    have hNorm : Tendsto (fun k : ℕ => ‖eT ((k : ℝ) • v)‖) atTop atTop := by
      simpa only [map_smul, norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _)] using
        (tendsto_mul_const_atTop_of_pos he).mpr
          (tendsto_natCast_atTop_atTop (R := ℝ))
    exact Real.tendsto_exp_atBot.comp (hNorm.const_mul_atTop_of_neg (neg_neg_of_pos hε))
  have hDiff : Tendsto (fun k => (∫ x, testTruncated k x ∂spectral) -
      (∫ x, test k x ∂spectral)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun k => (M * (B * d ε k)) * spectral.real S) atTop (𝓝 0) by
        simpa only [mul_zero, zero_mul] using ((hd.const_mul B).const_mul M).mul_const
          (spectral.real S))
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [hReg, hTest] with k hreg htest
    rw [← integral_sub ((hSwap k).1) htest]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) (fun x hx => by
      simp [testTruncated, test, image_eq_zero_of_notMem_tsupport hx])]
    refine norm_setIntegral_le_of_norm_le_const hfs.isCompact.measure_lt_top fun x hx => ?_
    simp only [testTruncated, test, ← mul_sub, norm_mul]
    exact mul_le_mul (hM ⟨x, hx, rfl⟩)
      (hBound _ hreg.1 hreg.2 _ ⟨x, hx, rfl⟩) (norm_nonneg _)
      ((norm_nonneg _).trans (hM ⟨x, hx, rfl⟩))
  simpa only [sub_sub_cancel, sub_zero] using hTrun.sub hDiff

end Langlands.Global.StandardParabolicFamily
