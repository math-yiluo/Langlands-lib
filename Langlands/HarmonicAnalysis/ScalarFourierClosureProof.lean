import Langlands.HarmonicAnalysis.ScalarFourierClosureStatement
import Langlands.HarmonicAnalysis.SelfDualSigmaFiniteProof
import Langlands.HarmonicAnalysis.CompactOpenAnnihilatorProof
import Langlands.Representation.Hecke.CommonInvarianceProof
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Group.Integral

noncomputable section

open MeasureTheory Topology Filter Set

namespace Langlands.HarmonicAnalysis

universe u

section ScalarFourier

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F] [T2Space F]
  [TotallyDisconnectedSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
private theorem exists_compactOpenAdd_invariant (f : SchwartzBruhat F) :
    ∃ H : OpenAddSubgroup F, IsCompact (H : Set F) ∧
      ∀ h ∈ H, ∀ x, f (h + x) = f x := by
  classical
  let : T2Space (Multiplicative F) := ‹T2Space F›
  let : LocallyCompactSpace (Multiplicative F) := ‹LocallyCompactSpace F›
  let : TotallyDisconnectedSpace (Multiplicative F) := ‹TotallyDisconnectedSpace F›
  let fm : SchwartzBruhat (Multiplicative F) :=
    ⟨fun x => f x.toAdd, f.property⟩
  obtain ⟨K, _, hKc, hKf⟩ :=
    Hecke.TestFunction.commonCompactOpenBiInvariance (Multiplicative F) {fm} ⊤
  let H : OpenAddSubgroup F :=
    { carrier := {x | Multiplicative.ofAdd x ∈ K}
      zero_mem' := K.one_mem
      add_mem' := fun hx hy => K.mul_mem hx hy
      neg_mem' := fun hx => K.inv_mem hx
      isOpen' := K.isOpen }
  refine ⟨H, hKc, ?_⟩
  intro h hh x
  exact (hKf fm (Finset.mem_singleton_self fm)).1 ⟨Multiplicative.ofAdd h, hh⟩
    (Multiplicative.ofAdd x)

omit [MeasurableSpace F] [BorelSpace F] in
private theorem character_locallyConstant (ψ : UnitaryAdditiveCharacter F) :
    IsLocallyConstant ψ.complex := by
  classical
  have harc : (1 : Circle) ∈ Circle.centeredArc (Real.pi / 2) := by
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  have hn : {x : F | ψ x ∈ Circle.centeredArc (Real.pi / 2)} ∈ 𝓝 0 :=
    ψ.continuous_toFun.continuousAt.preimage_mem_nhds
      ((Circle.isOpen_centeredArc _).mem_nhds (by simpa using harc))
  obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds (0 : F)
  obtain ⟨V, hVcl, hV0, hVsub⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.mp (inter_mem hn hCn)
  have hVc : IsCompact V :=
    hCc.of_isClosed_subset hVcl.isClosed (fun _ hx => (hVsub hx).2)
  let f : SchwartzBruhat F := Hecke.TestFunction.characteristic hVcl hVc
  obtain ⟨H, _, hHf⟩ := exists_compactOpenAdd_invariant f
  have hHarc : ∀ x ∈ H, ψ x ∈ Circle.centeredArc (Real.pi / 2) := by
    intro x hx
    have he : f x = f 0 := by simpa using hHf x hx 0
    have hxV : x ∈ V := by
      by_contra hxV
      simp [f, Hecke.TestFunction.characteristic_apply, hxV, hV0] at he
    exact (hVsub hxV).1
  have hHψ : ∀ x ∈ H, ψ.complex x = 1 := by
    intro x hx
    have he : ψ x = 1 := by
      apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
      intro n _
      rw [← AddChar.map_nsmul_eq_pow]
      exact hHarc (n • x) (H.nsmul_mem hx n)
    simp only [UnitaryAdditiveCharacter.complex_apply, he, Circle.coe_one]
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hnH : ∀ᶠ y in 𝓝 x, y - x ∈ H :=
    (continuous_id.sub continuous_const).continuousAt.eventually
      (by change (H : Set F) ∈ 𝓝 (x - x); simpa only [sub_self] using H.mem_nhds_zero)
  filter_upwards [hnH] with y hy
  calc
    ψ.complex y = ψ.complex ((y - x) + x) := by rw [sub_add_cancel]
    _ = ψ.complex (y - x) * ψ.complex x := ψ.complex.map_add_eq_mul _ _
    _ = ψ.complex x := by rw [hHψ _ hy, one_mul]

omit [BorelSpace F] in
private theorem fourierIntegral_locallyConstant
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (f : SchwartzBruhat F) :
    IsLocallyConstant (fourierIntegral ψ μ f) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have h : ∀ᶠ z in 𝓝 y, ∀ x ∈ tsupport f,
      ψ.complex (x * z) = ψ.complex (x * y) := by
    apply f.hasCompactSupport.eventually_forall_of_forall_eventually
    intro x _
    have h₁ := ((character_locallyConstant ψ).comp_continuous
      (continuous_snd.mul continuous_fst)).eventually_eq (y, x)
    have h₂ := ((character_locallyConstant ψ).comp_continuous
      (continuous_snd.mul (continuous_const (y := y)))).eventually_eq (y, x)
    filter_upwards [h₁, h₂] with p hp hpx
    exact hp.trans hpx.symm
  filter_upwards [h] with z hz
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change ψ.complex (x * z) * f x = ψ.complex (x * y) * f x
    by_cases hx : x ∈ tsupport f
    · rw [hz x hx]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]

omit [LocallyCompactSpace F] [T2Space F] [TotallyDisconnectedSpace F] in
private theorem fourierIntegral_eq_zero_of_translation
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (f : SchwartzBruhat F) (h y : F)
    (hf : ∀ x, f (h + x) = f x) (hψ : ψ.complex (h * y) ≠ 1) :
    fourierIntegral ψ μ f y = 0 := by
  have he : ψ.complex (h * y) * fourierIntegral ψ μ f y =
      fourierIntegral ψ μ f y := by
    calc
      ψ.complex (h * y) * fourierIntegral ψ μ f y =
          ∫ x, ψ.complex (h * y) * (ψ.complex (x * y) * f x) ∂μ.measure :=
        (integral_const_mul _ _).symm
      _ = ∫ x, ψ.complex ((h + x) * y) * f (h + x) ∂μ.measure := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          change ψ.complex (h * y) * (ψ.complex (x * y) * f x) =
            ψ.complex ((h + x) * y) * f (h + x)
          rw [add_mul, ψ.complex.map_add_eq_mul, hf, mul_assoc]
      _ = fourierIntegral ψ μ f y :=
        integral_add_left_eq_self (fun x => ψ.complex (x * y) * f x) h
  by_contra hfzero
  exact hψ ((mul_eq_right₀ hfzero).mp he)

private theorem fourierIntegral_hasCompactSupport
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (hcompact : ∀ H : OpenAddSubgroup F, IsCompact (H : Set F) →
      IsCompact {y : F | ∀ x ∈ H, ψ.complex (x * y) = 1})
    (f : SchwartzBruhat F) :
    HasCompactSupport (fourierIntegral ψ μ f) := by
  obtain ⟨H, hHc, hHf⟩ := exists_compactOpenAdd_invariant f
  apply (hcompact H hHc).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (hcompact H hHc).isClosed
  intro y hy x hx
  by_contra hψ
  exact hy (fourierIntegral_eq_zero_of_translation ψ μ f x y (hHf x hx) hψ)

/-- Compactness of compact-open annihilators suffices for scalar Fourier
closure on Schwartz–Bruhat functions. -/
theorem scalarFourierClosed_of_compactAnnihilator
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (hcompact : ∀ H : OpenAddSubgroup F, IsCompact (H : Set F) →
      IsCompact {y : F | ∀ x ∈ H, ψ.complex (x * y) = 1}) :
    ∀ f : SchwartzBruhat F, ∃ g : SchwartzBruhat F,
      ∀ y, g y = fourierIntegral ψ μ f y := by
  intro f
  exact ⟨⟨fourierIntegral ψ μ f,
    fourierIntegral_locallyConstant ψ μ f,
    fourierIntegral_hasCompactSupport ψ μ hcompact f⟩, fun _ => rfl⟩

end ScalarFourier

/-- Scalar self-duality implies sigma-finiteness and preserves the
Schwartz–Bruhat test space under the actual Fourier integral. -/
theorem scalarFourierClosure : ScalarFourierClosureStatement.{u} := by
  intro F _ _ _ _ _ _ _ _ ψ μ hself
  exact ⟨selfDualSigmaFinite F ψ μ hself,
    scalarFourierClosed_of_compactAnnihilator ψ μ
      (compactOpenAnnihilator F ψ μ hself)⟩

end Langlands.HarmonicAnalysis
