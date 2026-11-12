import Langlands.HarmonicAnalysis.Distribution.RenardConvolutionStatements
import Langlands.Representation.Hecke.CommonInvarianceProof

/-! # Regularity of the actual distribution convolution kernels -/

noncomputable section

open Filter Topology
open scoped Pointwise

namespace Langlands.HarmonicAnalysis.Distribution

universe uX uY uG

section Pairing

variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]

/-- Equality on the actual support is sufficient for extended evaluation. -/
theorem compactSupportPairing_congr (T : compactlySupported (X := Y))
    {f g : LocallyConstant Y ℂ}
    (h : ∀ y ∈ support (T : Distribution Y), f y = g y) :
    compactSupportPairing T f = compactSupportPairing T g := by
  have he : restrictLocallyConstantCompact T.property f =
      restrictLocallyConstantCompact T.property g := by
    ext y
    exact h y.val y.property
  rw [compactSupportPairing_apply, compactSupportPairing_apply, he]

omit [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y] in
/-- A locally constant kernel is uniformly constant near a parameter when the
other variable is restricted to a compact set. -/
theorem locallyConstant_on_compact_parameter (h : LocallyConstant (X × Y) ℂ)
    {K : Set Y} (hK : IsCompact K) :
    IsLocallyConstant (fun x : X => fun y : K => h (x, y.val)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have he : ∀ᶠ x' in 𝓝 x, ∀ y ∈ K, h (x', y) = h (x, y) := by
    apply hK.eventually_forall_of_forall_eventually
    intro y _
    have h1 := h.isLocallyConstant.eventually_eq (x, y)
    have h2 : ∀ᶠ p : X × Y in 𝓝 (x, y), h (x, p.2) = h (x, y) :=
      (h.isLocallyConstant.comp_continuous
        (show Continuous (fun p : X × Y => (x, p.2)) from
          continuous_const.prodMk continuous_snd)).eventually_eq (x, y)
    filter_upwards [h1, h2] with p hp hq
    exact hp.trans hq.symm
  filter_upwards [he] with x' hx'
  funext y
  exact hx' y.val y.property

/-- Applying a compact distribution in the second variable preserves local
constancy, without imposing compactness on the parameter space. -/
def compactPartial (S : compactlySupported (X := Y))
    (h : LocallyConstant (X × Y) ℂ) : LocallyConstant X ℂ :=
  ⟨fun x => compactSupportPairing S
      ⟨fun y => h (x, y), h.isLocallyConstant.comp_continuous
        (continuous_const.prodMk continuous_id)⟩, by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [(locallyConstant_on_compact_parameter h S.property).eventually_eq x]
      with x' hx'
    apply compactSupportPairing_congr
    intro y hy
    exact congrFun hx' ⟨y, hy⟩⟩

@[simp] theorem compactPartial_apply (S : compactlySupported (X := Y))
    (h : LocallyConstant (X × Y) ℂ) (x : X) :
    compactPartial S h x = compactSupportPairing S
      ⟨fun y => h (x, y), h.isLocallyConstant.comp_continuous
        (continuous_const.prodMk continuous_id)⟩ := rfl

end Pairing

section Group

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- The test kernel is literally evaluation on `y ↦ f(y⁻¹x)`. -/
theorem leftConvolveSmooth_eq_test (T : compactlySupported (X := G))
    (f : SchwartzBruhat G) :
    leftConvolveSmooth T ⟨(f : G → ℂ), f.locallyConstant⟩ =
      leftConvolveTest (T : Distribution G) f := by
  funext x
  unfold leftConvolveSmooth leftConvolveTest
  apply compactSupportPairing_eq_of_agrees
  intro y _
  simp

/-- The right test kernel is literally evaluation on `y ↦ f(xy⁻¹)`. -/
theorem rightConvolveSmooth_eq_test (T : compactlySupported (X := G))
    (f : SchwartzBruhat G) :
    rightConvolveSmooth ⟨(f : G → ℂ), f.locallyConstant⟩ T =
      rightConvolveTest f (T : Distribution G) := by
  funext x
  unfold rightConvolveSmooth rightConvolveTest
  apply compactSupportPairing_eq_of_agrees
  intro y _
  simp

theorem leftConvolveSmooth_locallyConstant (T : compactlySupported (X := G))
    (f : LocallyConstant G ℂ) : IsLocallyConstant (leftConvolveSmooth T f) :=
  (compactPartial T ⟨fun p : G × G => f (p.2⁻¹ * p.1),
    f.isLocallyConstant.comp_continuous (continuous_snd.inv.mul continuous_fst)⟩).isLocallyConstant

theorem rightConvolveSmooth_locallyConstant (T : compactlySupported (X := G))
    (f : LocallyConstant G ℂ) : IsLocallyConstant (rightConvolveSmooth f T) :=
  (compactPartial T ⟨fun p : G × G => f (p.1 * p.2⁻¹),
    f.isLocallyConstant.comp_continuous (continuous_fst.mul continuous_snd.inv)⟩).isLocallyConstant

theorem leftConvolveTest_locallyConstant (D : Distribution G) (f : SchwartzBruhat G) :
    IsLocallyConstant (leftConvolveTest D f) := by
  classical
  obtain ⟨K, _, _, hK⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  have hf := hK f (by simp)
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{z : G | x⁻¹ * z ∈ K}, K.isOpen.preimage
    (continuous_const.mul continuous_id), by simp, ?_⟩
  intro z hz
  unfold leftConvolveTest
  congr 1
  ext y
  simp only [Hecke.TestFunction.leftTranslate_apply, Hecke.TestFunction.inversion_apply,
    mul_inv_rev, inv_inv]
  have he : y⁻¹ * z = (y⁻¹ * x) * (x⁻¹ * z) := by simp [mul_assoc]
  rw [he]
  exact hf.2 ⟨x⁻¹ * z, hz⟩ (y⁻¹ * x)

theorem rightConvolveTest_locallyConstant (D : Distribution G) (f : SchwartzBruhat G) :
    IsLocallyConstant (rightConvolveTest f D) := by
  classical
  obtain ⟨K, _, _, hK⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  have hf := hK f (by simp)
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{z : G | z * x⁻¹ ∈ K}, K.isOpen.preimage
    (continuous_id.mul continuous_const), by simp, ?_⟩
  intro z hz
  unfold rightConvolveTest
  congr 1
  ext y
  simp only [Hecke.TestFunction.rightTranslate_apply, Hecke.TestFunction.inversion_apply,
    mul_inv_rev, inv_inv]
  have he : z * y⁻¹ = (z * x⁻¹) * (x * y⁻¹) := by simp [mul_assoc]
  rw [he]
  exact hf.1 ⟨z * x⁻¹, hz⟩ (x * y⁻¹)

theorem leftConvolveTest_hasCompactSupport (T : compactlySupported (X := G))
    (f : SchwartzBruhat G) : HasCompactSupport (leftConvolveTest (T : Distribution G) f) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (T.property.mul (Hecke.TestFunction.isCompact_support f))
  intro x hx
  by_contra hn
  apply hx
  apply mem_supportedOn_support (T : Distribution G)
  intro y hy
  simp only [Hecke.TestFunction.leftTranslate_apply, Hecke.TestFunction.inversion_apply,
    mul_inv_rev, inv_inv]
  by_contra hf
  exact hn ⟨y, hy, y⁻¹ * x, hf, by simp⟩

theorem rightConvolveTest_hasCompactSupport (T : compactlySupported (X := G))
    (f : SchwartzBruhat G) : HasCompactSupport (rightConvolveTest f (T : Distribution G)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((Hecke.TestFunction.isCompact_support f).mul T.property)
  intro x hx
  by_contra hn
  apply hx
  apply mem_supportedOn_support (T : Distribution G)
  intro y hy
  simp only [Hecke.TestFunction.rightTranslate_apply, Hecke.TestFunction.inversion_apply,
    mul_inv_rev, inv_inv]
  by_contra hf
  exact hn ⟨x * y⁻¹, hf, y, hy, by simp⟩

end Group

namespace RenardConvolution

theorem regularity : RegularityStatement.{uG} := by
  intro G _ _ _ _ _ _
  exact ⟨fun D f => ⟨leftConvolveTest_locallyConstant D f,
      rightConvolveTest_locallyConstant D f⟩,
    fun T f => ⟨leftConvolveSmooth_locallyConstant T f,
      rightConvolveSmooth_locallyConstant T f⟩,
    fun T f => ⟨leftConvolveTest_hasCompactSupport T f,
      rightConvolveTest_hasCompactSupport T f,
      leftConvolveSmooth_eq_test T f, rightConvolveSmooth_eq_test T f⟩⟩

theorem evaluation : EvaluationStatement.{uG} := by
  intro G _ _ _ _ _ _ D f
  constructor <;> change D f = D _ <;> congr 1 <;> ext x <;> simp

end RenardConvolution
end Langlands.HarmonicAnalysis.Distribution
