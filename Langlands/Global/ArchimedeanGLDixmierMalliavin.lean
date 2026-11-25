import Langlands.Global.ArchimedeanConvolution
import Langlands.Representation.Archimedean.DixmierMalliavin
import Mathlib.RingTheory.TotallySplit

/-!
# The Dixmier–Malliavin theorem for `GL_n` of the infinite adeles

`Langlands.Global.ArchimedeanGL.SmoothCompactKernel.exists_eq_sum_convolution`: on
`InfiniteAdelicGL K n = GL_n(F_∞)` with the Library's smooth structure (smoothness through
`archimedeanGLCoordinates` in the units of `ArchimedeanMatrix K n`), every
`κ : SmoothCompactKernel K n` is a finite sum of convolutions `φᵢ ⋆ ψᵢ` of such kernels for a given
left Haar measure, with `φᵢ` supported in a prescribed neighbourhood of `1` and `ψᵢ` supported in
the support of `κ`.

It is `Langlands.Archimedean.exists_eq_sum_gardingKernelConvolution_units` for the units of
`ArchimedeanMatrix K n`, transported by `archimedeanGLCoordinates` with
`Langlands.Hecke.convolutionIntegral_comp_continuousMulEquiv`.
-/

noncomputable section

universe u

open MeasureTheory Set Filter Topology
open scoped Classical Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.ArchimedeanGL

-- The matrix norm and product topology are definitionally compatible, but
-- resolving the units charts needs reduction through the normed-ring instances.
set_option backward.isDefEq.respectTransparency false

/-- **Dixmier–Malliavin for `GL_n(F_∞)`** in the Library's completion coordinates: every smooth
compactly supported kernel `κ` on `InfiniteAdelicGL K n` is a finite sum
`κ(g) = ∑ᵢ ∫ φᵢ(y) ψᵢ(y⁻¹ g) dμ(y)` of convolutions of smooth compactly supported kernels, for any
left Haar measure `μ`, with `φᵢ` supported in a prescribed neighbourhood `U` of `1` and `ψᵢ` in the
support of `κ`. Transport of the units case through `archimedeanGLCoordinates`. -/
theorem SmoothCompactKernel.exists_eq_sum_convolution
    (K : Type u) [Field K] [NumberField K] (n : ℕ)
    [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
    (μ : Measure (InfiniteAdelicGL K n)) [μ.IsHaarMeasure]
    {U : Set (InfiniteAdelicGL K n)} (hU : U ∈ 𝓝 1) (κ : SmoothCompactKernel K n) :
    ∃ (m : ℕ) (φ ψ : Fin m → SmoothCompactKernel K n),
      (∀ i, tsupport (φ i).val.val ⊆ U ∧ tsupport (ψ i).val.val ⊆ tsupport κ.val.val) ∧
      ∀ g, κ.val.val g = ∑ i, ∫ y, (φ i).val.val y * (ψ i).val.val (y⁻¹ * g) ∂μ := by
  set e := archimedeanGLCoordinates K n
  let _ : MeasurableSpace (ArchimedeanGL K n) := borel _
  have : BorelSpace (ArchimedeanGL K n) := ⟨rfl⟩
  have : (μ.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ e
  let κ' : Archimedean.smoothCompactKernels (ArchimedeanMatrix K n) (ArchimedeanGL K n) :=
    ⟨κ.val.val ∘ e.symm, κ.val.property, κ.property.comp_homeomorph e.symm.toHomeomorph⟩
  have hU' : e.symm ⁻¹' U ∈ 𝓝 (1 : ArchimedeanGL K n) :=
    (e.symm.continuous.continuousAt (x := 1)).preimage_mem_nhds (by simpa using hU)
  obtain ⟨m, φ', ψ', hsupp, hsum⟩ :=
    Archimedean.exists_eq_sum_gardingKernelConvolution_units (μ.map e) hU' κ'
  have hsmooth : ∀ u : Archimedean.smoothCompactKernels (ArchimedeanMatrix K n)
      (ArchimedeanGL K n), u.val ∘ e ∈ smoothFunctions K n := by
    intro u
    change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞ (fun x => u.val (e (e.symm x)))
    simpa using u.property.1
  let lift : Archimedean.smoothCompactKernels (ArchimedeanMatrix K n) (ArchimedeanGL K n) →
      SmoothCompactKernel K n := fun u =>
    ⟨⟨u.val ∘ e, hsmooth u⟩, u.property.2.comp_homeomorph e.toHomeomorph⟩
  have htsupp : ∀ u : ArchimedeanGL K n → ℂ, tsupport (u ∘ e) = e ⁻¹' tsupport u := fun u =>
    tsupport_comp_eq_preimage u e.toHomeomorph
  refine ⟨m, fun i => lift (φ' i), fun i => lift (ψ' i), fun i => ⟨?_, ?_⟩, fun g => ?_⟩
  · change tsupport ((φ' i).val ∘ e) ⊆ U
    rw [htsupp]
    intro x hx
    simpa using (hsupp i).1 hx
  · change tsupport ((ψ' i).val ∘ e) ⊆ tsupport κ.val.val
    rw [htsupp]
    intro x hx
    have h1 := (hsupp i).2 hx
    have h2 : tsupport (κ.val.val ∘ e.symm) = e.symm ⁻¹' tsupport κ.val.val :=
      tsupport_comp_eq_preimage κ.val.val e.symm.toHomeomorph
    change e x ∈ tsupport (κ.val.val ∘ e.symm) at h1
    rw [h2] at h1
    simpa using h1
  · have hg : κ.val.val g = κ'.val (e g) := by simp [κ']
    rw [hg, hsum, Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Archimedean.gardingKernelConvolution_apply]
    have := Hecke.convolutionIntegral_comp_continuousMulEquiv e μ (φ' i).val (ψ' i).val g
    rw [Hecke.convolutionIntegral, Hecke.convolutionIntegral] at this
    exact this.symm

end Langlands.Global.ArchimedeanGL
