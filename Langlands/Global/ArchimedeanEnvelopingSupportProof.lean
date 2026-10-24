import Langlands.Global.ArchimedeanEnvelopingSupportStatement

/-! # Locality of the actual archimedean enveloping differential -/

noncomputable section
universe u
open scoped TensorProduct
open Set Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

theorem smoothDifferential_eq_zero_of_notMem_tsupport
    (X : RealLieAlgebra K n) (f : SmoothFunctions K n)
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) (hg : g ∉ tsupport f.val) :
    (smoothDifferential K n X f).val g = 0 := by
  have hzero : f.val =ᶠ[𝓝 g] 0 := notMem_tsupport_iff_eventuallyEq.mp hg
  have hc : ContinuousAt
      (fun M : ArchimedeanMatrix K n =>
        (archimedeanGLCoordinates K n).symm ((unitsChart K n).symm M))
      (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) :=
    (archimedeanGLCoordinates K n).symm.continuous.continuousAt.comp
      ((unitsChart K n).continuousAt_symm (by
        simp only [unitsChart, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
        exact ⟨_, rfl⟩))
  have hc' : Filter.Tendsto
      (fun M : ArchimedeanMatrix K n =>
        (archimedeanGLCoordinates K n).symm ((unitsChart K n).symm M))
      (𝓝 (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n)) (𝓝 g) := by
    simpa only [ContinuousAt, unitsChart,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv,
      ContinuousMulEquiv.symm_apply_apply] using hc
  have hext : coordinateExtension K n f =ᶠ[
      𝓝 (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n)] 0 :=
    hzero.comp_tendsto hc'
  rw [smoothDifferential_apply, hext.fderiv_eq]
  simp

theorem tsupport_smoothDifferential_subset (X : RealLieAlgebra K n)
    (f : SmoothFunctions K n) :
    tsupport (smoothDifferential K n X f).val ⊆ tsupport f.val := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro g hg
  by_contra hx
  exact hg (smoothDifferential_eq_zero_of_notMem_tsupport K n X f g hx)

theorem tsupport_complexSmoothLieAction_subset (X : ComplexLieAlgebra K n)
    (f : SmoothFunctions K n) :
    tsupport (complexSmoothLieAction K n X f).val ⊆ tsupport f.val := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simpa only [complexSmoothLieAction_tmul, LinearMap.smul_apply,
      Submodule.coe_smul, Pi.smul_apply] using!
      (tsupport_smul_subset_right (fun _ => z) (smoothDifferential K n X f).val).trans
        (tsupport_smoothDifferential_subset K n X f)
  | add X Y hX hY =>
    simpa only [map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply] using!
      (tsupport_add (complexSmoothLieAction K n X f).val
        (complexSmoothLieAction K n Y f).val).trans (Set.union_subset hX hY)

theorem envelopingSupport : EnvelopingSupportStatement K n := by
  intro a
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ComplexLieAlgebra K n)) a
  change ∀ f, tsupport
    (envelopingAction K n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t) f).val ⊆
      tsupport f.val
  induction t using TensorAlgebra.induction with
  | algebraMap z =>
    intro f
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
      LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul]
    exact tsupport_smul_subset_right (fun _ => z) f.val
  | ι X =>
    intro f
    change tsupport (envelopingAction K n (envelopingGenerator K n X) f).val ⊆ _
    rw [envelopingAction_generator]
    exact tsupport_complexSmoothLieAction_subset K n X f
  | mul x y hx hy =>
    intro f
    simp only [map_mul, Module.End.mul_apply]
    exact (hx _).trans (hy f)
  | add x y hx hy =>
    intro f
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add]
    exact (tsupport_add _ _).trans (Set.union_subset (hx f) (hy f))

theorem envelopingCompactSupport : EnvelopingCompactSupportStatement K n :=
  envelopingCompactSupport_of_support K n (envelopingSupport K n)

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    EnvelopingSupportStatement K n := @envelopingSupport

end Langlands.Global.ArchimedeanGL
