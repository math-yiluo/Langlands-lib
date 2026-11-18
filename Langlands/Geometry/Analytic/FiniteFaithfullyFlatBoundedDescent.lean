import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Proof
import Langlands.Geometry.Analytic.TateUniversal.Definitions
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Bounded descent along finite faithfully flat affinoid maps -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open scoped TensorProduct
open AffinoidPushout

private theorem mem_range_algebraMap_of_tensor_eq
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {b : B}
    (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) :
    b ∈ LinearMap.range (Algebra.linearMap A B) := by
  let V := LinearMap.range (Algebra.linearMap A B)
  let q : B →ₗ[A] B ⧸ V := V.mkQ
  have h1 : q 1 = 0 := by
    change 1 ∈ LinearMap.ker V.mkQ
    rw [Submodule.ker_mkQ]
    exact ⟨1, map_one (algebraMap A B)⟩
  have h := congrArg (TensorProduct.map (LinearMap.id : B →ₗ[A] B) q) hb
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, h1, TensorProduct.tmul_zero] at h
  have hq : q b = 0 := by
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B)
    simpa only [TensorProduct.mk_apply, TensorProduct.tmul_zero] using h.symm
  change b ∈ LinearMap.ker V.mkQ at hq
  rwa [Submodule.ker_mkQ] at hq

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The two actual completed self-pushout maps detect unique bounded descent. -/
def FiniteFaithfullyFlatBoundedDescentStatement : Prop :=
  ∀ {A B C : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K A B) (g : BoundedAlgHom K C B),
    f.IsFiniteBanach → f.toAlgHom.toRingHom.FaithfullyFlat →
    (leftMap f f).comp g = (rightMap f f).comp g →
    ∃! h : BoundedAlgHom K C A, f.comp h = g

theorem finiteFaithfullyFlatBoundedDescent :
    FiniteFaithfullyFlatBoundedDescentStatement K := by
  intro A B C f g hfinite hflat hg
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Module.FaithfullyFlat A B := hflat
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective A B
  have hcomparison := (finiteTensorComparison A B B f f hfinite).1
  have hRange : Set.range f = {b | leftMap f f b = rightMap f f b} := by
    ext b
    constructor
    · rintro ⟨a, rfl⟩
      exact congrArg (fun p : BoundedAlgHom K A (algebra f f) => p a) (condition f f)
    · intro hb
      have htensor : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b := by
        apply hcomparison
        change tensorComparison f f (tensorLeft f f b) =
          tensorComparison f f (tensorRight f f b)
        rw [tensorComparison_tensorLeft, tensorComparison_tensorRight]
        exact hb.symm
      exact mem_range_algebraMap_of_tensor_eq htensor
  have hClosed : IsClosed (Set.range f.toContinuousLinearMap) := by
    change IsClosed (Set.range f)
    rw [hRange]
    exact isClosed_eq (leftMap f f).continuous (rightMap f f).continuous
  obtain ⟨M, hM⟩ :=
    f.toContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range hf hClosed
  have hRangeG (c : C) : g c ∈ f.toAlgHom.range := by
    change g c ∈ Set.range f
    rw [hRange]
    exact congrArg (fun p : BoundedAlgHom K C (algebra f f) => p c) hg
  let e := AlgEquiv.ofInjective f.toAlgHom hf
  let lift := e.symm.toAlgHom.comp (g.toAlgHom.codRestrict f.toAlgHom.range hRangeG)
  have hlift (c : C) : f (lift c) = g c :=
    congrArg Subtype.val (e.apply_symm_apply ⟨g c, hRangeG c⟩)
  have hbounded : lift.toRingHom.IsBounded := by
    obtain ⟨N, hN, hbound⟩ := g.bounded
    refine ⟨(M : ℝ) * N + 1, by positivity, fun c => ?_⟩
    change ‖lift c‖ ≤ ((M : ℝ) * N + 1) * ‖c‖
    calc
      ‖lift c‖ ≤ (M : ℝ) * ‖f (lift c)‖ := hM.le_mul_norm (map_zero _) (lift c)
      _ = (M : ℝ) * ‖g c‖ := by rw [hlift c]
      _ ≤ (M : ℝ) * (N * ‖c‖) := mul_le_mul_of_nonneg_left (hbound c) M.coe_nonneg
      _ = (M : ℝ) * N * ‖c‖ := (mul_assoc _ _ _).symm
      _ ≤ ((M : ℝ) * N + 1) * ‖c‖ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg c)
  refine ⟨⟨lift, hbounded⟩, BoundedAlgHom.ext hlift, ?_⟩
  intro h hh
  apply BoundedAlgHom.ext
  intro c
  apply hf
  exact (congrArg (fun p : BoundedAlgHom K C B => p c) hh).trans (hlift c).symm

end Langlands.Analytic.PresentedAffinoidAlgebra
