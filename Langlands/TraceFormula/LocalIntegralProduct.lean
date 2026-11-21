import Langlands.TraceFormula.GeneralLinearBaseChangeLocal
import Langlands.Global.AdelicFunctoriality.IntegralLocalComparisonProof

/-! # The integral subgroups in the completed tensor comparison -/

noncomputable section

namespace Langlands.TraceFormula

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped NumberField TensorProduct FiniteExtension

universe u

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (v : Langlands.Global.FinitePlace K)

local notation "Oᵥ" => v.adicCompletionIntegers K
local notation "Kᵥ" => v.adicCompletion K
local notation "Eᵥ" => LocalBaseChangeAlgebra K L (Sum.inr v)

private def integralTensorToLocalAlgebra : 𝓞 L ⊗[𝓞 K] Oᵥ →+* Eᵥ :=
  (integralTensorTransport L v).toRingHom.comp
    (Algebra.TensorProduct.map (AlgHom.id (𝓞 K) (𝓞 L))
      (Algebra.algHom (𝓞 K) Oᵥ Kᵥ)).toRingHom

omit [NumberField L] in
private theorem integralTensorToLocalAlgebra_tmul (b : 𝓞 L) (a : Oᵥ) :
    integralTensorToLocalAlgebra K L v (b ⊗ₜ[𝓞 K] a) =
      (a : Kᵥ) ⊗ₜ[K] algebraMap (𝓞 L) L b := by
  change integralTensorTransport L v
    (Algebra.TensorProduct.map (AlgHom.id (𝓞 K) (𝓞 L))
      (Algebra.algHom (𝓞 K) Oᵥ Kᵥ) (b ⊗ₜ[𝓞 K] a)) = _
  rw [Algebra.TensorProduct.map_tmul]
  exact integralTensorTransport_tmul L v b a

omit [NumberField L] in
private theorem integralTensorToLocalAlgebra_eq_transport (x : 𝓞 L ⊗[𝓞 K] Oᵥ) :
    integralTensorToLocalAlgebra K L v x =
      integralTensorTransport L v (integralTensorInclusion L v x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b a =>
    simp [integralTensorToLocalAlgebra_tmul]
    rfl
  | add x y hx hy =>
    simp [hx, hy]
    rfl

omit [NumberField L] in
private theorem localIntegers_eq_range :
    localIntegers K L v = (integralTensorToLocalAlgebra K L v).range := by
  apply le_antisymm
  · apply Subring.closure_le.mpr
    rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · refine ⟨(1 : 𝓞 L) ⊗ₜ[𝓞 K] a, ?_⟩
      rw [integralTensorToLocalAlgebra_tmul, map_one]
      rfl
    · refine ⟨b ⊗ₜ[𝓞 K] (1 : Oᵥ), ?_⟩
      rw [integralTensorToLocalAlgebra_tmul]
      rfl
  · rintro x ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul b a =>
      have ha : ((a : Kᵥ) ⊗ₜ[K] (1 : L) : Eᵥ) ∈ localIntegers K L v :=
        Subring.subset_closure (Or.inl ⟨a, rfl⟩)
      have hb : ((1 : Kᵥ) ⊗ₜ[K] algebraMap (𝓞 L) L b : Eᵥ) ∈ localIntegers K L v :=
        Subring.subset_closure (Or.inr ⟨b, rfl⟩)
      have hmul := (localIntegers K L v).mul_mem ha hb
      change ((a : Kᵥ) ⊗ₜ[K] (1 : L)) *
        ((1 : Kᵥ) ⊗ₜ[K] algebraMap (𝓞 L) L b) ∈ localIntegers K L v at hmul
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at hmul
      rw [integralTensorToLocalAlgebra_tmul]
      exact hmul
    | add x y hx hy =>
      rw [map_add]
      exact (localIntegers K L v).add_mem hx hy

/-- The actual integral order on the completed tensor algebra corresponds to the
product of the valuation rings at the places above `v`. -/
theorem finiteTensorMap_image_localIntegers :
    (finiteTensorMap (L := L) v) '' (localIntegers K L v : Set Eᵥ) =
      Set.pi Set.univ (fun q : FinitePlacesAbove L v ↦
        (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L))) := by
  have h := (integralLocalTensorComparison K L v).2.1
  let g : Eᵥ → (q : FinitePlacesAbove L v) → q.1.adicCompletion L := finiteTensorMap v
  change g '' (localIntegers K L v : Set Eᵥ) = _
  rw [localIntegers_eq_range, RingHom.coe_range, ← Set.range_comp, ← h]
  congr 1
  funext z
  exact (congrArg g (integralTensorToLocalAlgebra_eq_transport K L v z)).trans
      (finiteTensorMap_integralTensorTransport L v _)

theorem mem_localIntegers_iff_finiteTensorCoordinates (x : Eᵥ) :
    x ∈ localIntegers K L v ↔
      ∀ q : FinitePlacesAbove L v, finiteTensorMap (L := L) v x q ∈
        (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L)) := by
  have hf : Function.Injective (finiteTensorMap (L := L) v) :=
    ((completedTensorComparison K L).1 v).1
  have h : finiteTensorMap (L := L) v x ∈
      (finiteTensorMap (L := L) v) '' (localIntegers K L v : Set Eᵥ) ↔
      x ∈ localIntegers K L v := hf.mem_set_image
  rw [finiteTensorMap_image_localIntegers K L v] at h
  simpa only [Set.mem_pi, Set.mem_univ, true_implies] using h.symm

/-- Integral matrix membership is equivalent to integral membership in all the
completion coordinates. -/
theorem mem_integralSubgroup_localIntegers_iff (n : ℕ) (g : GeneralLinear n Eᵥ) :
    g ∈ GeneralLinearGroup.integralSubgroup (Fin n) (localIntegers K L v) ↔
      ∀ q : FinitePlacesAbove L v,
        Matrix.GeneralLinearGroup.map
            ((Pi.evalRingHom (fun q : FinitePlacesAbove L v ↦ q.1.adicCompletion L) q).comp
              (finiteTensorMap (L := L) v).toRingHom) g ∈
          GeneralLinearGroup.integralSubgroup (Fin n) (q.1.adicCompletionIntegers L).toSubring := by
  simp only [GeneralLinearGroup.mem_integralSubgroup]
  constructor
  · intro h q
    exact ⟨fun i j ↦ (mem_localIntegers_iff_finiteTensorCoordinates K L v (g i j)).mp
        (h.1 i j) q,
      fun i j ↦ (mem_localIntegers_iff_finiteTensorCoordinates K L v (g⁻¹ i j)).mp
        (h.2 i j) q⟩
  · intro h
    exact ⟨fun i j ↦ (mem_localIntegers_iff_finiteTensorCoordinates K L v (g i j)).mpr
        (fun q ↦ (h q).1 i j),
      fun i j ↦ (mem_localIntegers_iff_finiteTensorCoordinates K L v (g⁻¹ i j)).mpr
        (fun q ↦ (h q).2 i j)⟩

/-- The integral order used by the adelic `GL_n` comparison maps to the product
of the valuation rings over a finite place. -/
def LocalIntegralProductStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (v : Langlands.Global.FinitePlace K),
      (finiteTensorMap (L := L) v) ''
        (localIntegers K L v : Set (LocalBaseChangeAlgebra K L (.inr v))) =
        Set.pi Set.univ (fun q : FinitePlacesAbove L v ↦
          (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L)))

theorem localIntegralProduct : LocalIntegralProductStatement := by
  intro K L _ _ _ _ _ v
  exact finiteTensorMap_image_localIntegers K L v

end Langlands.TraceFormula
