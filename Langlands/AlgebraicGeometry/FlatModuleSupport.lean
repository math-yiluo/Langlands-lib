import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Supports under flat extension of scalars -/

universe u v w

open TensorProduct

namespace Langlands.AlgebraicGeometry.FlatModuleSupport

variable (B : Type u) (C : Type v) (M : Type w)
  [CommRing B] [CommRing C] [Algebra B C] [AddCommGroup M] [Module B M]

/-- Extension of scalars has support contained in the inverse image of support. -/
lemma support_tensor_subset :
    Module.support C (C ⊗[B] M) ⊆
      PrimeSpectrum.comap (algebraMap B C) ⁻¹' Module.support B M := by
  intro q hq
  have hspan : Submodule.span C {x : C ⊗[B] M | ∃ c m, c ⊗ₜ m = x} = ⊤ :=
    Submodule.span_eq_top_of_span_eq_top B C _ (TensorProduct.span_tmul_eq_top B C M)
  obtain ⟨_, ⟨c, m, rfl⟩, hm⟩ := (Module.mem_support_iff_of_span_eq_top hspan).mp hq
  by_contra hp
  obtain ⟨b, hb, hbm⟩ := Module.notMem_support_iff'.mp hp m
  apply hb
  apply hm
  rw [Submodule.mem_annihilator_span_singleton]
  rw [IsScalarTower.algebraMap_smul C, ← TensorProduct.tmul_smul, hbm,
    TensorProduct.tmul_zero]

/-- Flat extension of scalars has precisely the inverse image of support. -/
lemma support_tensor_eq [Module.Flat B C] :
    Module.support C (C ⊗[B] M) =
      PrimeSpectrum.comap (algebraMap B C) ⁻¹' Module.support B M := by
  refine (support_tensor_subset B C M).antisymm ?_
  intro q hq
  obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.mp hq
  let I := (Submodule.span B {m}).annihilator
  let f : B ⧸ I →ₗ[B] M := Submodule.liftQ I
    ((LinearMap.lsmul B M).flip m) (fun b hb => by
      simpa only [LinearMap.mem_ker, LinearMap.flip_apply, LinearMap.lsmul_apply,
        Submodule.mem_annihilator_span_singleton, I] using hb)
  have hf : Function.Injective f := LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr (by
    intro b hb
    induction b using Quotient.inductionOn' with
    | h b =>
      simpa only [Submodule.Quotient.mk''_eq_mk, Submodule.mem_bot,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_annihilator_span_singleton,
        LinearMap.mem_ker, Submodule.liftQ_apply, LinearMap.flip_apply,
        LinearMap.lsmul_apply, I, f] using hb))
  have hmap : I.map (algebraMap B C) ≤ q.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr hm
  have hquot : q ∈ Module.support C (C ⧸ I.map (algebraMap B C)) := by
    simpa only [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq,
      Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] using hmap
  have e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I
  rw [e.toLinearEquiv.support_eq] at hquot
  exact Module.support_subset_of_injective (f.baseChange C)
    (Module.Flat.lTensor_preserves_injective_linearMap f hf) hquot

/-- The identity on the ambient spectrum identifies the support after flat
extension with the inverse image of the original support. -/
noncomputable def baseChangeSupportHomeomorph [Module.Flat B C] :
    Module.support C (C ⊗[B] M) ≃ₜ
      (PrimeSpectrum.comap (algebraMap B C) ⁻¹' Module.support B M) :=
  Homeomorph.setCongr (support_tensor_eq B C M)

end Langlands.AlgebraicGeometry.FlatModuleSupport
