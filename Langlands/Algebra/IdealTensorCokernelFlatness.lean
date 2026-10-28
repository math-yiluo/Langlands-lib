import Langlands.Algebra.IdealTensorCokernelFlatnessStatement
import Mathlib.RingTheory.Flat.Tensor

/-! # Flatness of a cokernel from ideal-quotient tensor injectivity -/

universe u v w

namespace Langlands.Algebra

open TensorProduct LinearMap

/-- Ideal-quotient tensor injectivity into a flat module gives a flat cokernel. -/
theorem idealTensorCokernelFlatness :
    IdealTensorCokernelFlatnessStatement.{u, v, w} := by
  intro R A B _ _ _ _ _ f hB _hf hI
  let : Module.Flat R B := hB
  let q : B →ₗ[R] B ⧸ LinearMap.range f := (LinearMap.range f).mkQ
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have he : Function.Exact f q := by
    rw [LinearMap.exact_iff]
    exact Submodule.ker_mkQ _
  apply Module.Flat.iff_rTensor_injective'.mpr
  intro I
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective I hq x
  have hnatq :
      (LinearMap.lTensor R q).comp (LinearMap.rTensor B I.subtype) =
        (LinearMap.rTensor (B ⧸ LinearMap.range f) I.subtype).comp
          (LinearMap.lTensor I q) := by
    ext
    simp
  have hy :
      (LinearMap.lTensor R q) ((LinearMap.rTensor B I.subtype) y) = 0 := by
    rw [← LinearMap.comp_apply, hnatq]
    exact hx
  obtain ⟨a, ha⟩ :=
    (lTensor_exact R he hq ((LinearMap.rTensor B I.subtype) y)).mp hy
  have hIq : I.mkQ.comp I.subtype = 0 :=
    (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero
  have ha0 :
      (LinearMap.rTensor B I.mkQ) ((LinearMap.lTensor R f) a) = 0 := by
    rw [ha, ← LinearMap.rTensor_comp_apply, hIq, LinearMap.rTensor_zero,
      LinearMap.zero_apply]
  have hnatf :
      (LinearMap.lTensor (R ⧸ I) f).comp (LinearMap.rTensor A I.mkQ) =
        (LinearMap.rTensor B I.mkQ).comp (LinearMap.lTensor R f) := by
    ext
    simp
  have haI : (LinearMap.rTensor A I.mkQ) a = 0 := by
    apply hI I
    rw [map_zero, ← LinearMap.comp_apply, hnatf]
    exact ha0
  obtain ⟨c, hc⟩ :=
    (rTensor_exact A (LinearMap.exact_subtype_mkQ I)
      (Submodule.mkQ_surjective I) a).mp haI
  have hnatI :
      (LinearMap.rTensor B I.subtype).comp (LinearMap.lTensor I f) =
        (LinearMap.lTensor R f).comp (LinearMap.rTensor A I.subtype) := by
    ext
    simp
  have hcy : (LinearMap.lTensor I f) c = y := by
    apply Module.Flat.rTensor_preserves_injective_linearMap I.subtype
      (Submodule.injective_subtype I)
    rw [← LinearMap.comp_apply, hnatI, LinearMap.comp_apply, hc, ha]
  have hqf : q.comp f = 0 := he.linearMap_comp_eq_zero
  rw [← hcy, ← LinearMap.lTensor_comp_apply, hqf, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

end Langlands.Algebra
