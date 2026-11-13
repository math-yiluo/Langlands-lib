import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Injectivity of exterior antisymmetrization for free modules -/

noncomputable section

namespace Langlands.LinearAlgebra

open exteriorPower

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Free R M]

/-- Antisymmetrization from an exterior power to a tensor power is injective
for a free module, without any assumption on factorials in the ring. -/
theorem exteriorPowerToTensorPower_injective (n : ℕ) :
    Function.Injective (exteriorPower.toTensorPower R M n) := by
  suffices hzero : ∀ x, exteriorPower.toTensorPower R M n x = 0 → x = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    simpa only [map_sub, sub_eq_zero] using hxy
  intro x hx
  have hpair : (exteriorPower.pairingDual R M n).flip x = 0 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.flip_apply,
      exteriorPower.pairingDual, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      LinearMap.zero_apply]
    change TensorPower.multilinearMapToDual R M n f
      (exteriorPower.toTensorPower R M n x) = 0
    rw [hx, map_zero]
  classical
  obtain ⟨I, b⟩ := Module.Free.exists_basis R M
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  apply (b.exteriorPower n).repr.injective
  ext s
  simpa only [map_zero, Finsupp.zero_apply, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual, LinearMap.flip_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun hpair (exteriorPower.ιMulti_family R n b.coord s)

end Langlands.LinearAlgebra
