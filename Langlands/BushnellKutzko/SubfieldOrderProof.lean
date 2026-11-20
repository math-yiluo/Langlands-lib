import Langlands.BushnellKutzko.SubfieldOrderStatement
import Langlands.BushnellKutzko.SubfieldLayerLifting
import Langlands.BushnellKutzko.RelativeLatticeChain
import Langlands.BushnellKutzko.RadicalFiltrationProof

/-! # The order and radical filtration relative to a normalizing subfield -/

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u v w

/-- The relative order, its radical filtration and its period in BK93 (1.2.2)–(1.2.4). -/
theorem subfieldOrder : SubfieldOrderStatement.{u, v, w} := by
  intro F _ _ _ _ V _ _ E _ _ _ _ 𝓛 hE
  let := 𝓛.finiteDimensional_subfield E
  let := subfieldIntegers_isDiscreteValuationRing F E
  let := subfieldIntegers_isFractionRing F E
  let relative := 𝓛.subfieldChain E hE
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  let spectral := 𝓛.relativeLatticeChain hE (isIntegral_iff_mem_spectralInteger F E)
  obtain ⟨hmul, _, _, hradical, _⟩ := radicalFiltration E V spectral
  refine ⟨relative, fun _ => rfl, fun _ => Iff.rfl, fun _ _ => Iff.rfl, ?_, ?_, ?_⟩
  · intro m n
    refine le_antisymm (relative.endFiltration_mul_le m n) ?_
    intro x hx
    have hproduct : x ∈ spectral.endFiltration m * spectral.endFiltration n := by
      rw [hmul m n]
      exact hx
    exact Submodule.mul_induction_on hproduct
      (fun a ha b hb => Submodule.mul_mem_mul
        (show a ∈ relative.endFiltration m from ha)
        (show b ∈ relative.endFiltration n from hb))
      (fun _ _ ha hb => add_mem ha hb)
  · let e : relative.order ≃+* spectral.order :=
      { toFun := fun y => ⟨y.val, y.prop⟩
        invFun := fun y => ⟨y.val, y.prop⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl }
    have hcomap : Ideal.comap e.toRingHom (Ring.jacobson spectral.order) =
        Ring.jacobson relative.order := by
      simpa only [Ideal.comap_bot_of_injective e.toRingHom e.injective, Ideal.jacobson_bot] using
        (Ideal.comap_jacobson_of_surjective (f := e.toRingHom) e.surjective
          (K := (⊥ : Ideal spectral.order)))
    intro y
    rw [← hcomap, Ideal.mem_comap]
    exact hradical (e y)
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
    have hshift := 𝓛.fieldShift_uniformizer_mul_ramification E hE hϖ
    change (𝓛.fieldShift E hE (subfieldIntegerUnit E hϖ.ne_zero)).toAdd *
      (subfieldRamificationIndex F E : ℤ) = (𝓛.period : ℤ) at hshift
    rw [← 𝓛.subfieldChain_period_eq_shift E hE hϖ, mul_comm] at hshift
    exact_mod_cast hshift.symm

end Langlands.BushnellKutzko
