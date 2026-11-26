import Langlands.BushnellKutzko.RelativeUnitDoubleCosetStatement
import Langlands.BushnellKutzko.SimpleCharacterTransferComparison
import Langlands.BushnellKutzko.RelativeLatticeChain
import Langlands.BushnellKutzko.SubfieldLatticeChain
import Langlands.BushnellKutzko.MixedAdjointLifting

/-! # Relative unit double cosets by simultaneous interpolation -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

/-- BK93 (1.6.1) for the centralizer of a generator of a normalizing field. -/
theorem relativeUnitDoubleCoset : RelativeUnitDoubleCosetStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ L β hE hNorm m hm y hy
  let := hE.toField
  let E := elementAlgebra β
  let A := Module.End F V
  let G := Aˣ
  let B := centralizerUnitGroup β
  let U := L.unitFiltration m
  let Urel := relativeUnitFiltration L β m
  let ι := relativeEndUnits (F := F) (V := V) E
  have hRange : ι.range = B := relativeEndUnits_range_eq_centralizer β hE
  let := L.finiteDimensional_subfield E
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  let C := L.relativeLatticeChain hNorm (isIntegral_iff_mem_spectralInteger F E)
  have hC (i : ℤ) (v : V) : v ∈ C.lattice i ↔ v ∈ L.lattice i := Iff.rfl
  change ((U : Set G) * {y} * (U : Set G)) ∩ (B : Set G) =
    (Urel : Set G) * {y} * (Urel : Set G)
  ext z
  constructor
  · rintro ⟨hzU, hzB⟩
    obtain ⟨a₀, ha₀, v, hv, hz⟩ := Set.mem_mul.mp hzU
    obtain ⟨u, hu, y₀, hy₀, ha₀'⟩ := Set.mem_mul.mp ha₀
    have he : y₀ = y := Set.mem_singleton_iff.mp hy₀
    subst y₀
    have hEq : u⁻¹ * z = y * v := by
      rw [← hz, ← ha₀', mul_assoc u y v, inv_mul_cancel_left]
    obtain ⟨zE, hzE⟩ : z ∈ ι.range := hRange.symm ▸ hzB
    obtain ⟨yE, hyE⟩ : y ∈ ι.range := hRange.symm ▸ hy
    let zL := LinearMap.GeneralLinearGroup.toLinearEquiv zE
    let yL := LinearMap.GeneralLinearGroup.toLinearEquiv yE
    have hzL : zL.toLinearMap.restrictScalars F = (z : A) := congrArg Units.val hzE
    have hyL : yL.toLinearMap.restrictScalars F = (y : A) := congrArg Units.val hyE
    let a : A := ((u⁻¹ : G) : A) - 1
    let b : A := (v : A) - 1
    have ha : a ∈ L.endFiltration m := (U.inv_mem hu).2.2
    have hb : b ∈ L.endFiltration m := hv.2.2
    have haVal : (1 + a : A) = ((u⁻¹ : G) : A) := by rw [add_comm]; exact sub_add_cancel _ _
    have hbVal : (1 + b : A) = (v : A) := by rw [add_comm]; exact sub_add_cancel _ _
    have hEqEnd : (1 + a) * zL.toLinearMap.restrictScalars F =
        yL.toLinearMap.restrictScalars F * (1 + b) := by
      rw [haVal, hbVal, hzL, hyL]
      exact congrArg Units.val hEq
    obtain ⟨a', b', ha', hb', hrel⟩ := exists_relative_corrections C L hC yL zL ha hb hEqEnd
    obtain ⟨u', hu', hu'Val⟩ := L.exists_mem_unitFiltration hm ha'
    obtain ⟨v', hv', hv'Val⟩ := L.exists_mem_unitFiltration hm hb'
    have hBmem (g : G) (c : Module.End E V)
        (heq : (g : A) = 1 + c.restrictScalars F) : g ∈ B := by
      change Commute β (g : A)
      rw [heq]
      apply (Commute.one_right β).add_right
      apply LinearMap.ext
      intro w
      let bE : E := ⟨β, Algebra.self_mem_adjoin_singleton F β⟩
      exact (c.map_smul bE w).symm
    have hu'rel : u' ∈ Urel := ⟨hBmem u' a' hu'Val, hu'⟩
    have hv'rel : v' ∈ Urel := ⟨hBmem v' b' hv'Val, hv'⟩
    have hrelG : u' * z = y * v' := by
      apply Units.ext
      change (u' : A) * (z : A) = (y : A) * (v' : A)
      rw [hu'Val, hv'Val, ← hzL, ← hyL]
      apply LinearMap.ext
      intro w
      exact LinearMap.congr_fun hrel w
    refine Set.mem_mul.mpr ⟨u'⁻¹ * y,
      Set.mul_mem_mul (Urel.inv_mem hu'rel) (Set.mem_singleton y), v', hv'rel, ?_⟩
    rw [mul_assoc, ← hrelG, inv_mul_cancel_left]
  · intro hz
    obtain ⟨a, ha, v, hv, hz⟩ := Set.mem_mul.mp hz
    obtain ⟨u, hu, y₀, hy₀, ha'⟩ := Set.mem_mul.mp ha
    have he : y₀ = y := Set.mem_singleton_iff.mp hy₀
    subst y₀
    rw [← hz, ← ha']
    exact ⟨Set.mul_mem_mul (Set.mul_mem_mul hu.2 (Set.mem_singleton y)) hv.2,
      B.mul_mem (B.mul_mem hu.1 hy) hv.1⟩

end Langlands.BushnellKutzko
