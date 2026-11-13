import Langlands.GroupTheory.ProPTransport
import Langlands.Group.RelativeWeylConjugation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Topological subgroup conjugation and compact open inclusions -/

noncomputable section

universe u

open MeasureTheory
open Langlands.Group.RelativeWeyl

namespace Langlands.Cohomology

variable {X : Type u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]

/-- Conjugation induces an isomorphism with the conjugate subgroup, with the
actual induced topologies on both subgroup types. -/
def subgroupConjugationContinuousMulEquiv (g : X) (H : Subgroup X) :
    H ≃ₜ* conjugateSubgroup g H where
  toMulEquiv := (MulAut.conj g).subgroupMap H
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun x : H => g * (x : X) * g⁻¹)
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (fun x : conjugateSubgroup g H => g⁻¹ * (x : X) * g)
    fun_prop

/-- Conjugation preserves the pro-p property of actual topological subgroups. -/
theorem IsProPSubgroup.conjugate {p : ℕ} {H : Subgroup X}
    (hH : IsProPSubgroup p H) (g : X) : IsProPSubgroup p (conjugateSubgroup g H) :=
  hH.of_continuousMulEquiv (subgroupConjugationContinuousMulEquiv g H)

section Haar

variable [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- In a unimodular group, Haar measure of an open subgroup is unchanged by
conjugation. -/
theorem haar_conjugateSubgroup_eq (hmod : ∀ g : X, Measure.modularCharacter g = 1)
    (g : X) (H : Subgroup X) (hH : IsOpen (H : Set X)) :
    Measure.haar (conjugateSubgroup g H : Set X) = Measure.haar (H : Set X) := by
  let μ : Measure X := Measure.haar
  have : (μ.map (fun x => x * g⁻¹)).Regular :=
    Measure.Regular.map (Homeomorph.mulRight g⁻¹)
  have hright : μ.map (fun x => x * g⁻¹) = μ := by
    calc
      _ = Measure.modularCharacterFun (g⁻¹) • μ := by
        rw [Measure.modularCharacterFun_eq_haarScalarFactor μ]
        exact Measure.isMulLeftInvariant_eq_smul_of_regular _ _
      _ = μ := by change Measure.modularCharacter (g⁻¹) • μ = μ; rw [hmod, one_smul]
  have hmap : μ.map (fun x => g * x * g⁻¹) = μ := by
    calc
      _ = (μ.map (fun x => g * x)).map (fun x => x * g⁻¹) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = μ := by rw [map_mul_left_eq_self, hright]
  have hopen : IsOpen (conjugateSubgroup g H : Set X) := by
    change IsOpen ((MulAut.conj g) '' (H : Set X))
    exact (Homeomorph.mulLeft g |>.trans (Homeomorph.mulRight g⁻¹)).isOpenMap _ hH
  have hpre : (fun x => g * x * g⁻¹) ⁻¹' (conjugateSubgroup g H : Set X) = H := by
    ext x
    change (MulAut.conj g) x ∈ H.map (MulAut.conj g : X →* X) ↔ x ∈ H
    exact Subgroup.mem_map_iff_mem (MulAut.conj g).injective
  change μ (conjugateSubgroup g H : Set X) = μ (H : Set X)
  calc
    _ = (μ.map (fun x => g * x * g⁻¹)) (conjugateSubgroup g H : Set X) := by rw [hmap]
    _ = μ (H : Set X) := by
      rw [Measure.map_apply (by fun_prop) hopen.measurableSet, hpre]

/-- Nested compact open subgroups of equal Haar measure are equal. -/
theorem eq_of_le_of_haar_eq {H K : Subgroup X}
    (hH : IsOpen (H : Set X)) (hK : IsOpen (K : Set X))
    (hcompact : IsCompact (H : Set X)) (hle : H ≤ K)
    (hvol : Measure.haar (H : Set X) = Measure.haar (K : Set X)) : H = K := by
  have hclosed : IsClosed (H : Set X) := Subgroup.isClosed_of_isOpen H hH
  have hzero : Measure.haar ((K : Set X) \ H) = 0 := by
    rw [measure_sdiff hle hH.measurableSet.nullMeasurableSet hcompact.measure_ne_top,
      ← hvol, tsub_self]
  have hempty : (K : Set X) \ H = ∅ :=
    (hK.sdiff hclosed).eq_empty_of_measure_zero hzero
  exact le_antisymm hle (Set.sdiff_eq_empty.mp hempty)

/-- A compact open subgroup cannot be properly contained in one of its
conjugates in a unimodular group. -/
theorem conjugate_eq_of_le (hmod : ∀ g : X, Measure.modularCharacter g = 1)
    (g : X) (H : Subgroup X) (hH : IsOpen (H : Set X))
    (hcompact : IsCompact (H : Set X)) (hle : H ≤ conjugateSubgroup g H) :
    conjugateSubgroup g H = H := by
  symm
  apply eq_of_le_of_haar_eq hH _ hcompact hle (haar_conjugateSubgroup_eq hmod g H hH).symm
  change IsOpen ((MulAut.conj g) '' (H : Set X))
  exact (Homeomorph.mulLeft g |>.trans (Homeomorph.mulRight g⁻¹)).isOpenMap _ hH

end Haar
end Langlands.Cohomology
