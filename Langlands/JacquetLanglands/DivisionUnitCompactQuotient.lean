import Langlands.Analysis.Local.ModularCharacterContinuity
import Langlands.BaseChange.FiniteAlgebraUnits
import Langlands.JacquetLanglands.DivisionUnits
import Langlands.Representation.Unitary.CentralQuotientForm

/-! # Compactness modulo scalars and right Haar invariance of division units -/

noncomputable section

namespace Langlands.JacquetLanglands

open Set MeasureTheory MeasureTheory.Measure _root_.Topology
open Langlands.BaseChange Langlands.QuotientIntegration
open scoped NNReal

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (D : Type u) [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [TopologicalSpace D] [IsModuleTopology F D]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [FiniteDimensional F D] [TopologicalSpace D] [IsModuleTopology F D] in
private theorem scalarUnit_mem_center (a : Fˣ) :
    Units.map (algebraMap F D).toMonoidHom a ∈ Subgroup.center Dˣ := by
  rw [Subgroup.mem_center_iff]
  intro x
  exact Units.ext (Algebra.commutes a.val x.val).symm

/-- Each multiplicative scalar coset has a representative in a fixed compact set. -/
private theorem exists_compact_unit_representatives :
    ∃ C : Set Dˣ, IsCompact C ∧
      ∀ x : Dˣ, ∃ (a : Fˣ) (y : Dˣ), y ∈ C ∧ x = Units.map (algebraMap F D).toMonoidHom a * y := by
  classical
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let b := Module.finBasis F D
  let e := coordinateHomeomorph F D b
  let v := ValuativeRel.valuation F
  let I : Set F := {x | v x ≤ 1}
  have hI : IsCompact I := IsNonarchimedeanLocalField.isCompact_closedBall F 1
  let W : Set (Fin (Module.finrank F D) → F) :=
    Set.univ.pi (fun _ => I) ∩ ⋃ j, {a | a j = 1}
  have hW : IsCompact W := (isCompact_univ_pi fun _ => hI).inter_right
    (isClosed_iUnion_of_finite fun j => isClosed_eq (continuous_apply j) continuous_const)
  let p : Dˣ → (Fin (Module.finrank F D) → F) := e ∘ Units.val
  have hp : IsEmbedding p := e.isEmbedding.comp
    (finiteAlgebra_isOpenEmbedding_unitsVal (F := F) (A := D)).isEmbedding
  let C := p ⁻¹' W
  have hC : IsCompact C := hp.isInducing.isCompact_preimage' hW fun a ha => by
    obtain ⟨j, hj⟩ := mem_iUnion.mp ha.2
    have ha0 : e.symm a ≠ 0 := by
      intro h
      have hz : a = 0 := by
        rw [← e.apply_symm_apply a, h]
        exact b.equivFun.map_zero
      change a j = 1 at hj
      exact zero_ne_one (by simpa only [hz, Pi.zero_apply] using hj)
    exact ⟨Units.mk0 (e.symm a) ha0, e.apply_symm_apply a⟩
  refine ⟨C, hC, ?_⟩
  intro x
  have hx : e x.val ≠ 0 := by
    intro h
    exact x.ne_zero (e.injective (h.trans b.equivFun.map_zero.symm))
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  have hj0 : e x.val j ≠ 0 := hj
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => v (e x.val i))
    ⟨j, Finset.mem_univ _⟩
  have hi0 : e x.val i ≠ 0 := by
    intro h
    have hle := hi j (Finset.mem_univ _)
    rw [h, map_zero] at hle
    exact (map_ne_zero v).mpr hj0 (le_zero_iff.mp hle)
  let a : Fˣ := Units.mk0 (e x.val i) hi0
  let m := Units.map (algebraMap F D).toMonoidHom
  let y := m a⁻¹ * x
  have hy (j : Fin (Module.finrank F D)) : p y j = (e x.val i)⁻¹ * e x.val j := by
    change b.equivFun (algebraMap F D ((e x.val i)⁻¹) * x.val) j = _
    rw [← Algebra.smul_def, map_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  refine ⟨a, y, ?_, ?_⟩
  · change p y ∈ W
    refine ⟨fun j _ => ?_, mem_iUnion.mpr ⟨i, ?_⟩⟩
    · change v (p y j) ≤ 1
      rw [hy, map_mul, map_inv₀]
      exact (inv_mul_le_one₀ (pos_iff_ne_zero.mpr ((map_ne_zero v).mpr hi0))).mpr
        (hi j (Finset.mem_univ _))
    · change p y i = 1
      rw [hy, inv_mul_cancel₀ hi0]
  · change x = m a * (m a⁻¹ * x)
    rw [map_inv, mul_inv_cancel_left]

include F in
/-- The left quotient of division units by any subgroup containing the center is compact. -/
theorem compactSpace_leftQuotient_divisionUnits [IsTopologicalRing D]
    (H : Subgroup Dˣ) (hH : Subgroup.center Dˣ ≤ H) : CompactSpace (LeftQuotient H) := by
  obtain ⟨C, hC, hrep⟩ := exists_compact_unit_representatives F D
  have hq : leftQuotientMap H '' C = univ := by
    apply eq_univ_of_forall
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    obtain ⟨a, y, hy, rfl⟩ := hrep x
    refine ⟨y, hy, Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)⟩
    simpa only [mul_inv_cancel_right] using hH (scalarUnit_mem_center F D a)
  exact ⟨hq ▸ hC.image (leftQuotient_isOpenQuotientMap H).continuous⟩

variable [IsTopologicalRing D] [MeasurableSpace Dˣ] [BorelSpace Dˣ]

include F in
/-- The unit group of a finite-dimensional division algebra over a local field is unimodular. -/
theorem divisionUnits_haar_rightInvariant (μ : Measure Dˣ) [μ.IsHaarMeasure] [μ.Regular] :
    μ.IsMulRightInvariant := by
  let : LocallyCompactSpace Dˣ := units_locallyCompactSpace F D
  let χ : Dˣ →* ℝ≥0 := modularCharacter
  have hz (z : Dˣ) (hz : z ∈ Subgroup.center Dˣ) : χ z = 1 := by
    change modularCharacterFun z = 1
    rw [modularCharacterFun_eq_haarScalarFactor μ z]
    have he : (· * z) = (z * ·) := funext (Subgroup.mem_center_iff.mp hz)
    have hmap : μ.map (· * z) = μ := by rw [he, map_mul_left_eq_self]
    have hfactor (ν : Measure Dˣ) [ν.IsHaarMeasure] (hν : ν = μ) : haarScalarFactor ν μ = 1 := by
      subst ν
      exact haarScalarFactor_self _
    exact hfactor _ hmap
  obtain ⟨C, hC, hrep⟩ := exists_compact_unit_representatives F D
  have hrange : range χ = χ '' C := by
    refine subset_antisymm ?_ (image_subset_range _ _)
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, y, hy, rfl⟩ := hrep x
    exact ⟨y, hy, by rw [map_mul, hz _ (scalarUnit_mem_center F D a), one_mul]⟩
  have hbounded : BddAbove (range χ) := hrange ▸
    (hC.image (Haar.continuous_modularCharacter_of_locallyCompact (G := Dˣ))).bddAbove
  have hle (x : Dˣ) : χ x ≤ 1 := by
    by_contra! hx
    obtain ⟨b, hb⟩ := hbounded
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt b hx
    exact (not_lt_of_ge (hb ⟨x ^ n, map_pow χ x n⟩)) hn
  apply Haar.isMulRightInvariant_of_modularCharacter_eq_one _ μ
  intro x
  apply le_antisymm (hle x)
  calc
    1 = χ x * χ x⁻¹ := by rw [← map_mul, mul_inv_cancel, map_one]
    _ ≤ χ x := by simpa only [mul_one] using mul_le_mul_right (hle x⁻¹) (χ x)

end Langlands.JacquetLanglands
