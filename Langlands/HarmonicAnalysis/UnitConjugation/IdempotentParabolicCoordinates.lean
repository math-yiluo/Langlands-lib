import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicGroup

/-! # Levi and unipotent coordinates on the upper triangular unit group -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer

open _root_.Topology

universe u v

variable (F : Type u) [Field F] {A : Type v} [Ring A] [Algebra F A] {e : A}

local notation "Levi" => Subalgebra.centralizer F (Set.singleton e)
local notation "Upper" => offDiagonalCorner F e

private abbrev leviInclusion : Leviˣ →* Aˣ := Units.map (Levi).val.toMonoidHom

local notation "leviIncl" => leviInclusion F

variable [TopologicalSpace A]

/-- The units of the idempotent centralizer identify with their image in the ambient group. -/
def leviUnitsEquiv : Leviˣ ≃ₜ* leviUnits F (e := e) := by
  have hι : IsEmbedding (leviInclusion F (e := e)) := IsEmbedding.subtypeVal.units_map
  let E := MonoidHom.ofInjective hι.injective
  exact
    { __ := E
      continuous_toFun := hι.continuous.subtype_mk _
      continuous_invFun := by
        change Continuous (E.symm : leviUnits F (e := e) → Leviˣ)
        apply hι.continuous_iff.mpr
        have h : leviIncl ∘ E.symm = (Subtype.val : leviUnits F (e := e) → Aˣ) :=
          funext (MonoidHom.apply_ofInjective_symm hι.injective)
        rw [h]
        exact continuous_subtype_val }

@[simp]
theorem leviUnitsEquiv_apply_val (m : Leviˣ) :
    (leviUnitsEquiv F m).val = leviIncl m := rfl

variable [FiniteDimensional F A] [IsTopologicalRing A]

private def parabolicUnitLift (he : IsIdempotentElem e) (p : parabolicUnits F he) :
    (parabolicSubalgebra F he)ˣ where
  val := ⟨((p : Aˣ) : A), (mem_parabolicUnits_iff_of_finite F he _).mp p.property⟩
  inv := ⟨(((p : Aˣ)⁻¹ : Aˣ) : A),
    (mem_parabolicUnits_iff_of_finite F he _).mp ((parabolicUnits F he).inv_mem p.property)⟩
  val_inv := Subtype.ext p.val.val_inv
  inv_val := Subtype.ext p.val.inv_val

omit [IsTopologicalRing A] in
private theorem continuous_parabolicUnitLift (he : IsIdempotentElem e) :
    Continuous (parabolicUnitLift F he) :=
  Units.continuous_iff.mpr
    ⟨(Units.continuous_val.comp continuous_subtype_val).subtype_mk _,
      (Units.continuous_coe_inv.comp continuous_subtype_val).subtype_mk _⟩

private def leviProjection (he : IsIdempotentElem e) (p : parabolicUnits F he) : Leviˣ :=
  Units.map (parabolicDiagonal F he).toMonoidHom (parabolicUnitLift F he p)

private theorem continuous_leviProjection (he : IsIdempotentElem e) :
    Continuous (leviProjection F he) := by
  have hd : Continuous (parabolicDiagonal F he) := by
    apply continuous_induced_rng.mpr
    change Continuous fun a : parabolicSubalgebra F he => diagonalProjection F e (a : A)
    simp only [diagonalProjection_apply]
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).add
      ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  exact (hd.units_map _).comp (continuous_parabolicUnitLift F he)

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem mem_parabolicUnits_levi (he : IsIdempotentElem e) (m : Leviˣ) :
    leviIncl m ∈ parabolicUnits F he := by
  apply (mem_parabolicUnits_iff_of_finite F he _).mpr
  change (1 - e) * (m.val : A) * e = 0
  rw [mul_assoc, ← (mem_centralizer_singleton_iff F).mp m.val.property,
    ← mul_assoc, (idempotent_mul_rules he).2.1, zero_mul]

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem mem_parabolicUnits_upper (he : IsIdempotentElem e) (z : Upper) :
    upperCornerUnit F he z ∈ parabolicUnits F he := by
  apply (mem_parabolicUnits_iff_of_finite F he _).mpr
  obtain ⟨w, hw⟩ := z.property
  change (1 - e) * (1 + (z : A)) * e = 0
  rw [← hw, cornerProjection_apply]
  obtain ⟨_, hfe, _, _, _, hf, _, _⟩ := idempotent_mul_rules he
  simp only [mul_add, mul_one, add_mul, hfe, mul_assoc, hf, zero_mul, zero_add]

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem leviProjection_mul_upper (he : IsIdempotentElem e) (m : Leviˣ) (z : Upper) (hp) :
    leviProjection F he ⟨leviIncl m * upperCornerUnit F he z, hp⟩ = m := by
  apply Units.ext
  apply Subtype.ext
  change diagonalProjection F e ((m.val : A) * (1 + (z : A))) = (m.val : A)
  have hm := (mem_centralizer_singleton_iff F).mp m.val.property
  have hz : diagonalProjection F e (z : A) = 0 := by
    obtain ⟨w, hw⟩ := z.property
    rw [← hw, cornerProjection_apply, diagonalProjection_apply]
    obtain ⟨_, hfe, _, _, _, hf, _, _⟩ := idempotent_mul_rules he
    simp only [mul_assoc, hfe, hf, zero_mul, mul_zero, add_zero]
  rw [diagonalProjection_mul_left hm, map_add, diagonalProjection_of_commute he (by simp),
    hz, add_zero, mul_one]

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem mem_parabolicUnits_product (he : IsIdempotentElem e)
    (x : leviUnits F (e := e) × upperCornerUnits F he) :
    x.1.val * x.2.val ∈ parabolicUnits F he := by
  obtain ⟨m, hm⟩ := x.1.property
  obtain ⟨z, hz⟩ := x.2.property
  rw [← hm, ← hz]
  exact (parabolicUnits F he).mul_mem (mem_parabolicUnits_levi F he m)
    (mem_parabolicUnits_upper F he z.toAdd)

/-- Multiplication is a homeomorphism from the Levi and upper unipotent coordinates
onto the parabolic subgroup. -/
def parabolicUnitsHomeomorph (he : IsIdempotentElem e) :
    leviUnits F (e := e) × upperCornerUnits F he ≃ₜ parabolicUnits F he := by
  let forward (x : leviUnits F (e := e) × upperCornerUnits F he) : parabolicUnits F he :=
    ⟨x.1.val * x.2.val, mem_parabolicUnits_product F he x⟩
  let m (p : parabolicUnits F he) : leviUnits F (e := e) :=
    leviUnitsEquiv F (leviProjection F he p)
  let z (p : parabolicUnits F he) : Aˣ := (m p).val⁻¹ * p.val
  have hm : ∀ l : Leviˣ, ∀ t : Upper, ∀ hp,
      (m ⟨leviIncl l * upperCornerUnit F he t, hp⟩).val = leviIncl l := by
    intro l t hp
    change leviIncl (leviProjection F he ⟨leviIncl l * upperCornerUnit F he t, hp⟩) = _
    rw [leviProjection_mul_upper]
  have hz (p : parabolicUnits F he) : z p ∈ upperCornerUnits F he := by
    obtain ⟨l, t, hp⟩ := exists_levi_mul_upperCornerUnit F he p.val p.property
    have hmp : (m p).val = leviIncl l := by
      have hmem : leviIncl l * upperCornerUnit F he t ∈ parabolicUnits F he :=
        hp ▸ p.property
      have h : p = ⟨leviIncl l * upperCornerUnit F he t, hmem⟩ := Subtype.ext hp
      rw [h, hm]
    change (m p).val⁻¹ * p.val ∈ upperCornerUnits F he
    rw [hmp, hp, inv_mul_cancel_left]
    exact ⟨Multiplicative.ofAdd t, rfl⟩
  refine
    { toFun := forward
      invFun := fun p => (m p, ⟨z p, hz p⟩)
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _
      continuous_invFun := ?_ }
  · intro x
    obtain ⟨l, hl⟩ := x.1.property
    obtain ⟨t, ht⟩ := x.2.property
    have hmx : (m (forward x)).val = x.1.val := by
      have h : forward x =
          ⟨leviIncl l * upperCornerUnit F he t.toAdd,
            (parabolicUnits F he).mul_mem (mem_parabolicUnits_levi F he l)
              (mem_parabolicUnits_upper F he t.toAdd)⟩ :=
        Subtype.ext (congrArg₂ (· * ·) hl.symm ht.symm)
      rw [h, hm, hl]
    refine Prod.ext (Subtype.ext hmx) (Subtype.ext ?_)
    change (m (forward x)).val⁻¹ * (x.1.val * x.2.val) = x.2.val
    rw [hmx, inv_mul_cancel_left]
  · intro p
    apply Subtype.ext
    change (m p).val * ((m p).val⁻¹ * p.val) = p.val
    exact mul_inv_cancel_left _ _
  · have hm' : Continuous m := (leviUnitsEquiv F).continuous.comp (continuous_leviProjection F he)
    exact hm'.prodMk
      (((continuous_subtype_val.comp hm').inv.mul continuous_subtype_val).subtype_mk _)

@[simp]
theorem parabolicUnitsHomeomorph_apply_val (he : IsIdempotentElem e)
    (x : leviUnits F (e := e) × upperCornerUnits F he) :
    (parabolicUnitsHomeomorph F he x).val = x.1.val * x.2.val := rfl

end Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer
