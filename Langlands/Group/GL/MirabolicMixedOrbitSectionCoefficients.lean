import Langlands.Group.GL.MirabolicMixedOrbitSections

/-! Actual coefficient homomorphisms on the lower mixed-orbit sections. -/

namespace Langlands.GeneralLinear.Mirabolic.MixedOrbit

open Langlands.GeneralLinear.Mirabolic.MixedProduct

universe u

variable (k r : ℕ) (R : Type u) [CommRing R]

/-- The actual left orbit coefficient restricted along the successor section. -/
def leftSectionCoefficient (i : Fin 2) :
    leftSection k r R i →* GeneralLinear (k + 1) R × mirabolic (r + 1) R :=
  (leftCoefficient k r R i).comp (plusSuccessor.subgroupComap _)

/-- The actual right orbit coefficient restricted along the successor section. -/
def rightSectionCoefficient (i : Fin 2) :
    rightSection k r R i →* mirabolic (r + 1) R × GeneralLinear (k + 1) R :=
  (rightCoefficient k r R i).comp (plusSuccessor.subgroupComap _)

section EntryTools

variable {R} {n : ℕ}

private theorem successor_entry_eq (g : mirabolic n R)
    (i j : Fin (n + 2)) (a b : Fin (n + 1))
    (hi : i.val = a.val) (hj : j.val = b.val) :
    (successor g).val.val i j = g.val.val a b := by
  have hei : i = a.castSucc := Fin.ext hi
  have hej : j = b.castSucc := Fin.ext hj
  rw [hei, hej, successor_first]

private theorem successor_last_eq (g : mirabolic n R)
    (i : Fin (n + 2)) (hi : i.val < n + 1) :
    (successor g).val.val i (Fin.last (n + 1)) = 0 := by
  have he : i = (⟨i.val, hi⟩ : Fin (n + 1)).castSucc := Fin.ext rfl
  rw [he, successor_last]

end EntryTools

/-- The complete left identity coefficient pair, in actual lower mixed coordinates. -/
theorem leftSectionCoefficient_one (g : leftSection k r R 1) :
    leftSectionCoefficient k r R 1 g =
      ((leftProjection (leftIdentitySectionEquiv k r R g)).1,
        successor (leftProjection (leftIdentitySectionEquiv k r R g)).2) := by
  apply Prod.ext
  · apply Units.ext
    apply Matrix.ext
    intro a b
    change (leftCoefficient k r R 1 (plusSuccessor.subgroupComap _ g)).1.val a b = _
    rw [leftCoefficient_fst_apply]
    simp only [leftRepresentative_one, inv_one, one_mul, mul_one]
    change (successor g.val).val.val _ _ = _
    rw [leftProjection_gl_apply, leftIdentitySectionEquiv_val, rankCast_symm_apply]
    apply successor_entry_eq <;> simp
  · apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro a b
    change (leftCoefficient k r R 1 (plusSuccessor.subgroupComap _ g)).2.val.val a b = _
    rw [leftCoefficient_snd_apply]
    simp only [leftRepresentative_one, inv_one, one_mul, mul_one]
    change (successor g.val).val.val _ _ = _
    revert a
    refine Fin.lastCases ?_ (fun b => ?_) b
    · intro a
      have he : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (leftIndex (k + 1) (r + 1) (Sum.inr (Fin.last (r + 1)))) =
          Fin.last (k + r + 2) := Fin.ext (by simp)
      rw [he]
      refine Fin.lastCases ?_ (fun a => ?_) a
      · rw [he, (successor g.val).property, (successor _).property]
        simp
      · rw [successor_last]
        apply successor_last_eq
        simp only [Fin.val_cast, leftIndex_inr_val, Fin.val_castSucc]
        omega
    · intro a
      refine Fin.lastCases ?_ (fun a => ?_) a
      · have he : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
            (leftIndex (k + 1) (r + 1) (Sum.inr (Fin.last (r + 1)))) =
            Fin.last (k + r + 2) := Fin.ext (by simp)
        rw [he, (successor g.val).property, (successor _).property]
        have hne : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
            (leftIndex (k + 1) (r + 1) (Sum.inr b.castSucc)) ≠
            Fin.last (k + r + 2) := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_cast, leftIndex_inr_val, Fin.val_castSucc, Fin.val_last] at this
          omega
        simp only [hne, Fin.castSucc_ne_last, ↓reduceIte]
      · rw [successor_first, leftProjection_mirabolic_apply,
          leftIdentitySectionEquiv_val, rankCast_symm_apply]
        apply successor_entry_eq <;> simp

/-- The right identity coefficient retains the actual GL restriction to a mirabolic. -/
theorem rightSectionCoefficient_one (g : rightSection k r R 1) :
    rightSectionCoefficient k r R 1 g =
      (levi (leftProjection (rightIdentitySectionEquiv k r R g)).1,
        (leftProjection (rightIdentitySectionEquiv k r R g)).2.val) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro a b
    change (rightCoefficient k r R 1 (plusSuccessor.subgroupComap _ g)).1.val.val a b = _
    rw [rightCoefficient_fst_apply]
    simp only [rightRepresentative_one, inv_one, one_mul, mul_one]
    change (successor g.val).val.val _ _ = _
    revert a
    refine Fin.lastCases ?_ (fun b => ?_) b
    · intro a
      have he : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (rightIndex (k + 1) (r + 1) (Sum.inl (Fin.last (r + 1)))) =
          Fin.last (k + r + 2) := Fin.ext (by simp)
      rw [he]
      refine Fin.lastCases ?_ (fun a => ?_) a
      · rw [he, (successor g.val).property, levi_bottom]
        simp
      · rw [levi_last]
        apply successor_last_eq
        simp only [Fin.val_cast, rightIndex_first_val]
        omega
    · intro a
      refine Fin.lastCases ?_ (fun a => ?_) a
      · have he : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
            (rightIndex (k + 1) (r + 1) (Sum.inl (Fin.last (r + 1)))) =
            Fin.last (k + r + 2) := Fin.ext (by simp)
        rw [he, (successor g.val).property, levi_bottom]
        have hne : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
            (rightIndex (k + 1) (r + 1) (Sum.inl b.castSucc)) ≠
            Fin.last (k + r + 2) := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_cast, rightIndex_first_val, Fin.val_last] at this
          omega
        simp only [hne, Fin.castSucc_ne_last, ↓reduceIte]
      · rw [levi_first, leftProjection_gl_apply,
          rightIdentitySectionEquiv_val, rankCast_symm_apply]
        apply successor_entry_eq <;> simp
  · apply Units.ext
    apply Matrix.ext
    intro a b
    change (rightCoefficient k r R 1 (plusSuccessor.subgroupComap _ g)).2.val a b = _
    rw [rightCoefficient_snd_apply]
    simp only [rightRepresentative_one, inv_one, one_mul, mul_one]
    change (successor g.val).val.val _ _ = _
    rw [leftProjection_mirabolic_apply, rightIdentitySectionEquiv_val, rankCast_symm_apply]
    apply successor_entry_eq <;> simp

section RightCycle

private theorem cycle_inv_conjugate_entry {t a : ℕ} (ha : a ≤ t)
    (g : mirabolic (t + 1) R) (i j : Fin (t + 2)) :
    ((cycleElement t a ha R)⁻¹ * g * cycleElement t a ha R).val.val i j =
      g.val.val (descendingCycle t a ha i) (descendingCycle t a ha j) := by
  change ((permutation (t + 2) R (descendingCycle t a ha))⁻¹ * g.val *
    permutation (t + 2) R (descendingCycle t a ha)).val i j = _
  rw [mul_permutation_entry, permutation_inv, permutation_mul_entry]
  rfl

private theorem rightCycle_upper_first (a : Fin (r + 1)) :
    descendingCycle (k + r + 1) r (by omega)
        (Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (rightIndex (k + 1) (r + 1) (Sum.inl a.castSucc))) =
      (Fin.cast (congrArg (· + 1) (show k + 1 + r = k + r + 1 by omega))
        (rightIndex (k + 1) r (Sum.inl a))).castSucc := by
  refine Fin.lastCases ?_ (fun a => ?_) a
  · apply Fin.ext
    change (if _ = r then _ else if _ then _ else _) = _
    simp only [Fin.val_cast, rightIndex_first_val, Fin.val_last]
    simp
  · apply Fin.ext
    change (if _ = r then _ else if _ then _ else _) = _
    simp only [Fin.val_cast, rightIndex_first_val, Fin.val_castSucc]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem rightCycle_upper_middle (a : Fin (k + 1)) :
    descendingCycle (k + r + 1) r (by omega)
        (Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (rightIndex (k + 1) (r + 1) (Sum.inr a))) =
      (Fin.cast (congrArg (· + 1) (show k + 1 + r = k + r + 1 by omega))
        (rightIndex (k + 1) r (Sum.inr a))).castSucc := by
  apply Fin.ext
  change (if _ = r then _ else if _ then _ else _) = _
  simp only [Fin.val_cast, rightIndex_middle_val, Fin.val_castSucc]
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  omega

/-- The right cyclic coefficient pair is the lower right pair with successor on P. -/
theorem rightSectionCoefficient_zero (g : rightSection k r R 0) :
    rightSectionCoefficient k r R 0 g =
      (successor (rightProjection (rightCycleSectionEquiv k r R g)).1,
        (rightProjection (rightCycleSectionEquiv k r R g)).2) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro a b
    change (rightCoefficient k r R 0 (plusSuccessor.subgroupComap _ g)).1.val.val a b = _
    rw [rightCoefficient_fst_apply]
    simp only [rightRepresentative_zero, rightCycleElement, cycle_inv_conjugate_entry]
    change (successor g.val).val.val _ _ = _
    revert a
    refine Fin.lastCases ?_ (fun b => ?_) b
    · intro a
      have he : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (rightIndex (k + 1) (r + 1) (Sum.inl (Fin.last (r + 1)))) =
          Fin.last (k + r + 2) := Fin.ext (by simp)
      rw [he, descendingCycle_last]
      refine Fin.lastCases ?_ (fun a => ?_) a
      · rw [he, descendingCycle_last, (successor g.val).property, (successor _).property]
        simp
      · rw [rightCycle_upper_first, successor_last, successor_last]
    · intro a
      refine Fin.lastCases ?_ (fun a => ?_) a
      · have he : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
            (rightIndex (k + 1) (r + 1) (Sum.inl (Fin.last (r + 1)))) =
            Fin.last (k + r + 2) := Fin.ext (by simp)
        rw [he, descendingCycle_last, rightCycle_upper_first,
          (successor g.val).property, (successor _).property]
        simp only [Fin.castSucc_ne_last, ↓reduceIte]
      · rw [rightCycle_upper_first, rightCycle_upper_first, successor_first, successor_first,
          rightProjection_mirabolic_apply, rightCycleSectionEquiv_val, rankCast_symm_apply]
  · apply Units.ext
    apply Matrix.ext
    intro a b
    change (rightCoefficient k r R 0 (plusSuccessor.subgroupComap _ g)).2.val a b = _
    rw [rightCoefficient_snd_apply]
    simp only [rightRepresentative_zero, rightCycleElement, cycle_inv_conjugate_entry]
    change (successor g.val).val.val _ _ = _
    rw [rightCycle_upper_middle, rightCycle_upper_middle, successor_first,
      rightProjection_gl_apply, rightCycleSectionEquiv_val, rankCast_symm_apply]

end RightCycle

/-- Equality of the full actual left identity coefficient homomorphisms. -/
theorem leftSectionCoefficient_one_hom :
    leftSectionCoefficient k r R 1 =
      ((MonoidHom.id (GeneralLinear (k + 1) R)).prodMap successor).comp
        (leftProjection.comp (leftIdentitySectionEquiv k r R).toMonoidHom) :=
  MonoidHom.ext (leftSectionCoefficient_one k r R)

/-- Equality of the full actual right cyclic coefficient homomorphisms. -/
theorem rightSectionCoefficient_zero_hom :
    rightSectionCoefficient k r R 0 =
      (successor.prodMap (MonoidHom.id (GeneralLinear (k + 1) R))).comp
        (rightProjection.comp (rightCycleSectionEquiv k r R).toMonoidHom) :=
  MonoidHom.ext (rightSectionCoefficient_zero k r R)

/-- The quotient-orbit homomorphism includes the actual mirabolic subgroup into GL. -/
theorem rightSectionCoefficient_one_hom :
    rightSectionCoefficient k r R 1 =
      (levi.prodMap (mirabolic k R).subtype).comp
        (leftProjection.comp (rightIdentitySectionEquiv k r R).toMonoidHom) :=
  MonoidHom.ext (rightSectionCoefficient_one k r R)

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_leftSectionCoefficient (i : Fin 2) :
    Continuous (leftSectionCoefficient k r R i) :=
  (continuous_leftCoefficient k r R i).comp
    ((continuous_plusSuccessor.comp continuous_subtype_val).subtype_mk _)

theorem continuous_rightSectionCoefficient (i : Fin 2) :
    Continuous (rightSectionCoefficient k r R i) :=
  (continuous_rightCoefficient k r R i).comp
    ((continuous_plusSuccessor.comp continuous_subtype_val).subtype_mk _)

end Topology

end Langlands.GeneralLinear.Mirabolic.MixedOrbit
