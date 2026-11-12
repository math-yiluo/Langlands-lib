import Langlands.Group.GL.UpperUnipotentCompactContainmentProof
import Langlands.Group.GL.Mirabolic

/-! # A compact open upper-unipotent subgroup containing a compact set

The compact-denominator construction works over every nonarchimedean local
field, including positive characteristic.
-/

noncomputable section

namespace Langlands.GeneralLinear

universe uF

private def scalingDiagonal {F : Type uF} [Field F] (n : ℕ) (d : F) (hd : d ≠ 0) :
    Matrix.GeneralLinearGroup (Fin (n + 1)) F where
  val := Matrix.diagonal (fun i => (d ^ i.val)⁻¹)
  inv := Matrix.diagonal (fun i => d ^ i.val)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [hd]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [hd]

private theorem scalingDiagonal_conj_entry {F : Type uF} [Field F]
    (n : ℕ) (d : F) (hd : d ≠ 0)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) (i j : Fin (n + 1)) :
    (scalingDiagonal n d hd * g * (scalingDiagonal n d hd)⁻¹) i j =
      (d ^ i.val)⁻¹ * g i j * d ^ j.val := by
  change (Matrix.diagonal (fun i : Fin (n + 1) => (d ^ i.val)⁻¹) * g.val *
    Matrix.diagonal (fun i : Fin (n + 1) => d ^ i.val)) i j = _
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem scalingDiagonal_conj_integral {F : Type uF} [Field F] [ValuativeRel F]
    (n : ℕ) (d : F) (hd : d ≠ 0) (hdi : d ∈ (ValuativeRel.valuation F).integer)
    (g : GeneralLinear.upperUnipotent (n + 1) F)
    (hg : ∀ i j, d * g.val i j ∈ (ValuativeRel.valuation F).integer) :
    ∀ i j, (scalingDiagonal n d hd * g.val * (scalingDiagonal n d hd)⁻¹) i j ∈
      (ValuativeRel.valuation F).integer := by
  intro i j
  rw [scalingDiagonal_conj_entry]
  rcases lt_trichotomy i j with hij | rfl | hji
  · have he : j.val = i.val + (j.val - i.val - 1) + 1 := by
      have := Fin.lt_def.mp hij
      omega
    have heq : (d ^ i.val)⁻¹ * g.val i j * d ^ j.val =
        d ^ (j.val - i.val - 1) * (d * g.val i j) := by
      conv_lhs => rw [he, pow_add, pow_add, pow_one]
      field_simp
    rw [heq]
    exact ((ValuativeRel.valuation F).integer).mul_mem
      (((ValuativeRel.valuation F).integer).pow_mem hdi _) (hg i j)
  · simp [GeneralLinear.UpperUnipotent.entry_diag, hd]
  · simp [GeneralLinear.UpperUnipotent.entry_eq_zero g hji]

/-- A chosen compact open subgroup containing the supplied compact subset of
the actual upper-unipotent group, over any nonarchimedean local field. -/
def localFieldUpperUnipotentCompactOpenSubgroup
    (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    (C : Set (upperUnipotent n F)) (hC : IsCompact C) :
    {K : OpenSubgroup (upperUnipotent n F) //
      IsCompact (K : Set (upperUnipotent n F)) ∧ C ⊆ K} := by
  classical
  have hex : ∃ K : OpenSubgroup (upperUnipotent n F),
      IsCompact (K : Set (upperUnipotent n F)) ∧ C ⊆ K := by
    letI := IsTopologicalAddGroup.rightUniformSpace F
    haveI := isUniformAddGroup_of_addCommGroup (G := F)
    haveI : T2Space F := inferInstance
    cases n with
    | zero => exact ⟨⊤, Set.finite_univ.isCompact, fun _ _ => trivial⟩
    | succ n =>
        let S : Set F :=
          (⋃ i : Fin (n + 1), ⋃ j : Fin (n + 1), UpperUnipotent.entry i j '' C) ∪
          (⋃ i : Fin (n + 1), ⋃ j : Fin (n + 1),
            (fun g : upperUnipotent (n + 1) F => UpperUnipotent.entry i j (g⁻¹)) '' C)
        have hS : IsCompact S :=
          (isCompact_iUnion fun i => isCompact_iUnion fun j =>
            hC.image (UpperUnipotent.entry i j).continuous).union
          (isCompact_iUnion fun i => isCompact_iUnion fun j =>
            hC.image ((UpperUnipotent.entry i j).continuous.comp continuous_inv))
        obtain ⟨d, hd, hdi, hs⟩ := RankinSelberg.common_integer_denominator_of_isCompact S hS
        let D := scalingDiagonal n d hd
        let e := (Homeomorph.mulLeft D).trans (Homeomorph.mulRight D⁻¹)
        let f := (MulAut.conj D).toMonoidHom.comp (upperUnipotent (n + 1) F).subtype
        have hf : Continuous f := e.continuous.comp continuous_subtype_val
        let K := OpenSubgroup.comap f hf (Conductor.levelOpenSubgroup F n 0)
        refine ⟨K, ?_, ?_⟩
        · exact (e.isClosedEmbedding.comp
            (UpperUnipotent.isClosed (R := F) (n := n + 1)).isClosedEmbedding_subtypeVal).isCompact_preimage
              (Conductor.isCompact_levelOpenSubgroup F n 0)
        · intro g hg
          have hentries (i j : Fin (n + 1)) :
              d * g.val i j ∈ (ValuativeRel.valuation F).integer := by
            apply hs
            exact Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i,
              Set.mem_iUnion.mpr ⟨j, Set.mem_image_of_mem _ hg⟩⟩)
          have hinv (i j : Fin (n + 1)) :
              d * (g⁻¹).val i j ∈ (ValuativeRel.valuation F).integer := by
            apply hs
            exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i,
              Set.mem_iUnion.mpr ⟨j, Set.mem_image_of_mem _ hg⟩⟩)
          change f g ∈ Conductor.levelSubgroup F n 0
          rw [Conductor.levelSubgroup_zero, Conductor.mem_integralSubgroup]
          constructor
          · exact scalingDiagonal_conj_integral n d hd hdi g hentries
          · have he : (f g)⁻¹ = D * (g⁻¹).val * D⁻¹ := by
              simp [f, MulAut.conj_apply, mul_assoc]
            rw [he]
            exact scalingDiagonal_conj_integral n d hd hdi (g⁻¹) hinv
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

/-- Forgetting the choice and openness gives compact containment in the exact
form needed for character-localization exactness. -/
theorem localField_upperUnipotent_isLimitOfCompactSubgroups
    (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) :
    Jacquet.Localization.IsLimitOfCompactSubgroups (upperUnipotent n F) := by
  intro C hC
  obtain ⟨K, hK, hCK⟩ := localFieldUpperUnipotentCompactOpenSubgroup F n C hC
  exact ⟨K.toSubgroup, hK, hCK⟩

/-- The same compact-containment property for the actual upper subgroup inside
the mirabolic group, with its inherited topology. -/
theorem localField_mirabolicUpperUnipotent_isLimitOfCompactSubgroups
    (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) :
    Jacquet.Localization.IsLimitOfCompactSubgroups (Mirabolic.upperUnipotent n F) := by
  intro C hC
  let e := Mirabolic.upperUnipotentContinuousEquiv (F := F) (n := n)
  obtain ⟨K, hK, hCK⟩ := localFieldUpperUnipotentCompactOpenSubgroup F (n + 1)
    (e '' C) (hC.image e.continuous)
  refine ⟨K.toSubgroup.comap e.toMonoidHom, ?_, ?_⟩
  · exact e.toHomeomorph.isCompact_preimage.mpr hK
  · intro g hg
    exact hCK (Set.mem_image_of_mem e hg)

end Langlands.GeneralLinear
