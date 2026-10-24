import Langlands.Group.GL.UpperUnipotentCompactContainmentStatement
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity
import Langlands.Representation.Jacquet.LocalizationExactnessStatement

noncomputable section

namespace Langlands.RankinSelberg

universe uF

/-- A compact set of elements of a valuative topological field has one nonzero
integral common denominator. -/
theorem common_integer_denominator_of_isCompact {F : Type uF} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsValuativeTopology F] (C : Set F) (hC : IsCompact C) :
    ∃ d : F, d ≠ 0 ∧ d ∈ (ValuativeRel.valuation F).integer ∧
      ∀ x ∈ C, d * x ∈ (ValuativeRel.valuation F).integer := by
  classical
  let O := (ValuativeRel.valuation F).integer
  let D := {d : F // d ≠ 0 ∧ d ∈ O}
  let U (d : D) : Set F := {x | d.val * x ∈ O}
  have : Nonempty D := ⟨⟨1, one_ne_zero, O.one_mem⟩⟩
  have hopen (d : D) : IsOpen (U d) :=
    (ValuativeRel.valuation F).isOpen_integer.preimage (continuous_const.mul continuous_id)
  have hcover : C ⊆ ⋃ d : D, U d := by
    intro x _
    obtain ⟨d, hd, hdi, hx⟩ := common_integer_denominator ({x} : Finset F)
    exact Set.mem_iUnion.mpr ⟨⟨d, hd, hdi⟩, hx x (Finset.mem_singleton_self x)⟩
  have hdir : Directed (· ⊆ ·) U := by
    intro d e
    refine ⟨⟨d.val * e.val, mul_ne_zero d.property.1 e.property.1,
      O.mul_mem d.property.2 e.property.2⟩, ?_, ?_⟩
    · intro x hx
      change d.val * e.val * x ∈ O
      change d.val * x ∈ O at hx
      simpa only [mul_assoc, mul_left_comm, mul_comm] using O.mul_mem e.property.2 hx
    · intro x hx
      change d.val * e.val * x ∈ O
      change e.val * x ∈ O at hx
      simpa only [mul_assoc] using O.mul_mem d.property.2 hx
  obtain ⟨d, hd⟩ := hC.elim_directed_cover U hopen hcover hdir
  exact ⟨d.val, d.property.1, d.property.2, hd⟩

end Langlands.RankinSelberg

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

/-- Every compact subset of the actual upper-unipotent group is contained in a
compact open subgroup, for precisely the supplied compatible field topology. -/
theorem upperUnipotentCompactContainment : UpperUnipotentCompactContainmentStatement.{uF} := by
  intro p hp F T n
  let := hp
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  intro C hC
  cases n with
  | zero => exact ⟨⊤, Set.finite_univ.isCompact, fun _ _ => trivial⟩
  | succ n =>
      let S : Set F.Carrier :=
        (⋃ i : Fin (n + 1), ⋃ j : Fin (n + 1), UpperUnipotent.entry i j '' C) ∪
        (⋃ i : Fin (n + 1), ⋃ j : Fin (n + 1),
          (fun g : upperUnipotent (n + 1) F.Carrier => UpperUnipotent.entry i j (g⁻¹)) '' C)
      have hS : IsCompact S :=
        (isCompact_iUnion fun i => isCompact_iUnion fun j =>
          hC.image (UpperUnipotent.entry i j).continuous).union
        (isCompact_iUnion fun i => isCompact_iUnion fun j =>
          hC.image ((UpperUnipotent.entry i j).continuous.comp continuous_inv))
      obtain ⟨d, hd, hdi, hs⟩ := RankinSelberg.common_integer_denominator_of_isCompact S hS
      let D := scalingDiagonal n d hd
      let e := (Homeomorph.mulLeft D).trans (Homeomorph.mulRight D⁻¹)
      let f := (MulAut.conj D).toMonoidHom.comp (upperUnipotent (n + 1) F.Carrier).subtype
      have hf : Continuous f := e.continuous.comp continuous_subtype_val
      let K := OpenSubgroup.comap f hf (Conductor.levelOpenSubgroup F.Carrier n 0)
      refine ⟨K, ?_, ?_⟩
      · exact (e.isClosedEmbedding.comp
          (UpperUnipotent.isClosed (R := F.Carrier) (n := n + 1)).isClosedEmbedding_subtypeVal).isCompact_preimage
            (Conductor.isCompact_levelOpenSubgroup F.Carrier n 0)
      · intro g hg
        have hentries (i j : Fin (n + 1)) :
            d * g.val i j ∈ (ValuativeRel.valuation F.Carrier).integer := by
          apply hs
          exact Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i,
            Set.mem_iUnion.mpr ⟨j, Set.mem_image_of_mem _ hg⟩⟩)
        have hinv (i j : Fin (n + 1)) :
            d * (g⁻¹).val i j ∈ (ValuativeRel.valuation F.Carrier).integer := by
          apply hs
          exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i,
            Set.mem_iUnion.mpr ⟨j, Set.mem_image_of_mem _ hg⟩⟩)
        change f g ∈ Conductor.levelSubgroup F.Carrier n 0
        rw [Conductor.levelSubgroup_zero, Conductor.mem_integralSubgroup]
        constructor
        · exact scalingDiagonal_conj_integral n d hd hdi g hentries
        · have he : (f g)⁻¹ = D * (g⁻¹).val * D⁻¹ := by
            simp [f, MulAut.conj_apply, mul_assoc]
          rw [he]
          exact scalingDiagonal_conj_integral n d hd hdi (g⁻¹) hinv

/-- Forgetting openness supplies the literal compact-subgroup hypothesis of
character localization for the actual upper-unipotent subgroup. -/
theorem upperUnipotent_isLimitOfCompactSubgroups {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    Jacquet.Localization.IsLimitOfCompactSubgroups (upperUnipotent n F.Carrier) := by
  let := T.topology
  intro C hC
  obtain ⟨K, hK, hCK⟩ := upperUnipotentCompactContainment p inferInstance F T n C hC
  exact ⟨K.toSubgroup, hK, hCK⟩

end Langlands.GeneralLinear
