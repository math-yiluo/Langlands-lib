import Langlands.Group.GL.MirabolicProjection
import Langlands.Representation.Shahidi.TwoBlocks
import Langlands.Representation.Whittaker.EntrywiseCharacter

/-! # Concrete matrix data for partial character localization -/

namespace Langlands.Derivative.PartialLocalization

open GeneralLinear

universe uF

variable {F : Type uF} [CommRing F] {k m : ℕ}

private theorem mul_fixed_column (A B : Matrix (Fin (k + m)) (Fin (k + m)) F)
    (j : Fin k)
    (hB : ∀ i, B i (j.castAdd m) = if i = j.castAdd m then 1 else 0)
    (i : Fin (k + m)) :
    (A * B) i (j.castAdd m) = A i (j.castAdd m) := by
  simp only [Matrix.mul_apply, hB]
  simp

/-- Matrices fixing each of the first `k` standard coordinate vectors. -/
def fixedColumns (k m : ℕ) (F : Type uF) [CommRing F] :
    Subgroup (GeneralLinear (k + m) F) where
  carrier := {g | ∀ (i : Fin (k + m)) (j : Fin k),
    g i (j.castAdd m) = if i = j.castAdd m then 1 else 0}
  one_mem' := by
    intro i j
    simp [Matrix.one_apply]
  mul_mem' := by
    intro g h hg hh i j
    change (g.val * h.val) i (j.castAdd m) = _
    rw [mul_fixed_column _ _ j (fun i => hh i j), hg i j]
  inv_mem' := by
    intro g hg i j
    have he := mul_fixed_column (g⁻¹).val g.val j (fun i => hg i j) i
    rw [g.inv_mul] at he
    simpa only [Matrix.one_apply] using he.symm

/-- The actual group `[[I_k,A],[0,u_m]]`, defined in all natural ranks. -/
def partialUpper (k m : ℕ) (F : Type uF) [CommRing F] :
    Subgroup (GeneralLinear (k + m) F) :=
  GeneralLinear.upperUnipotent (k + m) F ⊓ fixedColumns k m F

theorem partialUpper_le_upper :
    partialUpper k m F ≤ GeneralLinear.upperUnipotent (k + m) F :=
  inf_le_left

theorem fixedColumn (g : partialUpper k m F) (i : Fin (k + m)) (j : Fin k) :
    g.val i (j.castAdd m) = if i = j.castAdd m then 1 else 0 :=
  g.property.2 i j

@[simp] theorem firstBlock (g : partialUpper k m F) (i j : Fin k) :
    g.val (i.castAdd m) (j.castAdd m) = if i = j then 1 else 0 := by
  rw [fixedColumn]
  simp

@[simp] theorem lowerLeft (g : partialUpper k m F) (i : Fin m) (j : Fin k) :
    g.val (i.natAdd k) (j.castAdd m) = 0 := by
  rw [fixedColumn]
  have he : i.natAdd k ≠ j.castAdd m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega
  simp [he]

private theorem trailingBlock_mul (g h : GeneralLinear.upperUnipotent (k + m) F) :
    (g.val.val * h.val.val).submatrix (Fin.natAdd k) (Fin.natAdd k) =
      g.val.val.submatrix (Fin.natAdd k) (Fin.natAdd k) *
        h.val.val.submatrix (Fin.natAdd k) (Fin.natAdd k) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_add]
  have hz : (∑ a : Fin k, g.val (i.natAdd k) (a.castAdd m) *
      h.val (a.castAdd m) (j.natAdd k)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    rw [UpperUnipotent.entry_eq_zero g (by
      simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
      omega), zero_mul]
  rw [hz, zero_add]

private theorem trailingBlock_one :
    (1 : Matrix (Fin (k + m)) (Fin (k + m)) F).submatrix
      (Fin.natAdd k) (Fin.natAdd k) = 1 := by
  ext i j
  simp [Matrix.one_apply]

/-- Extract the actual invertible final block of a full upper-unipotent matrix. -/
def upperFinalProjection :
    GeneralLinear.upperUnipotent (k + m) F →* GeneralLinear.upperUnipotent m F where
  toFun g :=
    ⟨{ val := g.val.val.submatrix (Fin.natAdd k) (Fin.natAdd k)
       inv := (g⁻¹).val.val.submatrix (Fin.natAdd k) (Fin.natAdd k)
       val_inv := by
         rw [← trailingBlock_mul]
         change (g * g⁻¹).val.val.submatrix _ _ = 1
         rw [mul_inv_cancel]
         exact trailingBlock_one
       inv_val := by
         rw [← trailingBlock_mul]
         change (g⁻¹ * g).val.val.submatrix _ _ = 1
         rw [inv_mul_cancel]
         exact trailingBlock_one },
     ⟨fun _ _ hij => g.property.1 (Nat.add_lt_add_left hij k),
       fun i => g.property.2 (i.natAdd k)⟩⟩
  map_one' := Subtype.ext (Units.ext trailingBlock_one)
  map_mul' g h := Subtype.ext (Units.ext (trailingBlock_mul g h))

/-- The final upper-unipotent block of the partial localization group. -/
def finalProjection :
    partialUpper k m F →* GeneralLinear.upperUnipotent m F :=
  upperFinalProjection.comp
    (Subgroup.inclusion (partialUpper_le_upper (k := k) (m := m) (F := F)))

@[simp] theorem finalProjection_apply (g : partialUpper k m F) (i j : Fin m) :
    (finalProjection g).val i j = g.val (i.natAdd k) (j.natAdd k) := rfl

theorem blockSum_mem_partialUpper (u : GeneralLinear.upperUnipotent m F) :
    blockSum ((1 : GeneralLinear k F), u.val) ∈ partialUpper k m F := by
  constructor
  · constructor
    · intro i j hij
      induction i using Fin.addCases <;> induction j using Fin.addCases
      · rename_i a b
        rw [blockSum_apply_left]
        have hab : a ≠ b := by
          intro h
          subst b
          exact (lt_irrefl _ hij)
        simp [hab]
      · exact blockSum_apply_left_right _ _ _ _
      · exact blockSum_apply_right_left _ _ _ _
      · rename_i a b
        rw [blockSum_apply_right]
        exact u.property.1 (by
          change k + b.val < k + a.val at hij
          exact Nat.lt_of_add_lt_add_left hij)
    · intro i
      induction i using Fin.addCases
      · simp
      · exact (blockSum_apply_right _ _ _ _).trans (u.property.2 _)
  · intro i j
    induction i using Fin.addCases
    · simp [Matrix.one_apply]
    · rename_i i
      rw [blockSum_apply_right_left]
      have he : i.natAdd k ≠ j.castAdd m := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        omega
      simp [he]

/-- Include the actual final upper block, with the first block equal to identity. -/
def finalLevi : GeneralLinear.upperUnipotent m F →* partialUpper k m F :=
  (blockSum.comp
    { toFun u := (1, u.val)
      map_one' := rfl
      map_mul' _ _ := by simp }).codRestrict _ blockSum_mem_partialUpper

@[simp] theorem finalLevi_val (u : GeneralLinear.upperUnipotent m F) :
    (finalLevi (k := k) u).val = blockSum ((1 : GeneralLinear k F), u.val) := rfl

@[simp] theorem finalProjection_finalLevi (u : GeneralLinear.upperUnipotent m F) :
    finalProjection (finalLevi (k := k) u) = u := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact blockSum_apply_right _ _ i j

/-- The character is the published adjacent-entry character on the final block. -/
def character (ψ : AddChar F ℂ) (k m : ℕ) : partialUpper k m F →* ℂˣ :=
  (Whittaker.entrywiseCharacter ψ m).comp finalProjection

@[simp] theorem character_succ (ψ : AddChar F ℂ) (k m : ℕ)
    (g : partialUpper k (m + 1) F) :
    (character ψ k (m + 1) g : ℂ) =
      ψ (∑ i : Fin m, g.val (i.castSucc.natAdd k) (i.succ.natAdd k)) := rfl

@[simp] theorem character_finalLevi (ψ : AddChar F ℂ)
    (u : GeneralLinear.upperUnipotent m F) :
    character ψ k m (finalLevi u) = Whittaker.entrywiseCharacter ψ m u := by
  change Whittaker.entrywiseCharacter ψ m (finalProjection (finalLevi u)) = _
  rw [finalProjection_finalLevi]

section Mirabolic

open GeneralLinear.Mirabolic

/-- The actual partial upper group, viewed inside its ambient mirabolic. -/
def mirabolicPartialUpper (k m : ℕ) (F : Type uF) [CommRing F] :
    Subgroup (mirabolic (k + m) F) :=
  (partialUpper k (m + 1) F).comap (mirabolic (k + m) F).subtype

theorem partialUpper_le_mirabolic :
    partialUpper k (m + 1) F ≤ mirabolic (k + m) F :=
  partialUpper_le_upper.trans upperUnipotent_le_mirabolic

/-- The smaller partial upper group in the actual mirabolic Levi range. -/
def partialLeviSubgroup (k m : ℕ) (F : Type uF) [CommRing F] :
    Subgroup (mirabolic (k + m) F) :=
  (partialUpper k m F).map levi

theorem projection_mem_partialUpper (g : mirabolicPartialUpper k m F) :
    projection g.val ∈ partialUpper k m F := by
  constructor
  · constructor
    · intro i j hij
      exact g.property.1.1 hij
    · intro i
      exact g.property.1.2 i.castSucc
  · intro i j
    have hg := g.property.2 i.castSucc j
    change g.val.val.val i.castSucc (j.castAdd (m + 1)) = _ at hg
    change g.val.val.val i.castSucc ((j.castAdd m).castSucc) = _
    simpa only [← Fin.castSucc_castAdd, Fin.castSucc_inj] using hg

theorem levi_mem_partialUpper (g : partialUpper k m F) :
    levi g.val ∈ mirabolicPartialUpper k m F := by
  change (levi g.val).val ∈ partialUpper k (m + 1) F
  constructor
  · constructor
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact (lt_irrefl _ hij).elim
      · rename_i j
        exact (levi _).property j.castSucc |>.trans (by simp)
      · exact (not_lt_of_ge (Fin.le_last _) hij).elim
      · exact (levi_first _ _ _).trans (g.property.1.1 hij)
    · intro i
      change (levi g.val).val.val i i = 1
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact (levi_bottom _ _).trans (ite_eq_left rfl)
      · exact (levi_first _ _ _).trans (g.property.1.2 _)
  · intro i j
    change (levi g.val).val.val i (j.castAdd (m + 1)) = _
    rw [← Fin.castSucc_castAdd]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · exact (levi_bottom g.val _).trans (by
        simp [(Fin.castSucc_ne_last _).symm, Fin.castSucc_ne_last])
    · rw [levi_first, g.property.2]
      simp

theorem radical_le_partialUpper :
    radical (k + m) F ≤ mirabolicPartialUpper k m F := by
  intro g hg
  constructor
  · exact radical_le_upperUnipotent hg
  · intro i j
    exact hg i (j.castAdd m)

theorem partialLeviSubgroup_le_partialUpper :
    partialLeviSubgroup k m F ≤ mirabolicPartialUpper k m F := by
  rintro _ ⟨g, hg, rfl⟩
  exact levi_mem_partialUpper ⟨g, hg⟩

/-- The successive actual final-column radical and smaller Levi group generate
precisely the partial upper group. -/
theorem partialUpper_eq_radical_sup :
    mirabolicPartialUpper k m F =
      radical (k + m) F ⊔ partialLeviSubgroup k m F := by
  apply le_antisymm
  · intro g hg
    rw [eq_radicalElement_mul_levi g]
    exact mul_mem (Subgroup.mem_sup_left (radicalElement _).property)
      (Subgroup.mem_sup_right
        ⟨projection g, projection_mem_partialUpper ⟨g, hg⟩, rfl⟩)
  · exact sup_le radical_le_partialUpper partialLeviSubgroup_le_partialUpper

end Mirabolic

section TwoBlocks

variable (hk : 0 < k) (hm : 0 < m)

theorem partialUpper_le_parabolic :
    partialUpper k m F ≤ (Shahidi.twoBlocks k m hk hm).parabolic F := by
  intro g hg
  apply (Shahidi.twoBlocks_mem_parabolic_iff hk hm F g).mpr
  exact lowerLeft ⟨g, hg⟩

theorem parabolicRadical_le_partialUpper :
    (Shahidi.twoBlocks k m hk hm).unipotentSubgroup F ≤ partialUpper k m F := by
  intro g hg
  obtain ⟨hp, hd⟩ :=
    ((Shahidi.twoBlocks k m hk hm).mem_unipotentSubgroup_iff F g).mp hg
  have h00 (i j : Fin k) : g (i.castAdd m) (j.castAdd m) = if i = j then 1 else 0 := by
    have h := hd 0 i j
    rw [Shahidi.twoBlocks_index_first hk hm, Shahidi.twoBlocks_index_first hk hm] at h
    exact h
  have h11 (i j : Fin m) : g (i.natAdd k) (j.natAdd k) = if i = j then 1 else 0 := by
    have h := hd 1 i j
    rw [Shahidi.twoBlocks_index_second hk hm, Shahidi.twoBlocks_index_second hk hm] at h
    exact h
  have h10 := (Shahidi.twoBlocks_mem_parabolic_iff hk hm F g).mp hp
  constructor
  · constructor
    · intro i j hij
      induction i using Fin.addCases <;> induction j using Fin.addCases
      · rw [h00]
        apply ite_eq_right
        intro he
        subst he
        exact (lt_irrefl _ hij)
      · exfalso
        rename_i i j
        change k + j.val < i.val at hij
        omega
      · exact h10 _ _
      · rw [h11]
        apply ite_eq_right
        intro he
        subst he
        exact (lt_irrefl _ hij)
    · intro i
      induction i using Fin.addCases
      · exact (h00 _ _).trans (ite_eq_left rfl)
      · exact (h11 _ _).trans (ite_eq_left rfl)
  · intro i j
    induction i using Fin.addCases
    · simpa only [Fin.castAdd_inj] using h00 _ j
    · rename_i i
      rw [h10]
      have he : i.natAdd k ≠ j.castAdd m := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        omega
      simp [he]

/-- The embedded final upper-unipotent factor, as a subgroup of the actual GL. -/
def finalLeviRange (k m : ℕ) (F : Type uF) [CommRing F] :
    Subgroup (GeneralLinear (k + m) F) :=
  ((partialUpper k m F).subtype.comp finalLevi).range

theorem finalLeviRange_le_partialUpper :
    finalLeviRange k m F ≤ partialUpper k m F := by
  rintro _ ⟨u, rfl⟩
  exact (finalLevi u).property

theorem leviProjection_first_eq_one (g : partialUpper k m F) :
    (Shahidi.twoBlocks k m hk hm).leviProjection F
      ⟨g.val, partialUpper_le_parabolic hk hm g.property⟩ 0 = 1 := by
  apply Units.ext
  ext i j
  exact (Shahidi.twoBlocks_leviProjection_first hk hm F _ i j).trans
    ((firstBlock g i j).trans Matrix.one_apply.symm)

theorem leviProjection_second_eq_final (g : partialUpper k m F) :
    (Shahidi.twoBlocks k m hk hm).leviProjection F
      ⟨g.val, partialUpper_le_parabolic hk hm g.property⟩ 1 =
        (finalProjection g).val := by
  apply Units.ext
  ext i j
  exact Shahidi.twoBlocks_leviProjection_second hk hm F _ i j

/-- The parabolic radical and the upper group of its final block generate exactly
the same actual subgroup as the successive mirabolic radicals. -/
theorem partialUpper_eq_parabolicRadical_sup :
    partialUpper k m F =
      (Shahidi.twoBlocks k m hk hm).unipotentSubgroup F ⊔ finalLeviRange k m F := by
  apply le_antisymm
  · intro g hg
    let gp : (Shahidi.twoBlocks k m hk hm).parabolic F :=
      ⟨g, partialUpper_le_parabolic hk hm hg⟩
    have he : (Shahidi.twoBlocks k m hk hm).leviEmbedding F
        ((Shahidi.twoBlocks k m hk hm).leviProjection F gp) =
          (finalLevi (k := k) (finalProjection ⟨g, hg⟩)).val := by
      rw [Shahidi.twoBlocks_leviEmbedding, finalLevi_val]
      exact congrArg blockSum (Prod.ext
        (leviProjection_first_eq_one hk hm ⟨g, hg⟩)
        (leviProjection_second_eq_final hk hm ⟨g, hg⟩))
    have hdec := congrArg Subtype.val
      (((Shahidi.twoBlocks k m hk hm).decomposition F).symm_apply_apply gp)
    change ((Shahidi.twoBlocks k m hk hm).unipotentPart F gp).val.val *
      (Shahidi.twoBlocks k m hk hm).leviEmbedding F
        ((Shahidi.twoBlocks k m hk hm).leviProjection F gp) = g at hdec
    rw [he] at hdec
    rw [← hdec]
    exact mul_mem
      (Subgroup.mem_sup_left ⟨_, ((Shahidi.twoBlocks k m hk hm).unipotentPart F gp).property, rfl⟩)
      (Subgroup.mem_sup_right ⟨finalProjection ⟨g, hg⟩, rfl⟩)
  · exact sup_le (parabolicRadical_le_partialUpper hk hm) finalLeviRange_le_partialUpper

theorem finalProjection_radical
    (u : (Shahidi.twoBlocks k m hk hm).unipotentSubgroup F) :
    finalProjection ⟨u.val, parabolicRadical_le_partialUpper hk hm u.property⟩ = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hd := (((Shahidi.twoBlocks k m hk hm).mem_unipotentSubgroup_iff F u.val).mp
    u.property).2 1 i j
  rw [Shahidi.twoBlocks_index_second hk hm, Shahidi.twoBlocks_index_second hk hm] at hd
  exact hd.trans Matrix.one_apply.symm

theorem character_radical (ψ : AddChar F ℂ)
    (u : (Shahidi.twoBlocks k m hk hm).unipotentSubgroup F) :
    character ψ k m ⟨u.val, parabolicRadical_le_partialUpper hk hm u.property⟩ = 1 := by
  change Whittaker.entrywiseCharacter ψ m (finalProjection _) = 1
  rw [finalProjection_radical hk hm, map_one]

end TwoBlocks

section Topology

variable [TopologicalSpace F]

theorem continuous_finalProjection :
    Continuous (finalProjection (k := k) (m := m) (F := F)) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · exact (Units.continuous_val.comp continuous_subtype_val).matrix_submatrix _ _
  · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_submatrix _ _

theorem continuous_finalLevi :
    Continuous (finalLevi (k := k) (m := m) (F := F)) :=
  (blockSumContinuous.continuous.comp
    (continuous_const.prodMk continuous_subtype_val)).subtype_mk _

end Topology

end Langlands.Derivative.PartialLocalization
