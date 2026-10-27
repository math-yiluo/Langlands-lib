import Langlands.Group.GL.MirabolicRadical

/-! # The mirabolic projection and the actual plus-induction subgroup -/

namespace Langlands.GeneralLinear.Mirabolic

universe u

variable {F : Type u} [CommRing F] {n : ℕ}

/-- The defining last-row equations of a mirabolic matrix. -/
private theorem lastRow (g : mirabolic n F) (j : Fin (n + 1)) :
    g.val.val (Fin.last n) j = if j = Fin.last n then 1 else 0 :=
  g.property j

/-- A product's upper-left block is the product of upper-left blocks when the
second factor has the mirabolic last row. -/
private theorem upperLeft_mul (g h : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (hh : ∀ j, h (Fin.last n) j = if j = Fin.last n then 1 else 0) :
    (g * h).submatrix Fin.castSucc Fin.castSucc =
      g.submatrix Fin.castSucc Fin.castSucc * h.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hh, Fin.castSucc_ne_last]

private theorem upperLeft_one :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F).submatrix Fin.castSucc Fin.castSucc = 1 := by
  ext i j
  simp [Matrix.one_apply]

/-- The upper-left `n × n` block `g ↦ A` of `g = [[A,v],[0,1]]`, with inverse the
upper-left block of the actual mirabolic inverse. -/
def projection : mirabolic n F →* Langlands.GeneralLinear n F where
  toFun g :=
    { val := g.val.val.submatrix Fin.castSucc Fin.castSucc
      inv := (g⁻¹).val.val.submatrix Fin.castSucc Fin.castSucc
      val_inv := by
        rw [← upperLeft_mul _ _ (lastRow g⁻¹)]
        change ((g * g⁻¹).val.val).submatrix _ _ = 1
        rw [mul_inv_cancel]
        exact upperLeft_one
      inv_val := by
        rw [← upperLeft_mul _ _ (lastRow g)]
        change ((g⁻¹ * g).val.val).submatrix _ _ = 1
        rw [inv_mul_cancel]
        exact upperLeft_one }
  map_one' := Units.ext upperLeft_one
  map_mul' g h := Units.ext (upperLeft_mul _ _ (lastRow h))

@[simp] theorem projection_apply (g : mirabolic n F) (i j : Fin n) :
    (projection g).val i j = g.val.val i.castSucc j.castSucc := rfl

/-- The inverse entries are those of the actual mirabolic inverse. -/
@[simp] theorem projection_inv_apply (g : mirabolic n F) (i j : Fin n) :
    ((projection g)⁻¹).val i j = (g⁻¹).val.val i.castSucc j.castSucc := rfl

@[simp] theorem projection_levi (a : Langlands.GeneralLinear n F) :
    projection (levi a) = a := by
  apply Units.ext
  ext i j
  exact levi_first a i j

theorem projection_surjective : Function.Surjective (projection (n := n) (F := F)) :=
  fun a => ⟨levi a, projection_levi a⟩

@[simp] theorem projection_successor (g : mirabolic n F) :
    projection (successor g) = g.val :=
  projection_levi g.val

@[simp] theorem projection_radicalElement (v : Fin n → F) :
    projection (radicalElement v).val = 1 := by
  apply Units.ext
  ext i j
  simp [Matrix.one_apply]

/-- The kernel of the projection is exactly the published actual radical. -/
theorem ker_projection : (projection (n := n) (F := F)).ker = radical n F := by
  ext g
  rw [MonoidHom.mem_ker, mem_radical]
  constructor
  · intro h i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [lastRow g j.castSucc]
      simp [Fin.castSucc_ne_last, (Fin.castSucc_ne_last j).symm]
    · have hij := congrArg (fun a : Langlands.GeneralLinear n F => a.val i j) h
      simpa [Matrix.one_apply] using hij
  · intro h
    apply Units.ext
    ext i j
    simp [h i.castSucc j, Matrix.one_apply]

theorem projection_eq_one_iff (g : mirabolic n F) :
    projection g = 1 ↔ g ∈ radical n F := by
  rw [← MonoidHom.mem_ker, ker_projection]

/-- The radical is normal, being the kernel of the actual projection. -/
instance radical_normal : (radical n F).Normal := by
  rw [← ker_projection]
  infer_instance

/-- The final column above the last diagonal entry. -/
def lastColumn (g : mirabolic n F) : Fin n → F :=
  fun i => g.val.val i.castSucc (Fin.last n)

@[simp] theorem lastColumn_apply (g : mirabolic n F) (i : Fin n) :
    lastColumn g i = g.val.val i.castSucc (Fin.last n) := rfl

/-- On the radical, `lastColumn` is the published radical coordinate map. -/
theorem lastColumn_val (u : radical n F) : lastColumn u.val = radicalCoordinates u := rfl

@[simp] theorem lastColumn_radicalElement (v : Fin n → F) :
    lastColumn (radicalElement v).val = v :=
  radicalCoordinates_element v

@[simp] theorem lastColumn_levi (a : Langlands.GeneralLinear n F) :
    lastColumn (levi a) = 0 :=
  funext (levi_last a)

@[simp] theorem lastColumn_one : lastColumn (1 : mirabolic n F) = 0 := by
  rw [← map_one levi, lastColumn_levi]

/-- `(g*h)` has final column `A_g v_h + v_g`, where `A_g = projection g`. -/
theorem lastColumn_mul (g h : mirabolic n F) :
    lastColumn (g * h) = (projection g).val.mulVec (lastColumn h) + lastColumn g := by
  funext i
  change (g.val.val * h.val.val) i.castSucc (Fin.last n) = _
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, lastRow h, Matrix.mulVec, dotProduct]

@[simp] theorem projection_radicalElement_mul_levi (v : Fin n → F)
    (a : Langlands.GeneralLinear n F) :
    projection ((radicalElement v).val * levi a) = a := by
  rw [map_mul, projection_radicalElement, projection_levi, one_mul]

@[simp] theorem lastColumn_radicalElement_mul_levi (v : Fin n → F)
    (a : Langlands.GeneralLinear n F) :
    lastColumn ((radicalElement v).val * levi a) = v := by
  rw [lastColumn_mul, projection_radicalElement, lastColumn_levi, Matrix.mulVec_zero,
    zero_add, lastColumn_radicalElement]

/-- Every mirabolic matrix is `u(v) * diag(A,1)`, radical factor first. -/
theorem eq_radicalElement_mul_levi (g : mirabolic n F) :
    g = (radicalElement (lastColumn g)).val * levi (projection g) := by
  have hmem : g * (levi (projection g))⁻¹ ∈ radical n F := by
    rw [← projection_eq_one_iff, map_mul, map_inv, projection_levi, mul_inv_cancel]
  have hcol : lastColumn (g * (levi (projection g))⁻¹) = lastColumn g := by
    rw [lastColumn_mul, ← map_inv, lastColumn_levi, Matrix.mulVec_zero, zero_add]
  have he : (radicalElement (lastColumn g)).val = g * (levi (projection g))⁻¹ := by
    rw [← hcol]
    exact congrArg Subtype.val (radicalElement_coordinates ⟨_, hmem⟩)
  rw [he, inv_mul_cancel_right]

/-- The radical-then-Levi coordinates are unique. -/
theorem eq_radicalElement_mul_levi_iff (g : mirabolic n F) (v : Fin n → F)
    (a : Langlands.GeneralLinear n F) :
    g = (radicalElement v).val * levi a ↔ v = lastColumn g ∧ a = projection g := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨rfl, rfl⟩
    exact eq_radicalElement_mul_levi g

/-- Radical-then-Levi coordinates, as an equivalence of sets only. -/
def radicalLeviEquiv : mirabolic n F ≃ (Fin n → F) × Langlands.GeneralLinear n F where
  toFun g := (lastColumn g, projection g)
  invFun p := (radicalElement p.1).val * levi p.2
  left_inv g := (eq_radicalElement_mul_levi g).symm
  right_inv p := Prod.ext (lastColumn_radicalElement_mul_levi p.1 p.2)
    (projection_radicalElement_mul_levi p.1 p.2)

@[simp] theorem radicalLeviEquiv_apply (g : mirabolic n F) :
    radicalLeviEquiv g = (lastColumn g, projection g) := rfl

@[simp] theorem radicalLeviEquiv_symm_apply (p : (Fin n → F) × Langlands.GeneralLinear n F) :
    radicalLeviEquiv.symm p = (radicalElement p.1).val * levi p.2 := rfl

/-- The source's `P_(n+1) V_(n+2)` inside `P_(n+2)`: the upper-left block is mirabolic. -/
def plusSubgroup (n : ℕ) (F : Type u) [CommRing F] : Subgroup (mirabolic (n + 1) F) :=
  (mirabolic n F).comap projection

@[simp] theorem mem_plusSubgroup (g : mirabolic (n + 1) F) :
    g ∈ plusSubgroup n F ↔ projection g ∈ mirabolic n F := Iff.rfl

/-- Entrywise: row `n` of the `(n+2) × (n+2)` matrix is `(0, …, 0, 1, *)`. -/
theorem mem_plusSubgroup_iff_entry (g : mirabolic (n + 1) F) :
    g ∈ plusSubgroup n F ↔ ∀ j : Fin (n + 1),
      g.val.val (Fin.last n).castSucc j.castSucc = if j = Fin.last n then 1 else 0 :=
  Iff.rfl

theorem successor_mem_plusSubgroup (g : mirabolic n F) : successor g ∈ plusSubgroup n F := by
  rw [mem_plusSubgroup, projection_successor]
  exact g.property

theorem radical_le_plusSubgroup : radical (n + 1) F ≤ plusSubgroup n F := by
  intro g hg
  rw [mem_plusSubgroup, (projection_eq_one_iff g).mpr hg]
  exact one_mem _

theorem successorSubgroup_le_plusSubgroup : successorSubgroup n F ≤ plusSubgroup n F := by
  rintro _ ⟨g, rfl⟩
  exact successor_mem_plusSubgroup g

/-- Restriction of `projection` to the plus subgroup, valued in the smaller mirabolic. -/
def plusProjection : plusSubgroup n F →* mirabolic n F :=
  (projection.comp (plusSubgroup n F).subtype).codRestrict (mirabolic n F) fun g => g.property

@[simp] theorem plusProjection_val (g : plusSubgroup n F) :
    (plusProjection g).val = projection g.val := rfl

@[simp] theorem plusProjection_apply (g : plusSubgroup n F) (i j : Fin (n + 1)) :
    (plusProjection g).val.val i j = g.val.val.val i.castSucc j.castSucc := rfl

/-- The successor map as a homomorphism into the plus subgroup. -/
def plusSuccessor : mirabolic n F →* plusSubgroup n F :=
  successor.codRestrict (plusSubgroup n F) successor_mem_plusSubgroup

@[simp] theorem plusSuccessor_val (g : mirabolic n F) :
    (plusSuccessor g).val = successor g := rfl

/-- The radical inclusion into the plus subgroup. -/
def plusRadical : radical (n + 1) F →* plusSubgroup n F :=
  Subgroup.inclusion radical_le_plusSubgroup

@[simp] theorem plusRadical_val (u : radical (n + 1) F) :
    (plusRadical u).val = u.val := rfl

@[simp] theorem plusProjection_plusSuccessor (g : mirabolic n F) :
    plusProjection (plusSuccessor g) = g :=
  Subtype.ext (projection_successor g)

theorem plusProjection_comp_plusSuccessor :
    (plusProjection (n := n) (F := F)).comp plusSuccessor = MonoidHom.id _ :=
  MonoidHom.ext plusProjection_plusSuccessor

theorem plusProjection_surjective :
    Function.Surjective (plusProjection (n := n) (F := F)) :=
  fun g => ⟨plusSuccessor g, plusProjection_plusSuccessor g⟩

@[simp] theorem plusProjection_plusRadical (u : radical (n + 1) F) :
    plusProjection (plusRadical u) = 1 :=
  Subtype.ext ((projection_eq_one_iff u.val).mpr u.property)

/-- The kernel of `plusProjection` is the actual radical. -/
theorem ker_plusProjection :
    (plusProjection (n := n) (F := F)).ker = (radical (n + 1) F).subgroupOf (plusSubgroup n F) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← projection_eq_one_iff,
    ← plusProjection_val, OneMemClass.coe_eq_one]

/-- Every plus element is an actual radical matrix times a successor matrix. -/
theorem plus_eq_radicalElement_mul_successor (g : plusSubgroup n F) :
    g.val = (radicalElement (lastColumn g.val)).val * successor (plusProjection g) :=
  eq_radicalElement_mul_levi g.val

theorem plus_eq_plusRadical_mul_plusSuccessor (g : plusSubgroup n F) :
    g = plusRadical (radicalElement (lastColumn g.val)) * plusSuccessor (plusProjection g) :=
  Subtype.ext (plus_eq_radicalElement_mul_successor g)

theorem mem_plusSubgroup_iff_exists (g : mirabolic (n + 1) F) :
    g ∈ plusSubgroup n F ↔
      ∃ (v : Fin (n + 1) → F) (p : mirabolic n F), g = (radicalElement v).val * successor p := by
  constructor
  · intro hg
    exact ⟨_, _, plus_eq_radicalElement_mul_successor ⟨g, hg⟩⟩
  · rintro ⟨v, p, rfl⟩
    exact mul_mem (radical_le_plusSubgroup (radicalElement v).property)
      (successor_mem_plusSubgroup p)

theorem plusSubgroup_eq_sup :
    plusSubgroup n F = radical (n + 1) F ⊔ successorSubgroup n F := by
  apply le_antisymm
  · intro g hg
    obtain ⟨v, p, rfl⟩ := (mem_plusSubgroup_iff_exists g).mp hg
    exact mul_mem (Subgroup.mem_sup_left (radicalElement v).property)
      (Subgroup.mem_sup_right ⟨p, rfl⟩)
  · exact sup_le radical_le_plusSubgroup successorSubgroup_le_plusSubgroup

/-- Boundary rank: `P_1 V_2 = V_2` inside `P_2`, since `P_1` is trivial. -/
theorem plusSubgroup_zero : plusSubgroup 0 F = radical 1 F := by
  have hbot : successorSubgroup 0 F = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨g, rfl⟩
    rw [Subsingleton.elim g 1, map_one]
    exact one_mem _
  rw [plusSubgroup_eq_sup, hbot, sup_bot_eq]

/-- On the plus subgroup the final coordinate of `lastColumn` is additive. -/
theorem lastColumn_mul_last (g h : plusSubgroup n F) :
    lastColumn (g * h).val (Fin.last n) =
      lastColumn g.val (Fin.last n) + lastColumn h.val (Fin.last n) := by
  have hg : ∀ j, (projection g.val).val (Fin.last n) j = if j = Fin.last n then 1 else 0 :=
    g.property
  change lastColumn (g.val * h.val) (Fin.last n) = _
  rw [lastColumn_mul, Pi.add_apply, add_comm]
  congr 1
  simp [Matrix.mulVec, dotProduct, hg]

/-- Radical-then-successor coordinates on the plus subgroup, as sets only. -/
def radicalSuccessorEquiv : plusSubgroup n F ≃ (Fin (n + 1) → F) × mirabolic n F where
  toFun g := (lastColumn g.val, plusProjection g)
  invFun p := ⟨(radicalElement p.1).val * successor p.2,
    (mem_plusSubgroup_iff_exists _).mpr ⟨p.1, p.2, rfl⟩⟩
  left_inv g := Subtype.ext (plus_eq_radicalElement_mul_successor g).symm
  right_inv p := Prod.ext (lastColumn_radicalElement_mul_levi p.1 p.2.val)
    (Subtype.ext (projection_radicalElement_mul_levi p.1 p.2.val))

@[simp] theorem radicalSuccessorEquiv_apply (g : plusSubgroup n F) :
    radicalSuccessorEquiv g = (lastColumn g.val, plusProjection g) := rfl

@[simp] theorem radicalSuccessorEquiv_symm_apply_val
    (p : (Fin (n + 1) → F) × mirabolic n F) :
    (radicalSuccessorEquiv.symm p).val = (radicalElement p.1).val * successor p.2 := rfl

section Topology

variable [TopologicalSpace F]

/-- Continuity uses only the topology on units, not continuity of ring operations. -/
theorem continuous_projection : Continuous (projection (n := n) (F := F)) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    intro i j
    exact (entry (F := F) i.castSucc j.castSucc).continuous
  · apply continuous_matrix
    intro i j
    exact ((continuous_apply j.castSucc).comp ((continuous_apply i.castSucc).comp
      (show Continuous (fun g : Langlands.GeneralLinear (n + 1) F => (g⁻¹).val) from
        Units.continuous_coe_inv))).comp continuous_subtype_val

theorem continuous_lastColumn : Continuous (lastColumn (n := n) (F := F)) :=
  continuous_pi fun i => (entry (F := F) i.castSucc (Fin.last n)).continuous

theorem continuous_plusProjection : Continuous (plusProjection (n := n) (F := F)) :=
  (continuous_projection.comp continuous_subtype_val).subtype_mk _

/-- The projection as a continuous homomorphism. -/
def projectionContinuous : ContinuousMonoidHom (mirabolic n F) (Langlands.GeneralLinear n F) where
  toMonoidHom := projection
  continuous_toFun := continuous_projection

/-- The plus projection as a continuous homomorphism. -/
def plusProjectionContinuous : ContinuousMonoidHom (plusSubgroup n F) (mirabolic n F) where
  toMonoidHom := plusProjection
  continuous_toFun := continuous_plusProjection

/-- Closedness follows from the published closedness of the smaller mirabolic group. -/
theorem plusSubgroup_isClosed [T2Space F] :
    IsClosed (plusSubgroup n F : Set (mirabolic (n + 1) F)) :=
  (isClosed (n := n) (F := F)).preimage continuous_projection

variable [IsTopologicalRing F]

/-- The radical-then-Levi coordinates are a homeomorphism (not a group isomorphism). -/
def radicalLeviHomeomorph : mirabolic n F ≃ₜ (Fin n → F) × Langlands.GeneralLinear n F where
  toEquiv := radicalLeviEquiv
  continuous_toFun := continuous_lastColumn.prodMk continuous_projection
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_radicalElement).comp continuous_fst).mul
      (continuous_levi.comp continuous_snd)

@[simp] theorem radicalLeviHomeomorph_apply (g : mirabolic n F) :
    radicalLeviHomeomorph g = (lastColumn g, projection g) := rfl

@[simp] theorem radicalLeviHomeomorph_symm_apply
    (p : (Fin n → F) × Langlands.GeneralLinear n F) :
    radicalLeviHomeomorph.symm p = (radicalElement p.1).val * levi p.2 := rfl

/-- Radical-then-successor coordinates on the plus subgroup are a homeomorphism. -/
def radicalSuccessorHomeomorph :
    plusSubgroup n F ≃ₜ (Fin (n + 1) → F) × mirabolic n F where
  toEquiv := radicalSuccessorEquiv
  continuous_toFun :=
    (continuous_lastColumn.comp continuous_subtype_val).prodMk continuous_plusProjection
  continuous_invFun :=
    (((continuous_subtype_val.comp continuous_radicalElement).comp continuous_fst).mul
      (continuous_successor.comp continuous_snd)).subtype_mk _

@[simp] theorem radicalSuccessorHomeomorph_apply (g : plusSubgroup n F) :
    radicalSuccessorHomeomorph g = (lastColumn g.val, plusProjection g) := rfl

@[simp] theorem radicalSuccessorHomeomorph_symm_apply_val
    (p : (Fin (n + 1) → F) × mirabolic n F) :
    (radicalSuccessorHomeomorph.symm p).val = (radicalElement p.1).val * successor p.2 := rfl

end Topology

end Langlands.GeneralLinear.Mirabolic
