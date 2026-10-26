import Langlands.Group.GL.Mirabolic
import Langlands.Group.GL.RankMaps
import Mathlib.Algebra.BigOperators.Fin

/-! # Radical coordinates and standard Levi maps for the actual mirabolic group -/

namespace Langlands.GeneralLinear.Mirabolic

universe u

variable {F : Type u} [CommRing F] {n : ℕ}

private theorem fixedColumn_mul (g h : Langlands.GeneralLinear (n + 1) F)
    (hh : ∀ i (j : Fin n), h.val i j.castSucc = if i = j.castSucc then 1 else 0)
    (i : Fin (n + 1)) (j : Fin n) :
    (g * h).val i j.castSucc = g.val i j.castSucc := by
  change (g.val * h.val) i j.castSucc = _
  simp [Matrix.mul_apply, hh]

/-- The actual radical: the first `n` columns are the corresponding identity columns. -/
def radical (n : ℕ) (F : Type u) [CommRing F] : Subgroup (mirabolic n F) where
  carrier := {g | ∀ i (j : Fin n), g.val.val i j.castSucc = if i = j.castSucc then 1 else 0}
  one_mem' := by intro i j; simp [Matrix.one_apply]
  mul_mem' := by
    intro g h hg hh i j
    change (g.val * h.val).val i j.castSucc = _
    rw [fixedColumn_mul g.val h.val hh, hg]
  inv_mem' := by
    intro g hg i j
    have h := fixedColumn_mul g.val⁻¹ g.val hg i j
    rw [inv_mul_cancel] at h
    simpa [Matrix.one_apply] using h.symm

@[simp] theorem mem_radical (g : mirabolic n F) :
    g ∈ radical n F ↔
      ∀ i (j : Fin n), g.val.val i j.castSucc = if i = j.castSucc then 1 else 0 := Iff.rfl

private def columnUnit (v : Fin n → F) :
    Matrix.GeneralLinearGroup (Fin n ⊕ Fin 1) F where
  val := Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (Matrix.of fun i (_ : Fin 1) => v i) 0 (1 : Matrix (Fin 1) (Fin 1) F)
  inv := Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (Matrix.of fun i (_ : Fin 1) => -v i) 0 (1 : Matrix (Fin 1) (Fin 1) F)
  val_inv := by
    simp [Matrix.fromBlocks_multiply, Pi.add_def]
    exact Matrix.fromBlocks_one
  inv_val := by
    simp [Matrix.fromBlocks_multiply, Pi.add_def]
    exact Matrix.fromBlocks_one

private def columnGL (v : Fin n → F) : Langlands.GeneralLinear (n + 1) F :=
  reindex finSumFinEquiv (columnUnit v)

private theorem columnGL_first (v : Fin n → F) (i : Fin (n + 1)) (j : Fin n) :
    (columnGL v).val i j.castSucc = if i = j.castSucc then 1 else 0 := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · change Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (Matrix.of fun i (_ : Fin 1) => v i) 0 (1 : Matrix (Fin 1) (Fin 1) F)
      (finSumFinEquiv.symm (Fin.natAdd n (0 : Fin 1)))
      (finSumFinEquiv.symm (j.castAdd 1)) = _
    simp [(Fin.castSucc_ne_last _).symm]
  · change Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (Matrix.of fun i (_ : Fin 1) => v i) 0 (1 : Matrix (Fin 1) (Fin 1) F)
      (finSumFinEquiv.symm (i.castAdd 1)) (finSumFinEquiv.symm (j.castAdd 1)) = _
    simp [Matrix.one_apply]

private theorem columnGL_last (v : Fin n → F) (i : Fin n) :
    (columnGL v).val i.castSucc (Fin.last n) = v i := by
  change Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (Matrix.of fun i (_ : Fin 1) => v i) 0 (1 : Matrix (Fin 1) (Fin 1) F)
    (finSumFinEquiv.symm (i.castAdd 1))
    (finSumFinEquiv.symm (Fin.natAdd n (0 : Fin 1))) = _
  simp

private theorem columnGL_bottom (v : Fin n → F) (j : Fin (n + 1)) :
    (columnGL v).val (Fin.last n) j = if j = Fin.last n then 1 else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · change Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (Matrix.of fun i (_ : Fin 1) => v i) 0 (1 : Matrix (Fin 1) (Fin 1) F)
      (finSumFinEquiv.symm (Fin.natAdd n (0 : Fin 1)))
      (finSumFinEquiv.symm (Fin.natAdd n (0 : Fin 1))) = _
    simp
  · rw [columnGL_first]
    simp [(Fin.castSucc_ne_last _).symm]

/-- The actual matrix `u(v) = [[I,v],[0,1]]` in the radical. -/
def radicalElement (v : Fin n → F) : radical n F :=
  ⟨⟨columnGL v, columnGL_bottom v⟩, columnGL_first v⟩

@[simp] theorem radicalElement_first (v : Fin n → F)
    (i : Fin (n + 1)) (j : Fin n) :
    (radicalElement v).val.val.val i j.castSucc = if i = j.castSucc then 1 else 0 :=
  columnGL_first v i j

@[simp] theorem radicalElement_last (v : Fin n → F) (i : Fin n) :
    (radicalElement v).val.val.val i.castSucc (Fin.last n) = v i :=
  columnGL_last v i

@[simp] theorem radicalElement_bottom (v : Fin n → F) (j : Fin (n + 1)) :
    (radicalElement v).val.val.val (Fin.last n) j = if j = Fin.last n then 1 else 0 :=
  columnGL_bottom v j

/-- Extract the last column above the final diagonal entry. -/
def radicalCoordinates (g : radical n F) : Fin n → F :=
  fun i => g.val.val.val i.castSucc (Fin.last n)

@[simp] theorem radicalCoordinates_element (v : Fin n → F) :
    radicalCoordinates (radicalElement v) = v := by
  funext i
  exact radicalElement_last v i

@[simp] theorem radicalElement_coordinates (g : radical n F) :
    radicalElement (radicalCoordinates g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · exact (radicalElement_bottom _ _).trans (g.val.property _).symm
    · exact radicalElement_last _ i
  · exact (radicalElement_first _ i j).trans (g.property i j).symm

@[simp] theorem radicalElement_zero : radicalElement (0 : Fin n → F) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change (reindex finSumFinEquiv (columnUnit (0 : Fin n → F))).val = 1
  have h : columnUnit (0 : Fin n → F) = 1 := by
    apply Units.ext
    exact Matrix.fromBlocks_one
  rw [h, map_one]
  rfl

/-- Matrix multiplication is addition of the radical columns. -/
theorem radicalElement_add (v w : Fin n → F) :
    radicalElement (v + w) = radicalElement v * radicalElement w := by
  apply Subtype.ext
  apply Subtype.ext
  change columnGL (v + w) = columnGL v * columnGL w
  rw [columnGL, columnGL, columnGL, ← map_mul]
  apply congrArg
  apply Units.ext
  simp [columnUnit, Matrix.fromBlocks_multiply]
  ext i j
  simp [add_comm]

/-- Multiplication-preserving coordinates on the actual matrix radical. -/
def radicalEquiv : radical n F ≃* Multiplicative (Fin n → F) :=
  (show Multiplicative (Fin n → F) ≃* radical n F from
    { toFun := fun v => radicalElement v.toAdd
      invFun := fun g => Multiplicative.ofAdd (radicalCoordinates g)
      left_inv := fun v => radicalCoordinates_element v.toAdd
      right_inv := radicalElement_coordinates
      map_mul' := fun v w => radicalElement_add v.toAdd w.toAdd }).symm

@[simp] theorem radicalEquiv_apply (g : radical n F) (i : Fin n) :
    (radicalEquiv g).toAdd i = g.val.val.val i.castSucc (Fin.last n) := rfl

@[simp] theorem radicalEquiv_symm_apply (v : Multiplicative (Fin n → F)) :
    radicalEquiv.symm v = radicalElement v.toAdd := rfl

@[simp] theorem radicalEquiv_symm_first (v : Multiplicative (Fin n → F))
    (i : Fin (n + 1)) (j : Fin n) :
    (radicalEquiv.symm v).val.val.val i j.castSucc = if i = j.castSucc then 1 else 0 :=
  radicalElement_first _ i j

@[simp] theorem radicalEquiv_symm_last (v : Multiplicative (Fin n → F)) (i : Fin n) :
    (radicalEquiv.symm v).val.val.val i.castSucc (Fin.last n) = v.toAdd i :=
  radicalElement_last _ i

/-- Radical matrices are actual upper-unipotent matrices. -/
theorem radical_le_upperUnipotent : radical n F ≤ upperUnipotent n F := by
  intro g hg
  constructor
  · intro i j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro h
      exact (not_lt_of_ge (Fin.le_last i) h).elim
    · intro h
      change g.val.val i j.castSucc = 0
      rw [hg i j]
      have hne : i ≠ j.castSucc := ne_of_gt h
      simp [hne]
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using g.property (Fin.last n)
    · change g.val.val i.castSucc i.castSucc = 1
      rw [hg i.castSucc i]
      simp

/-- The literal matrix inclusion into the ambient upper-unipotent group. -/
def radicalToUpperUnipotent : radical n F →* GeneralLinear.upperUnipotent (n + 1) F :=
  upperUnipotentEquiv.toMonoidHom.comp (Subgroup.inclusion radical_le_upperUnipotent)

@[simp] theorem radicalToUpperUnipotent_val (g : radical n F) :
    (radicalToUpperUnipotent g).val = g.val.val := rfl

/-- The standard Levi inclusion `g ↦ diag(g,1)` into the actual mirabolic group. -/
def levi : Langlands.GeneralLinear n F →* mirabolic n F :=
  (rankInclusion 1).codRestrict _ fun g => by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [ite_true]
      change (blockSum (g, (1 : Langlands.GeneralLinear 1 F))).val
          (Fin.natAdd n (0 : Fin 1)) (Fin.natAdd n (0 : Fin 1)) = 1
      rw [blockSum_apply_right]
      simp
    · change (blockSum (g, (1 : Langlands.GeneralLinear 1 F))).val
          (Fin.natAdd n (0 : Fin 1)) (j.castAdd 1) = _
      rw [blockSum_apply_right_left]
      simp

@[simp] theorem levi_first (g : Langlands.GeneralLinear n F) (i j : Fin n) :
    (levi g).val.val i.castSucc j.castSucc = g.val i j :=
  blockSum_apply_left g 1 i j

@[simp] theorem levi_last (g : Langlands.GeneralLinear n F) (i : Fin n) :
    (levi g).val.val i.castSucc (Fin.last n) = 0 :=
  blockSum_apply_left_right g 1 i (0 : Fin 1)

@[simp] theorem levi_bottom (g : Langlands.GeneralLinear n F) (j : Fin (n + 1)) :
    (levi g).val.val (Fin.last n) j = if j = Fin.last n then 1 else 0 :=
  (levi g).property j

theorem levi_injective : Function.Injective (levi (n := n) (F := F)) := by
  intro g h he
  exact rankInclusion_injective 1 (congrArg Subtype.val he)

/-- The induced standard embedding `P_(n+1) → P_(n+2)`. -/
def successor : mirabolic n F →* mirabolic (n + 1) F :=
  levi.comp (mirabolic n F).subtype

theorem successor_injective : Function.Injective (successor (n := n) (F := F)) :=
  levi_injective.comp Subtype.val_injective

/-- The concrete block identity underlying the conjugation action. -/
theorem levi_mul_radicalElement (g : Langlands.GeneralLinear n F) (v : Fin n → F) :
    levi g * (radicalElement v).val =
      (radicalElement (g.val.mulVec v)).val * levi g := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change ((levi g).val.val * (radicalElement v).val.val.val) i j =
    ((radicalElement (g.val.mulVec v)).val.val.val * (levi g).val.val) i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, levi_first, levi_last,
      levi_bottom, radicalElement_first, radicalElement_last, radicalElement_bottom,
      Matrix.mulVec, dotProduct]

/-- `mulVec` means `(g*v) i = ∑ j, g i j * v j`, with no transpose. -/
theorem levi_conjugate_radicalElement (g : Langlands.GeneralLinear n F) (v : Fin n → F) :
    levi g * (radicalElement v).val * (levi g)⁻¹ =
      (radicalElement (g.val.mulVec v)).val := by
  rw [levi_mul_radicalElement, mul_inv_cancel_right]

/-- The standard Levi is an actual subgroup of the actual mirabolic group. -/
def leviSubgroup (n : ℕ) (F : Type u) [CommRing F] : Subgroup (mirabolic n F) :=
  (levi (n := n) (F := F)).range

/-- The embedding identifies `GL_n` with its actual range. -/
noncomputable def leviEquiv : Langlands.GeneralLinear n F ≃* leviSubgroup n F :=
  MonoidHom.ofInjective levi_injective

@[simp] theorem leviEquiv_val (g : Langlands.GeneralLinear n F) :
    (leviEquiv g).val = levi g := rfl

@[simp] theorem leviEquiv_symm_entry (g : leviSubgroup n F) (i j : Fin n) :
    (leviEquiv.symm g).val i j = g.val.val.val i.castSucc j.castSucc := by
  obtain ⟨g, rfl⟩ := leviEquiv.surjective g
  simp

/-- The successor mirabolic is the actual range of `diag(-,1)`. -/
def successorSubgroup (n : ℕ) (F : Type u) [CommRing F] :
    Subgroup (mirabolic (n + 1) F) :=
  (successor (n := n) (F := F)).range

noncomputable def successorEquiv : mirabolic n F ≃* successorSubgroup n F :=
  MonoidHom.ofInjective successor_injective

@[simp] theorem successorEquiv_val (g : mirabolic n F) :
    (successorEquiv g).val = successor g := rfl

@[simp] theorem successor_first (g : mirabolic n F) (i j : Fin (n + 1)) :
    (successor g).val.val i.castSucc j.castSucc = g.val.val i j :=
  levi_first g.val i j

@[simp] theorem successor_last (g : mirabolic n F) (i : Fin (n + 1)) :
    (successor g).val.val i.castSucc (Fin.last (n + 1)) = 0 :=
  levi_last g.val i

@[simp] theorem successorEquiv_symm_entry (g : successorSubgroup n F)
    (i j : Fin (n + 1)) :
    (successorEquiv.symm g).val.val i j =
      g.val.val.val i.castSucc j.castSucc := by
  obtain ⟨g, rfl⟩ := successorEquiv.surjective g
  simp

private theorem levi_conjugate_mem (g : Langlands.GeneralLinear n F)
    (u : mirabolic n F) (hu : u ∈ radical n F) :
    levi g * u * (levi g)⁻¹ ∈ radical n F := by
  let v := radicalCoordinates (⟨u, hu⟩ : radical n F)
  have he : (radicalElement v).val = u := congrArg Subtype.val
    (radicalElement_coordinates (⟨u, hu⟩ : radical n F))
  rw [← he, levi_conjugate_radicalElement]
  exact (radicalElement _).property

/-- Normalization is proved for the actual embedded Levi subgroup. -/
theorem leviSubgroup_le_normalizer :
    leviSubgroup n F ≤ Subgroup.normalizer (radical n F) := by
  rintro _ ⟨g, rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro u
  constructor
  · exact levi_conjugate_mem g u
  · intro hu
    have h := levi_conjugate_mem g⁻¹ _ hu
    simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_assoc,
      mul_inv_cancel, inv_mul_cancel, mul_one] using h

/-- Normalization for the actual embedded smaller mirabolic subgroup. -/
theorem successorSubgroup_le_normalizer :
    successorSubgroup n F ≤ Subgroup.normalizer (radical (n + 1) F) := by
  rintro _ ⟨g, rfl⟩
  exact leviSubgroup_le_normalizer ⟨g.val, rfl⟩

/-- The rank-one radical has only its identity, including over the zero ring. -/
instance radical_rankOneSubsingleton : Subsingleton (radical 0 F) := inferInstance

section Topology

variable [TopologicalSpace F]

/-- The extracted last column is continuous for the inherited matrix topology. -/
theorem continuous_radicalCoordinates :
    Continuous (radicalCoordinates (n := n) (F := F)) := by
  apply continuous_pi
  intro i
  exact (entry i.castSucc (Fin.last n)).continuous.comp continuous_subtype_val

theorem continuous_radicalToUpperUnipotent :
    Continuous (radicalToUpperUnipotent (n := n) (F := F)) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The standard Levi map is continuous for any coefficient topology. -/
theorem continuous_levi : Continuous (levi (n := n) (F := F)) :=
  (rankInclusionContinuous 1).continuous.subtype_mk _

theorem continuous_successor : Continuous (successor (n := n) (F := F)) :=
  continuous_levi.comp continuous_subtype_val

private theorem continuous_leviEquiv_symm :
    Continuous ((leviEquiv (n := n) (F := F)).symm) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    intro i j
    change Continuous (fun g : leviSubgroup n F => (leviEquiv.symm g).val i j)
    simp_rw [leviEquiv_symm_entry]
    exact (entry (F := F) i.castSucc j.castSucc).continuous.comp continuous_subtype_val
  · apply continuous_matrix
    intro i j
    have hc : Continuous (fun g : leviSubgroup n F =>
        (g.val.val⁻¹).val i.castSucc j.castSucc) :=
      ((continuous_apply j.castSucc).comp ((continuous_apply i.castSucc).comp
        (show Continuous (fun g : Langlands.GeneralLinear (n + 1) F => (g⁻¹).val) from
          Units.continuous_coe_inv))).comp
            (continuous_subtype_val.comp continuous_subtype_val)
    convert hc using 1
    funext g
    rw [← map_inv, leviEquiv_symm_entry]
    rfl

/-- A genuine topological group equivalence with the embedded Levi subgroup. -/
noncomputable def leviContinuousEquiv :
    Langlands.GeneralLinear n F ≃ₜ* leviSubgroup n F where
  toMulEquiv := leviEquiv
  continuous_toFun := continuous_levi.subtype_mk _
  continuous_invFun := continuous_leviEquiv_symm

private theorem continuous_successorEquiv_symm :
    Continuous ((successorEquiv (n := n) (F := F)).symm) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    intro i j
    change Continuous (fun g : successorSubgroup n F => (successorEquiv.symm g).val.val i j)
    simp_rw [successorEquiv_symm_entry]
    exact (entry (F := F) i.castSucc j.castSucc).continuous.comp continuous_subtype_val
  · apply continuous_matrix
    intro i j
    have hc : Continuous (fun g : successorSubgroup n F =>
        (g.val.val⁻¹).val i.castSucc j.castSucc) :=
      ((continuous_apply j.castSucc).comp ((continuous_apply i.castSucc).comp
        (show Continuous (fun g : Langlands.GeneralLinear (n + 1 + 1) F => (g⁻¹).val) from
          Units.continuous_coe_inv))).comp
            (continuous_subtype_val.comp continuous_subtype_val)
    convert hc using 1
    funext g
    change ((successorEquiv.symm g)⁻¹).val.val i j = _
    rw [← map_inv, successorEquiv_symm_entry]
    rfl

/-- The smaller mirabolic group is topologically its actual successor range. -/
noncomputable def successorContinuousEquiv :
    mirabolic n F ≃ₜ* successorSubgroup n F where
  toMulEquiv := successorEquiv
  continuous_toFun := continuous_successor.subtype_mk _
  continuous_invFun := continuous_successorEquiv_symm

variable [IsTopologicalRing F]

private theorem continuous_columnUnit :
    Continuous (columnUnit (n := n) (F := F)) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    rintro (i | i) (j | j)
    · exact continuous_const
    · exact continuous_apply i
    · exact continuous_const
    · exact continuous_const
  · apply continuous_matrix
    rintro (i | i) (j | j)
    · exact continuous_const
    · exact (continuous_apply i).neg
    · exact continuous_const
    · exact continuous_const

theorem continuous_radicalElement :
    Continuous (radicalElement (n := n) (F := F)) :=
  (((reindexContinuous finSumFinEquiv).continuous.comp continuous_columnUnit).subtype_mk _).subtype_mk _

/-- Radical coordinates preserve both the group law and the inherited topologies. -/
def radicalContinuousEquiv : radical n F ≃ₜ* Multiplicative (Fin n → F) where
  toMulEquiv := radicalEquiv
  continuous_toFun := continuous_ofAdd.comp continuous_radicalCoordinates
  continuous_invFun := continuous_radicalElement.comp continuous_toAdd

omit [IsTopologicalRing F] in
/-- The defining entry equations also show the radical is closed. -/
theorem radical_isClosed [T2Space F] :
    IsClosed (radical n F : Set (mirabolic n F)) := by
  change IsClosed {g : mirabolic n F | ∀ i (j : Fin n),
    g.val.val i j.castSucc = if i = j.castSucc then 1 else 0}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (entry i j.castSucc).continuous continuous_const

end Topology

end Langlands.GeneralLinear.Mirabolic
