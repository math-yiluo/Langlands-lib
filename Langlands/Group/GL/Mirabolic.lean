import Langlands.Group.GL.UpperUnipotent

/-! # The actual mirabolic matrix subgroup -/

namespace Langlands.GeneralLinear

universe u

variable {F : Type u} [CommRing F] {n : ℕ}

private theorem lastRow_mul (g h : Langlands.GeneralLinear (n + 1) F)
    (hg : ∀ j, g.val (Fin.last n) j = if j = Fin.last n then 1 else 0)
    (j : Fin (n + 1)) :
    (g * h).val (Fin.last n) j = h.val (Fin.last n) j := by
  change (g.val * h.val) (Fin.last n) j = _
  simp [Matrix.mul_apply, hg]

/-- Invertible matrices whose last row is `(0, …, 0, 1)`. -/
def mirabolic (n : ℕ) (F : Type u) [CommRing F] :
    Subgroup (Langlands.GeneralLinear (n + 1) F) where
  carrier := {g | ∀ j, g.val (Fin.last n) j = if j = Fin.last n then 1 else 0}
  one_mem' := by intro j; simp [Matrix.one_apply, eq_comm]
  mul_mem' := by
    intro g h hg hh j
    rw [lastRow_mul g h hg j, hh j]
  inv_mem' := by
    intro g hg j
    have h := lastRow_mul g g⁻¹ hg j
    rw [mul_inv_cancel] at h
    simpa [Matrix.one_apply, eq_comm] using h.symm

@[simp] theorem mem_mirabolic (g : Langlands.GeneralLinear (n + 1) F) :
    g ∈ mirabolic n F ↔
      ∀ j, g.val (Fin.last n) j = if j = Fin.last n then 1 else 0 := Iff.rfl

/-- Every upper unipotent matrix lies in the mirabolic subgroup. -/
theorem upperUnipotent_le_mirabolic : upperUnipotent (n + 1) F ≤ mirabolic n F := by
  intro g hg j
  by_cases hj : j = Fin.last n
  · subst j
    simpa using hg.2 (Fin.last n)
  · have hjlt : j < Fin.last n := lt_of_le_of_ne (Fin.le_last j) hj
    rw [ite_eq_right (by simp [hj])]
    exact hg.1 hjlt

namespace Mirabolic

/-- The actual upper-unipotent subgroup, now inside the mirabolic group. -/
def upperUnipotent (n : ℕ) (F : Type u) [CommRing F] :
    Subgroup (mirabolic n F) :=
  (GeneralLinear.upperUnipotent (n + 1) F).comap (mirabolic n F).subtype

@[simp] theorem mem_upperUnipotent (g : mirabolic n F) :
    g ∈ upperUnipotent n F ↔ g.val ∈ GeneralLinear.upperUnipotent (n + 1) F := Iff.rfl

/-- Forgetting the redundant mirabolic membership identifies the two unipotent groups. -/
def upperUnipotentEquiv :
    upperUnipotent n F ≃* GeneralLinear.upperUnipotent (n + 1) F where
  toFun g := ⟨g.val.val, g.property⟩
  invFun g := ⟨⟨g.val, upperUnipotent_le_mirabolic g.property⟩, g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem upperUnipotentEquiv_val (g : upperUnipotent n F) :
    (upperUnipotentEquiv g).val = g.val.val := rfl

@[simp] theorem upperUnipotentEquiv_symm_val
    (g : GeneralLinear.upperUnipotent (n + 1) F) :
    (upperUnipotentEquiv.symm g).val.val = g.val := rfl

/-- The rank-one mirabolic group has only its identity. -/
theorem rankOne_eq_one (g : mirabolic 0 F) : g = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hi : i = Fin.last 0 := Fin.ext (by omega)
  have hj : j = Fin.last 0 := Fin.ext (by omega)
  subst i
  subst j
  simpa using g.property (Fin.last 0)

instance rankOneSubsingleton : Subsingleton (mirabolic 0 F) :=
  ⟨fun g h => (rankOne_eq_one g).trans (rankOne_eq_one h).symm⟩

section Topology

variable [TopologicalSpace F]

/-- Matrix entries use the inherited subgroup topology. -/
def entry (i j : Fin (n + 1)) : C(mirabolic n F, F) where
  toFun g := g.val i j
  continuous_toFun := (GeneralLinear.entry i j).continuous.comp continuous_subtype_val

/-- The unipotent identification preserves the inherited topologies. -/
def upperUnipotentContinuousEquiv :
    upperUnipotent n F ≃ₜ* GeneralLinear.upperUnipotent (n + 1) F where
  toMulEquiv := upperUnipotentEquiv
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

variable [T2Space F]

/-- Entrywise equations make the mirabolic group closed. -/
theorem isClosed : IsClosed (mirabolic n F : Set (Langlands.GeneralLinear (n + 1) F)) := by
  change IsClosed {g : Langlands.GeneralLinear (n + 1) F |
    ∀ j, g.val (Fin.last n) j = if j = Fin.last n then 1 else 0}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun j =>
    isClosed_eq (GeneralLinear.entry (Fin.last n) j).continuous continuous_const

/-- The unipotent subgroup is closed in the mirabolic group. -/
theorem upperUnipotent_isClosed : IsClosed (upperUnipotent n F : Set (mirabolic n F)) :=
  GeneralLinear.UpperUnipotent.isClosed.preimage continuous_subtype_val

/-- Closedness supplies local compactness whenever the ambient matrix group is locally compact. -/
theorem locallyCompactSpace [LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F)] :
    LocallyCompactSpace (mirabolic n F) :=
  (isClosed (F := F) (n := n)).locallyCompactSpace

end Topology
end Mirabolic
end Langlands.GeneralLinear
