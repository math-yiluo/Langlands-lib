import Langlands.Representation.AffineGeneric.Radical

/-!
# The pro-unipotent radical `I⁺` of the standard Iwahori subgroup

`I⁺ = 1 + 𝔓` is the subgroup of `GL_{m+1}(F)` of elements `g` with `g - 1` and `g⁻¹ - 1` in the
radical `𝔓` of the standard Iwahori order. The units of the order normalize `I⁺`. Over a
nonarchimedean local field, `I⁺` is open and compact. For a uniformizer `ϖ`, the map
`g ↦ (groupCoord ϖ g i)_i` is a homomorphism from `I⁺` to the additive group of `k^{m+1}`.
-/

noncomputable section

open Filter Topology

namespace Langlands.AffineGeneric

open ValuativeRel Matrix LevelZero

universe u

variable {F : Type u} [Field F] [ValuativeRel F]

variable (m : ℕ)

/-- The pro-unipotent radical `I⁺ = 1 + 𝔓` of the standard Iwahori subgroup. -/
def iwahoriRadical : Subgroup (GeneralLinear (m + 1) F) where
  carrier := {g | IsIwahoriRadical ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1) ∧
    IsIwahoriRadical (((g⁻¹ : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1)}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, inv_one, Matrix.GeneralLinearGroup.coe_one, sub_self]
    exact ⟨isIwahoriRadical_zero, isIwahoriRadical_zero⟩
  mul_mem' := by
    intro g h hg hh
    have key : ∀ A B : Matrix (Fin (m + 1)) (Fin (m + 1)) F,
        IsIwahoriRadical (A - 1) → IsIwahoriRadical (B - 1) → IsIwahoriRadical (A * B - 1) := by
      intro A B hA hB
      have he : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
      rw [he]
      exact (hA.add hB).add (hA.isIwahoriOrder.mul_radical hB)
    refine ⟨?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.coe_mul]
      exact key _ _ hg.1 hh.1
    · rw [_root_.mul_inv_rev, Matrix.GeneralLinearGroup.coe_mul]
      exact key _ _ hh.2 hg.2
  inv_mem' := by
    intro g hg
    refine ⟨hg.2, ?_⟩
    rw [inv_inv]
    exact hg.1

variable {m}

theorem mem_iwahoriRadical_iff {g : GeneralLinear (m + 1) F} :
    g ∈ iwahoriRadical m ↔ IsIwahoriRadical ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1) ∧
      IsIwahoriRadical
        (((g⁻¹ : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1) :=
  Iff.rfl

/-- Conjugation by a unit of the Iwahori order preserves `I⁺`. -/
theorem conj_mem_iwahoriRadical {ι g : GeneralLinear (m + 1) F}
    (hι : IsIwahoriOrder (ι : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (hι' : IsIwahoriOrder ((ι⁻¹ : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (hg : g ∈ iwahoriRadical m) : ι * g * ι⁻¹ ∈ iwahoriRadical m := by
  have key : ∀ A : Matrix (Fin (m + 1)) (Fin (m + 1)) F, IsIwahoriRadical (A - 1) →
      IsIwahoriRadical ((ι : Matrix _ _ F) * A * ((ι⁻¹ : GeneralLinear (m + 1) F) : Matrix _ _ F)
        - 1) := by
    intro A hA
    have hιι : (ι : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        ((ι⁻¹ : GeneralLinear (m + 1) F) : Matrix _ _ F) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
    have he : (ι : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * A *
        ((ι⁻¹ : GeneralLinear (m + 1) F) : Matrix _ _ F) - 1 =
        (ι : Matrix _ _ F) * (A - 1) * ((ι⁻¹ : GeneralLinear (m + 1) F) : Matrix _ _ F) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hιι]
    rw [he]
    exact (hι.mul_radical hA).mul_order hι'
  refine ⟨?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
    exact key _ hg.1
  · rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← mul_assoc, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_mul]
    exact key _ hg.2

omit [ValuativeRel F] in
theorem coe_inv_mul_coe {g : GeneralLinear (m + 1) F} :
    ((g⁻¹ : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
  rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]

theorem iwahoriRadical_le_maximalCompact [TopologicalSpace F] :
    iwahoriRadical (F := F) m ≤ maximalCompact (F := F) m := by
  intro g hg
  have hint : ∀ A : Matrix (Fin (m + 1)) (Fin (m + 1)) F, IsIwahoriRadical (A - 1) →
      ∀ i j, valuation F (A i j) ≤ 1 := by
    intro A hA i j
    have he : A = (A - 1) + 1 := by abel
    rw [he, Matrix.add_apply]
    exact (valuation F).map_add_le (hA i j).1 ((isIwahoriOrder_one i j).1)
  rw [Conductor.mem_integralSubgroup]
  exact ⟨fun i j => (Valuation.mem_integer_iff _ _).mpr (hint _ hg.1 i j),
    fun i j => (Valuation.mem_integer_iff _ _).mpr (hint _ hg.2 i j)⟩

section Topology

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem nearIdentity_subset_iwahoriRadical :
    nearIdentity (F := F) m ⊆ (iwahoriRadical (F := F) m : Set (GeneralLinear (m + 1) F)) := by
  intro g hg
  refine ⟨fun i j => ⟨(hg i j).1.le, fun _ => (hg i j).1⟩,
    fun i j => ⟨(hg i j).2.le, fun _ => (hg i j).2⟩⟩

theorem isOpen_iwahoriRadical :
    IsOpen (iwahoriRadical (F := F) m : Set (GeneralLinear (m + 1) F)) :=
  Subgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset (nearIdentity_mem_nhds (F := F) m) nearIdentity_subset_iwahoriRadical)

theorem isCompact_iwahoriRadical :
    IsCompact (iwahoriRadical (F := F) m : Set (GeneralLinear (m + 1) F)) :=
  (isCompact_maximalCompact (F := F) (m := m)).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ isOpen_iwahoriRadical) iwahoriRadical_le_maximalCompact

end Topology

/-! ### Group coordinates -/

variable (ϖ : Fˣ)

/-- The cyclic coordinate `a_i(g - 1) = coord ϖ (g - 1) i`, defined for any `ϖ : Fˣ`.
For a uniformizer `ϖ` and `g ∈ I⁺` these are the affine simple coordinates when `m ≥ 1`.
When `m = 0`, the corresponding map on `I⁺ = 1 + 𝔭` is `g ↦ res(ϖ⁻¹ (g - 1))`,
the principal-unit homomorphism to `k` with kernel `1 + 𝔭²`. -/
def groupCoord (g : GeneralLinear (m + 1) F) (i : Fin (m + 1)) : Residue F :=
  coord ϖ ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1) i

variable {ϖ}
variable (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement (valuation F) ϖ)
include hϖ

theorem groupCoord_mul {g h : GeneralLinear (m + 1) F} (hg : g ∈ iwahoriRadical m)
    (hh : h ∈ iwahoriRadical m) (i : Fin (m + 1)) :
    groupCoord ϖ (g * h) i = groupCoord ϖ g i + groupCoord ϖ h i := by
  unfold groupCoord
  have he : ((g * h : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1 =
      ((g : Matrix _ _ F) - 1) + ((h : Matrix _ _ F) - 1) +
        ((g : Matrix _ _ F) - 1) * ((h : Matrix _ _ F) - 1) := by
    rw [Matrix.GeneralLinearGroup.coe_mul]
    noncomm_ring
  rw [he, coord_add hϖ (hg.1.add hh.1) (hg.1.isIwahoriOrder.mul_radical hh.1),
    coord_add hϖ hg.1 hh.1, coord_mul_radical hϖ hg.1 hh.1, add_zero]

omit hϖ in
theorem groupCoord_one (i : Fin (m + 1)) : groupCoord ϖ (1 : GeneralLinear (m + 1) F) i = 0 := by
  unfold groupCoord coord
  simp

theorem groupCoord_inv {g : GeneralLinear (m + 1) F} (hg : g ∈ iwahoriRadical m)
    (i : Fin (m + 1)) : groupCoord ϖ g⁻¹ i = -groupCoord ϖ g i := by
  have h := groupCoord_mul hϖ hg ((iwahoriRadical m).inv_mem hg) i
  rw [mul_inv_cancel, groupCoord_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- For a uniformizer `ϖ`, conjugation by a unit of the Iwahori order scales the coordinates
on `I⁺` by diagonal residues. -/
theorem groupCoord_conj {ι g : GeneralLinear (m + 1) F}
    (hι : IsIwahoriOrder (ι : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (hι' : IsIwahoriOrder ((ι⁻¹ : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (hg : g ∈ iwahoriRadical m) (i : Fin (m + 1)) :
    groupCoord ϖ (ι * g * ι⁻¹) i = resOf ((ι : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i) *
      groupCoord ϖ g i * resOf (((ι⁻¹ : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1))
        (Fin (m + 1)) F) (finRotate (m + 1) i) (finRotate (m + 1) i)) := by
  unfold groupCoord
  have hιι : (ι : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      ((ι⁻¹ : GeneralLinear (m + 1) F) : Matrix _ _ F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have he : ((ι * g * ι⁻¹ : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1 =
      (ι : Matrix _ _ F) * ((g : Matrix _ _ F) - 1) *
        ((ι⁻¹ : GeneralLinear (m + 1) F) : Matrix _ _ F) := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, hιι]
  rw [he, coord_mul_order hϖ (hι.mul_radical hg.1) hι', coord_order_mul hϖ hι hg.1]

end Langlands.AffineGeneric
