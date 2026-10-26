import Langlands.Group.GL.Maps
import Langlands.Group.GL.TriangularParabolic
import Langlands.Group.GL.UpperUnipotent
import Langlands.Representation.Whittaker.Iwasawa
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.Algebra.Group.Action.Opposite

/-!
# Actual upper Bruhat cells and elementary coordinate maps
-/

namespace Langlands.GeneralLinear

universe u

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The full upper unipotent subgroup is contained in the upper triangular subgroup. -/
theorem upperUnipotent_le_upperTriangular :
    upperUnipotent n R ≤ upperTriangularSubgroup n R :=
  fun _ hg => hg.1

/-- The inclusion retaining the actual underlying matrix. -/
def upperUnipotentInUpperTriangular :
    upperUnipotent n R →* upperTriangularSubgroup n R :=
  Subgroup.inclusion (upperUnipotent_le_upperTriangular n R)

@[simp]
theorem upperUnipotentInUpperTriangular_val (g : upperUnipotent n R) :
    (upperUnipotentInUpperTriangular n R g).val = g.val :=
  rfl

/-- An explicit entrywise criterion for the existing upper unipotent subgroup. -/
theorem mem_upperUnipotent_iff (g : Langlands.GeneralLinear n R) :
    g ∈ upperUnipotent n R ↔
      (∀ i j : Fin n, j < i → g i j = 0) ∧ ∀ i : Fin n, g i i = 1 :=
  Iff.rfl

/-- Actual lower unipotent matrices, constructed by long-Weyl conjugation. -/
def lowerUnipotent : Subgroup (Langlands.GeneralLinear n R) :=
  (upperUnipotent n R).comap (MulAut.conj (weylLong n R)).toMonoidHom

/-- Membership in the lower unipotent subgroup is exactly the lower entry condition. -/
theorem mem_lowerUnipotent_iff (g : Langlands.GeneralLinear n R) :
    g ∈ lowerUnipotent n R ↔
      (∀ i j : Fin n, i < j → g i j = 0) ∧ ∀ i : Fin n, g i i = 1 := by
  change
    ((∀ i j : Fin n, j < i →
      (weylLong n R * g * (weylLong n R)⁻¹) i j = 0) ∧
      ∀ i : Fin n, (weylLong n R * g * (weylLong n R)⁻¹) i i = 1) ↔ _
  simp only [weylLong_inv, weylLong_conjugate_entry]
  constructor
  · rintro ⟨hzero, hdiag⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simpa only [Fin.rev_rev] using hzero i.rev j.rev (Fin.rev_lt_rev.mpr hij)
    · simpa only [Fin.rev_rev] using hdiag i.rev
  · rintro ⟨hzero, hdiag⟩
    exact ⟨fun i j hji => hzero i.rev j.rev (Fin.rev_lt_rev.mpr hji),
      fun i => hdiag i.rev⟩

/-- Upper and lower unipotent matrices intersect only in the identity. -/
theorem upperUnipotent_inf_lowerUnipotent :
    upperUnipotent n R ⊓ lowerUnipotent n R = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  rw [Subgroup.mem_bot]
  apply Units.ext
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [(mem_lowerUnipotent_iff n R g).mp hg.2 |>.1 i j hij]
    simp [ne_of_lt hij]
  · simpa using hg.1.2 i
  · rw [hg.1.1 hji]
    simp [ne_of_gt hji]

variable (w : Equiv.Perm (Fin n))

/-- Shalika's `U_w⁺ = U ∩ w⁻¹ U w`, with the published permutation matrix. -/
def permutationUnipotentPlus : Subgroup (Langlands.GeneralLinear n R) :=
  upperUnipotent n R ⊓
    (upperUnipotent n R).comap (MulAut.conj (permutation n R w)).toMonoidHom

/-- Shalika's `U_w⁻ = U ∩ w⁻¹ Ubar w`, with the published permutation matrix. -/
def permutationUnipotentMinus : Subgroup (Langlands.GeneralLinear n R) :=
  upperUnipotent n R ⊓
    (lowerUnipotent n R).comap (MulAut.conj (permutation n R w)).toMonoidHom

theorem mem_permutationUnipotentPlus_iff (g : Langlands.GeneralLinear n R) :
    g ∈ permutationUnipotentPlus n R w ↔
      g ∈ upperUnipotent n R ∧
        permutation n R w * g * (permutation n R w)⁻¹ ∈ upperUnipotent n R :=
  Iff.rfl

theorem mem_permutationUnipotentMinus_iff (g : Langlands.GeneralLinear n R) :
    g ∈ permutationUnipotentMinus n R w ↔
      g ∈ upperUnipotent n R ∧
        permutation n R w * g * (permutation n R w)⁻¹ ∈ lowerUnipotent n R :=
  Iff.rfl

/-- Plus membership kills precisely the additional entries whose order is reversed by `w`. -/
theorem mem_permutationUnipotentPlus_iff_entries (g : Langlands.GeneralLinear n R) :
    g ∈ permutationUnipotentPlus n R w ↔
      g ∈ upperUnipotent n R ∧
        ∀ i j : Fin n, w j < w i → g i j = 0 := by
  rw [mem_permutationUnipotentPlus_iff]
  constructor
  · rintro ⟨hg, hc⟩
    refine ⟨hg, fun i j hji => ?_⟩
    have h := hc.1 hji
    simpa only [permutation_conjugate_entry, Equiv.Perm.coe_inv,
      Equiv.symm_apply_apply] using h
  · rintro ⟨hg, hzero⟩
    refine ⟨hg, ?_⟩
    rw [mem_upperUnipotent_iff]
    simp only [permutation_conjugate_entry]
    refine ⟨fun i j hji => ?_, fun i => hg.2 _⟩
    apply hzero
    simpa only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using hji

/-- Minus membership kills the additional entries whose order is preserved by `w`. -/
theorem mem_permutationUnipotentMinus_iff_entries (g : Langlands.GeneralLinear n R) :
    g ∈ permutationUnipotentMinus n R w ↔
      g ∈ upperUnipotent n R ∧
        ∀ i j : Fin n, w i < w j → g i j = 0 := by
  rw [mem_permutationUnipotentMinus_iff]
  constructor
  · rintro ⟨hg, hc⟩
    refine ⟨hg, fun i j hij => ?_⟩
    have h := (mem_lowerUnipotent_iff n R _).mp hc |>.1 (w i) (w j) hij
    simpa only [permutation_conjugate_entry, Equiv.Perm.coe_inv,
      Equiv.symm_apply_apply] using h
  · rintro ⟨hg, hzero⟩
    refine ⟨hg, ?_⟩
    rw [mem_lowerUnipotent_iff]
    simp only [permutation_conjugate_entry]
    refine ⟨fun i j hij => ?_, fun i => hg.2 _⟩
    apply hzero
    simpa only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using hij

theorem permutationUnipotentPlus_le_upperUnipotent :
    permutationUnipotentPlus n R w ≤ upperUnipotent n R :=
  inf_le_left

theorem permutationUnipotentMinus_le_upperUnipotent :
    permutationUnipotentMinus n R w ≤ upperUnipotent n R :=
  inf_le_left

/-- The plus and minus permutation subgroups have trivial intersection. -/
theorem permutationUnipotentPlus_inf_minus :
    permutationUnipotentPlus n R w ⊓ permutationUnipotentMinus n R w = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  rw [Subgroup.mem_bot]
  have hc : permutation n R w * g * (permutation n R w)⁻¹ = 1 := by
    have hmem : permutation n R w * g * (permutation n R w)⁻¹ ∈
        upperUnipotent n R ⊓ lowerUnipotent n R := ⟨hg.1.2, hg.2.2⟩
    rwa [upperUnipotent_inf_lowerUnipotent, Subgroup.mem_bot] at hmem
  apply (MulAut.conj (permutation n R w)).injective
  change permutation n R w * g * (permutation n R w)⁻¹ =
    permutation n R w * 1 * (permutation n R w)⁻¹
  rw [hc, mul_one, mul_inv_cancel]

/-- The actual upper triangular double coset of the specified permutation matrix. -/
def upperBruhatCell : Set (Langlands.GeneralLinear n R) :=
  {g | ∃ b₁ ∈ upperTriangularSubgroup n R,
    ∃ b₂ ∈ upperTriangularSubgroup n R, g = b₁ * permutation n R w * b₂}

/-- The cell as a subtype; its topology is the inherited matrix-group topology. -/
abbrev UpperBruhatCell :=
  ↥(upperBruhatCell n R w)

theorem mem_upperBruhatCell_iff (g : Langlands.GeneralLinear n R) :
    g ∈ upperBruhatCell n R w ↔
      ∃ b₁ ∈ upperTriangularSubgroup n R,
        ∃ b₂ ∈ upperTriangularSubgroup n R, g = b₁ * permutation n R w * b₂ :=
  Iff.rfl

theorem mul_mem_upperBruhatCell (b : upperTriangularSubgroup n R)
    {g : Langlands.GeneralLinear n R} (hg : g ∈ upperBruhatCell n R w) :
    b.val * g ∈ upperBruhatCell n R w := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  exact ⟨b.val * b₁, mul_mem b.property hb₁, b₂, hb₂, by simp only [mul_assoc]⟩

theorem mem_upperBruhatCell_mul (b : upperTriangularSubgroup n R)
    {g : Langlands.GeneralLinear n R} (hg : g ∈ upperBruhatCell n R w) :
    g * b.val ∈ upperBruhatCell n R w := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  exact ⟨b₁, hb₁, b₂ * b.val, mul_mem hb₂ b.property, by simp only [mul_assoc]⟩

/-- Left multiplication by the upper triangular subgroup acts on each cell. -/
instance upperBruhatCellLeftAction :
    MulAction (upperTriangularSubgroup n R) (UpperBruhatCell n R w) where
  smul b g := ⟨b.val * g.val, mul_mem_upperBruhatCell n R w b g.property⟩
  one_smul g := Subtype.ext (one_mul g.val)
  mul_smul a b g := Subtype.ext (mul_assoc a.val b.val g.val)

/-- Right multiplication is an action of the opposite upper triangular group. -/
instance upperBruhatCellRightAction :
    MulAction (upperTriangularSubgroup n R)ᵐᵒᵖ (UpperBruhatCell n R w) where
  smul b g := ⟨g.val * b.unop.val, mem_upperBruhatCell_mul n R w b.unop g.property⟩
  one_smul g := Subtype.ext (mul_one g.val)
  mul_smul a b g := Subtype.ext (mul_assoc g.val b.unop.val a.unop.val).symm

/-- Restrict the left action through the actual inclusion `U → B`. -/
instance upperBruhatCellUnipotentLeftAction :
    MulAction (upperUnipotent n R) (UpperBruhatCell n R w) :=
  MulAction.compHom (UpperBruhatCell n R w) (upperUnipotentInUpperTriangular n R)

/-- Restrict the right action through the opposite of the actual inclusion `U → B`. -/
instance upperBruhatCellUnipotentRightAction :
    MulAction (upperUnipotent n R)ᵐᵒᵖ (UpperBruhatCell n R w) :=
  MulAction.compHom (UpperBruhatCell n R w)
    { toFun := fun u => MulOpposite.op (upperUnipotentInUpperTriangular n R u.unop)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

@[simp]
theorem upperBruhatCell_left_smul_val (b : upperTriangularSubgroup n R)
    (g : UpperBruhatCell n R w) : (b • g).val = b.val * g.val := rfl

@[simp]
theorem upperBruhatCell_right_smul_val (b : (upperTriangularSubgroup n R)ᵐᵒᵖ)
    (g : UpperBruhatCell n R w) : (b • g).val = g.val * b.unop.val := rfl

@[simp]
theorem upperBruhatCell_unipotent_left_smul_val (u : upperUnipotent n R)
    (g : UpperBruhatCell n R w) : (u • g).val = u.val * g.val := rfl

@[simp]
theorem upperBruhatCell_unipotent_right_smul_val (u : (upperUnipotent n R)ᵐᵒᵖ)
    (g : UpperBruhatCell n R w) : (u • g).val = g.val * u.unop.val := rfl

/-- The elementary map `(b,v) ↦ b * p * v` into the actual cell. -/
def upperBruhatCellMap :
    upperTriangularSubgroup n R × permutationUnipotentMinus n R w →
      UpperBruhatCell n R w :=
  fun x => ⟨x.1.val * permutation n R w * x.2.val,
    x.1.val, x.1.property, x.2.val,
    upperUnipotent_le_upperTriangular n R x.2.property.1, rfl⟩

@[simp]
theorem upperBruhatCellMap_val
    (x : upperTriangularSubgroup n R × permutationUnipotentMinus n R w) :
    (upperBruhatCellMap n R w x).val = x.1.val * permutation n R w * x.2.val :=
  rfl

theorem upperBruhatCellMap_mem
    (x : upperTriangularSubgroup n R × permutationUnipotentMinus n R w) :
    x.1.val * permutation n R w * x.2.val ∈ upperBruhatCell n R w :=
  (upperBruhatCellMap n R w x).property

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- Multiplication is continuous for the actual subgroup and cell topologies. -/
@[fun_prop]
theorem continuous_upperBruhatCellMap : Continuous (upperBruhatCellMap n R w) := by
  apply Continuous.subtype_mk
  exact ((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
    (continuous_subtype_val.comp continuous_snd)

/-- The same map bundled as a continuous map. -/
def upperBruhatCellMapContinuous :
    C(upperTriangularSubgroup n R × permutationUnipotentMinus n R w,
      UpperBruhatCell n R w) :=
  ⟨upperBruhatCellMap n R w, continuous_upperBruhatCellMap n R w⟩

end Topology

section Torus

variable {K : Type u} [Field K]

/-- The existing unit-diagonal matrix is upper triangular. -/
theorem diagonalUnits_mem_upperTriangular (d : Fin n → Kˣ) :
    Iwasawa.diagonalUnits d ∈ upperTriangularSubgroup n K := by
  rw [mem_upperTriangularSubgroup_iff]
  intro i j hji
  change (Matrix.diagonal fun i => (d i : K)) i j = 0
  simp [ne_of_gt hji]

/-- Move a diagonal matrix past the specified permutation, without changing conventions. -/
theorem permutation_mul_diagonalUnits (d : Fin n → Kˣ) :
    permutation n K w * Iwasawa.diagonalUnits d =
      Iwasawa.diagonalUnits (fun i => d (w⁻¹ i)) * permutation n K w := by
  apply Units.ext
  ext i j
  rw [permutation_mul_entry, mul_permutation_entry]
  change (Matrix.diagonal fun i => (d i : K)) (w⁻¹ i) j =
    (Matrix.diagonal fun i => (d (w⁻¹ i) : K)) i (w j)
  by_cases h : w j = i
  · subst i
    simp
  · have h' : w.symm i ≠ j := by
      intro he
      apply h
      simpa using (congrArg w he).symm
    simp [Equiv.Perm.coe_inv, h', Ne.symm h]

/-- The torus-parameter multiplication lies in the cell. -/
theorem unipotent_diagonal_mem_upperBruhatCell
    (u₁ u₂ : upperUnipotent n K) (d : Fin n → Kˣ) :
    u₁.val * permutation n K w * Iwasawa.diagonalUnits d * u₂.val ∈
      upperBruhatCell n K w := by
  refine ⟨u₁.val * Iwasawa.diagonalUnits (fun i => d (w⁻¹ i)),
    mul_mem (upperUnipotent_le_upperTriangular n K u₁.property)
      (diagonalUnits_mem_upperTriangular n _),
    u₂.val, upperUnipotent_le_upperTriangular n K u₂.property, ?_⟩
  simp only [mul_assoc, permutation_mul_diagonalUnits]

/-- Shalika's second coordinate map, using the existing actual diagonal homomorphism. -/
def upperBruhatTorusMap :
    upperUnipotent n K × (Fin n → Kˣ) × upperUnipotent n K →
      UpperBruhatCell n K w :=
  fun x => ⟨x.1.val * permutation n K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val,
    unipotent_diagonal_mem_upperBruhatCell n w x.1 x.2.2 x.2.1⟩

@[simp]
theorem upperBruhatTorusMap_val
    (x : upperUnipotent n K × (Fin n → Kˣ) × upperUnipotent n K) :
    (upperBruhatTorusMap n w x).val =
      x.1.val * permutation n K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val :=
  rfl

variable [TopologicalSpace K]

/-- Continuity of the existing diagonal homomorphism needs only the coefficient topology. -/
@[fun_prop]
theorem continuous_diagonalUnits :
    Continuous (Iwasawa.diagonalUnits (m := n) (F := K)) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i)).matrix_diagonal
  · exact (continuous_pi fun i =>
      Units.continuous_coe_inv.comp (continuous_apply i)).matrix_diagonal

variable [IsTopologicalRing K]

/-- Continuity of the torus-coordinate map for the inherited matrix topologies. -/
@[fun_prop]
theorem continuous_upperBruhatTorusMap : Continuous (upperBruhatTorusMap n w (K := K)) := by
  apply Continuous.subtype_mk
  exact (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
    ((continuous_diagonalUnits n).comp (continuous_fst.comp continuous_snd))).mul
    (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))

/-- The torus-coordinate multiplication map bundled with continuity. -/
def upperBruhatTorusMapContinuous :
    C(upperUnipotent n K × (Fin n → Kˣ) × upperUnipotent n K,
      UpperBruhatCell n K w) :=
  ⟨upperBruhatTorusMap n w, continuous_upperBruhatTorusMap n w⟩

end Torus

end Langlands.GeneralLinear
