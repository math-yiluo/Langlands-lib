import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Ring.Compact

/-!
# The congruence subgroups used in newvector theory

The rank is `n + 1`, so `n = 0` includes rank one. Reduction is performed
on actual invertible integral matrices. See JPSS (1981), Section 5.1,
page 211, and the paired Markdown for the level-zero convention.
-/

noncomputable section

namespace Langlands.Conductor

universe uR uF

open Matrix

variable {R : Type uR} [CommRing R]

/-- The subgroup of invertible matrices whose specified row is the
corresponding row of the identity matrix. -/
def rowStabilizer {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    Subgroup (GeneralLinearGroup ι R) where
  carrier := {g | (g : Matrix ι ι R) i = (1 : Matrix ι ι R) i}
  one_mem' := rfl
  mul_mem' := by
    intro g h hg hh
    funext j
    change ((g : Matrix ι ι R) * (h : Matrix ι ι R)) i j = _
    rw [Matrix.mul_apply]
    simp_rw [congrFun hg]
    change ((1 : Matrix ι ι R) * (h : Matrix ι ι R)) i j = _
    simpa only [Matrix.one_mul] using congrFun hh j
  inv_mem' := by
    intro g hg
    have h := congrArg (fun a : GeneralLinearGroup ι R =>
      (a : Matrix ι ι R) i) (mul_inv_cancel g)
    funext j
    have hj := congrFun h j
    change ((g : Matrix ι ι R) * (g⁻¹ : GeneralLinearGroup ι R)) i j = _ at hj
    rw [Matrix.mul_apply] at hj
    simp_rw [congrFun hg] at hj
    change ((1 : Matrix ι ι R) * (g⁻¹ : GeneralLinearGroup ι R)) i j = _ at hj
    simpa only [Matrix.one_mul, GeneralLinearGroup.coe_one] using hj

/-- Integral matrices whose last row is the last standard row modulo `I`. -/
def integralCongruence (n : ℕ) (I : Ideal R) :
    Subgroup (GeneralLinearGroup (Fin (n + 1)) R) :=
  (rowStabilizer (R := R ⧸ I) (Fin.last n)).comap
    (GeneralLinearGroup.map (Ideal.Quotient.mk I))

/-- Entrywise membership in the reduction stabilizer. -/
theorem mem_integralCongruence (n : ℕ) (I : Ideal R)
    (g : GeneralLinearGroup (Fin (n + 1)) R) :
    g ∈ integralCongruence n I ↔
      ∀ j, g (Fin.last n) j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
        (Fin.last n) j ∈ I := by
  change (GeneralLinearGroup.map (Ideal.Quotient.mk I) g :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⧸ I)) (Fin.last n) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⧸ I)) (Fin.last n) ↔ _
  rw [funext_iff]
  apply forall_congr'
  intro j
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simp [GeneralLinearGroup.map_apply, Matrix.one_apply]

/-- Reduction modulo the unit ideal imposes no restriction. -/
@[simp]
theorem integralCongruence_top (n : ℕ) :
    integralCongruence (R := R) n ⊤ = ⊤ := by
  ext g
  simp [mem_integralCongruence]

/-- Increasing the ideal weakens the congruence condition. -/
theorem integralCongruence_mono (n : ℕ) {I J : Ideal R} (h : I ≤ J) :
    integralCongruence n I ≤ integralCongruence n J := by
  intro g hg
  exact (mem_integralCongruence n J g).2 fun j =>
    h ((mem_integralCongruence n I g).1 hg j)

/-- In rank one the condition is the usual unit congruence `g - 1 ∈ I`. -/
@[simp]
theorem mem_integralCongruence_rankOne (I : Ideal R)
    (g : GeneralLinearGroup (Fin 1) R) :
    g ∈ integralCongruence 0 I ↔ g 0 0 - 1 ∈ I := by
  simp [mem_integralCongruence, Matrix.one_apply]

/-- Deleting a final standard row and column preserves the determinant. -/
theorem det_eq_upperLeft_of_row (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : A (Fin.last n) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
      (Fin.last n)) :
    A.det = (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row A (Fin.last n)]
  simp_rw [congrFun h]
  simp [Matrix.one_apply, pow_add, ← mul_pow]

/-- The source's bottom-right block is a unit at every positive level. -/
theorem isUnit_last_entry [IsLocalRing R] (n a : ℕ) (ha : 0 < a)
    (g : GeneralLinearGroup (Fin (n + 1)) R)
    (hg : g ∈ integralCongruence n (IsLocalRing.maximalIdeal R ^ a)) :
    IsUnit (g (Fin.last n) (Fin.last n)) := by
  have hm := integralCongruence_mono n
    (show IsLocalRing.maximalIdeal R ^ a ≤ IsLocalRing.maximalIdeal R by
      simpa only [pow_one] using
        (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal R) ha)) hg
  have hx := (mem_integralCongruence n (IsLocalRing.maximalIdeal R) g).1 hm (Fin.last n)
  have hr : IsLocalRing.residue R (g (Fin.last n) (Fin.last n)) = 1 := by
    change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) _ =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) 1
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    simpa only [Matrix.one_apply_eq] using hx
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 (hr ▸ one_ne_zero)

/-- The source's upper-left block is invertible at every positive level. -/
theorem isUnit_upperLeft [IsLocalRing R] (n a : ℕ) (ha : 0 < a)
    (g : GeneralLinearGroup (Fin (n + 1)) R)
    (hg : g ∈ integralCongruence n (IsLocalRing.maximalIdeal R ^ a)) :
    IsUnit ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) R).submatrix
      Fin.castSucc Fin.castSucc) := by
  have hm := integralCongruence_mono n
    (show IsLocalRing.maximalIdeal R ^ a ≤ IsLocalRing.maximalIdeal R by
      simpa only [pow_one] using
        (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal R) ha)) hg
  have hrow : (GeneralLinearGroup.map (IsLocalRing.residue R) g :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (IsLocalRing.ResidueField R)) (Fin.last n) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) (IsLocalRing.ResidueField R))
        (Fin.last n) := hm
  apply (Matrix.isUnit_iff_isUnit_det _).2
  apply isUnit_of_map_unit (IsLocalRing.residue R)
  rw [RingHom.map_det]
  have hd := det_eq_upperLeft_of_row n _ hrow
  exact hd ▸ Matrix.isUnits_det_units (GeneralLinearGroup.map (IsLocalRing.residue R) g)

variable {F : Type uF} [Field F]

/-- The image of the integral general linear group inside the field group. -/
def integralSubgroup (O : Subring F) (n : ℕ) :
    Subgroup (GeneralLinearGroup (Fin (n + 1)) F) :=
  (GeneralLinearGroup.map (n := Fin (n + 1)) O.subtype).range

/-- A congruence subgroup as a subgroup of the actual general linear group
over the field, using entrywise inclusion of integral matrices. -/
def congruenceSubgroup (O : Subring F) (n : ℕ) (I : Ideal O) :
    Subgroup (GeneralLinearGroup (Fin (n + 1)) F) :=
  (integralCongruence n I).map (GeneralLinearGroup.map O.subtype)

/-- Inclusion of integral invertible matrices is injective. -/
theorem integral_map_injective (O : Subring F) (n : ℕ) :
    Function.Injective (GeneralLinearGroup.map (n := Fin (n + 1)) O.subtype) := by
  intro g h e
  apply GeneralLinearGroup.ext
  intro i j
  apply Subtype.val_injective
  exact congrArg (fun a : GeneralLinearGroup (Fin (n + 1)) F => a i j) e

/-- Integral invertible matrices are exactly those matrices for which both
the matrix and its inverse have integral entries. -/
theorem mem_integralSubgroup (O : Subring F) (n : ℕ)
    (g : GeneralLinearGroup (Fin (n + 1)) F) :
    g ∈ integralSubgroup O n ↔
      (∀ i j, g i j ∈ O) ∧ (∀ i j, g⁻¹ i j ∈ O) := by
  constructor
  · rintro ⟨h, rfl⟩
    constructor
    · exact fun i j => (h i j).property
    · intro i j
      rw [← map_inv]
      exact (h⁻¹ i j).property
  · rintro ⟨hg, hi⟩
    let A : Matrix (Fin (n + 1)) (Fin (n + 1)) O := fun i j => ⟨g i j, hg i j⟩
    let B : Matrix (Fin (n + 1)) (Fin (n + 1)) O := fun i j => ⟨g⁻¹ i j, hi i j⟩
    have hab : A * B = 1 := by
      apply Matrix.ext
      intro i j
      apply Subtype.val_injective
      change ((A * B).map O.subtype) i j = ((1 : Matrix _ _ O).map O.subtype) i j
      rw [Matrix.map_mul, Matrix.map_one O.subtype (map_zero O.subtype) (map_one O.subtype)]
      change ((g * g⁻¹ : GeneralLinearGroup (Fin (n + 1)) F) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j = _
      rw [mul_inv_cancel, GeneralLinearGroup.coe_one]
    have hba : B * A = 1 := by
      apply Matrix.ext
      intro i j
      apply Subtype.val_injective
      change ((B * A).map O.subtype) i j = ((1 : Matrix _ _ O).map O.subtype) i j
      rw [Matrix.map_mul, Matrix.map_one O.subtype (map_zero O.subtype) (map_one O.subtype)]
      change ((g⁻¹ * g : GeneralLinearGroup (Fin (n + 1)) F) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j = _
      rw [inv_mul_cancel, GeneralLinearGroup.coe_one]
    exact ⟨⟨A, B, hab, hba⟩, GeneralLinearGroup.ext (fun _ _ => rfl)⟩

/-- The field subgroup has exactly the intended integral representatives. -/
theorem map_mem_congruenceSubgroup (O : Subring F) (n : ℕ) (I : Ideal O)
    (g : GeneralLinearGroup (Fin (n + 1)) O) :
    GeneralLinearGroup.map O.subtype g ∈ congruenceSubgroup O n I ↔
      g ∈ integralCongruence n I := by
  exact Subgroup.mem_map_iff_mem (integral_map_injective O n)

@[simp]
theorem congruenceSubgroup_top (O : Subring F) (n : ℕ) :
    congruenceSubgroup O n ⊤ = integralSubgroup O n := by
  simp [congruenceSubgroup, integralSubgroup, Subgroup.map_top]

/-- The local-field newvector subgroup at exponent `a`.
The valuation is used only to specify its integer ring and maximal ideal. -/
def levelSubgroup (F : Type uF) [Field F] [ValuativeRel F] (n a : ℕ) :
    Subgroup (GeneralLinearGroup (Fin (n + 1)) F) :=
  congruenceSubgroup (ValuativeRel.valuation F).integer n
    (IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ a)

@[simp]
theorem levelSubgroup_zero (F : Type uF) [Field F] [ValuativeRel F] (n : ℕ) :
    levelSubgroup F n 0 = integralSubgroup (ValuativeRel.valuation F).integer n := by
  simp [levelSubgroup]

/-- Higher levels form smaller subgroups. -/
theorem levelSubgroup_antitone (F : Type uF) [Field F] [ValuativeRel F] (n : ℕ) :
    Antitone (levelSubgroup F n) := by
  intro a b hab
  exact Subgroup.map_mono (integralCongruence_mono n (Ideal.pow_le_pow_right hab))

section Topology

open Topology

/-- An open ideal gives an open integral reduction stabilizer. -/
theorem isOpen_integralCongruence [TopologicalSpace R] [IsTopologicalRing R]
    (n : ℕ) (I : Ideal R) (hI : IsOpen (I : Set R)) :
    IsOpen (integralCongruence n I : Set (GeneralLinearGroup (Fin (n + 1)) R)) := by
  have hset : (integralCongruence n I : Set (GeneralLinearGroup (Fin (n + 1)) R)) =
      ⋂ j, {g | g (Fin.last n) j -
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (Fin.last n) j ∈ I} := by
    ext g
    simp only [SetLike.mem_coe, mem_integralCongruence, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  exact isOpen_iInter_of_finite fun j => hI.preimage (by fun_prop)

variable [TopologicalSpace F] [IsTopologicalRing F]

omit [IsTopologicalRing F] in
/-- Integral general linear groups are open when the subring is open. -/
theorem isOpen_integralSubgroup (O : Subring F) (n : ℕ) (hO : IsOpen (O : Set F)) :
    IsOpen (integralSubgroup O n : Set (GeneralLinearGroup (Fin (n + 1)) F)) := by
  have hset : (integralSubgroup O n : Set (GeneralLinearGroup (Fin (n + 1)) F)) =
      (⋂ i, ⋂ j, {g | g i j ∈ O}) ∩ (⋂ i, ⋂ j, {g | g⁻¹ i j ∈ O}) := by
    ext g
    simp only [SetLike.mem_coe, mem_integralSubgroup, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  apply IsOpen.inter
  · exact isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun j => hO.preimage (by fun_prop)
  · exact isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun j => hO.preimage (by fun_prop)

omit [IsTopologicalRing F] in
/-- The inclusion of integral general linear groups is an open embedding
when the integer subring is open. -/
theorem isOpenEmbedding_integral_map (O : Subring F) (n : ℕ)
    (hO : IsOpen (O : Set F)) :
    IsOpenEmbedding (GeneralLinearGroup.map (n := Fin (n + 1)) O.subtype) where
  toIsEmbedding := IsEmbedding.generalLinearGroup_map IsEmbedding.subtypeVal
  isOpen_range := isOpen_integralSubgroup O n hO

/-- Open congruence conditions remain open inside the field group. -/
theorem isOpen_congruenceSubgroup (O : Subring F) (n : ℕ) (I : Ideal O)
    (hO : IsOpen (O : Set F)) (hI : IsOpen (I : Set O)) :
    IsOpen (congruenceSubgroup O n I : Set (GeneralLinearGroup (Fin (n + 1)) F)) :=
  (isOpenEmbedding_integral_map O n hO).isOpenMap _
    (isOpen_integralCongruence n I hI)

/-- Congruence subgroups are compact over a compact Hausdorff integer ring. -/
theorem isCompact_congruenceSubgroup [T2Space F] (O : Subring F) [CompactSpace O]
    (n : ℕ) (I : Ideal O) (hI : IsOpen (I : Set O)) :
    IsCompact (congruenceSubgroup O n I : Set (GeneralLinearGroup (Fin (n + 1)) F)) := by
  let : CompactSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) O) :=
    inferInstanceAs (CompactSpace (Fin (n + 1) → Fin (n + 1) → O))
  have hclosed := (integralCongruence n I).isClosed_of_isOpen
    (isOpen_integralCongruence n I hI)
  exact hclosed.isCompact.image (Continuous.generalLinearGroup_map continuous_subtype_val)

end Topology

section LocalField

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem localField_t2 : T2Space F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

/-- The actual open newvector subgroup of a nonarchimedean local field. -/
def levelOpenSubgroup (n a : ℕ) :
    OpenSubgroup (GeneralLinearGroup (Fin (n + 1)) F) := by
  have := localField_t2 F
  exact
    { toSubgroup := levelSubgroup F n a
      isOpen' := isOpen_congruenceSubgroup _ _ _
        (Valuation.isOpen_integer (v := ValuativeRel.valuation F))
        (IsLocalRing.isOpen_maximalIdeal_pow (ValuativeRel.valuation F).integer a) }

/-- Each newvector subgroup is compact in the inherited matrix-group topology. -/
theorem isCompact_levelOpenSubgroup (n a : ℕ) :
    IsCompact (levelOpenSubgroup F n a : Set (GeneralLinearGroup (Fin (n + 1)) F)) := by
  have := localField_t2 F
  exact isCompact_congruenceSubgroup _ _ _
    (IsLocalRing.isOpen_maximalIdeal_pow (ValuativeRel.valuation F).integer a)

end LocalField

end Langlands.Conductor
