import Langlands.GroupScheme.SpecialLinearTernaryPresentation

/-! # Homomorphisms out of ternary SL from two binary SL homomorphisms -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.SpecialLinear.TernaryPresentation

section CellExtension

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Data for extending a map defined on a subgroup `P` across the double coset `P n P`. -/
structure CellData (P : Subgroup G) (n : G) (f : G → H) (ν : H) : Prop where
  not_mem : n ∉ P
  sq_mem : n * n ∈ P
  map_mul : ∀ p ∈ P, ∀ q ∈ P, f (p * q) = f p * f q
  conj : ∀ μ ∈ P, n * μ * n⁻¹ ∈ P → f (n * μ * n⁻¹) = ν * f μ * ν⁻¹
  sq : f (n * n) = ν * ν

/-- The compatibility of `f` at an element `r` of `P` whose `n`-conjugate leaves `P`. -/
def CellGood (P : Subgroup G) (n : G) (f : G → H) (ν : H) (r : G) : Prop :=
  ∃ p₁ ∈ P, ∃ p₂ ∈ P, n * r * n = p₁ * n * p₂ ∧ ν * f r * ν = f p₁ * ν * f p₂

namespace CellData

variable {P : Subgroup G} {n : G} {f : G → H} {ν : H}

theorem map_one (D : CellData P n f ν) : f 1 = 1 := by
  have h := D.map_mul 1 P.one_mem 1 P.one_mem
  rw [mul_one] at h
  exact mul_eq_left.mp h.symm

theorem map_inv (D : CellData P n f ν) {p : G} (hp : p ∈ P) : f p⁻¹ = (f p)⁻¹ := by
  have h := D.map_mul p hp p⁻¹ (P.inv_mem hp)
  rw [mul_inv_cancel, D.map_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem cell_not_mem (D : CellData P n f ν) {p q : G} (hp : p ∈ P) (hq : q ∈ P) :
    p * n * q ∉ P := by
  intro h
  apply D.not_mem
  have : n = p⁻¹ * (p * n * q) * q⁻¹ := by group
  rw [this]
  exact P.mul_mem (P.mul_mem (P.inv_mem hp) h) (P.inv_mem hq)

theorem cell_eq (D : CellData P n f ν) {p q p' q' : G} (hp : p ∈ P) (hq : q ∈ P)
    (hp' : p' ∈ P) (hq' : q' ∈ P) (h : p * n * q = p' * n * q') :
    f p * ν * f q = f p' * ν * f q' := by
  have hμ : q * q'⁻¹ ∈ P := P.mul_mem hq (P.inv_mem hq')
  have hconj : n * (q * q'⁻¹) * n⁻¹ = p⁻¹ * p' := by
    have : n * q = p⁻¹ * (p' * n * q') := by rw [← h]; group
    calc n * (q * q'⁻¹) * n⁻¹ = (n * q) * q'⁻¹ * n⁻¹ := by group
      _ = p⁻¹ * p' := by rw [this]; group
  have key := D.conj _ hμ (hconj ▸ P.mul_mem (P.inv_mem hp) hp')
  rw [hconj, D.map_mul _ (P.inv_mem hp) _ hp', D.map_mul _ hq _ (P.inv_mem hq'),
    D.map_inv hp, D.map_inv hq'] at key
  calc f p * ν * f q = f p * (ν * (f q * (f q')⁻¹) * ν⁻¹) * ν * f q' := by group
    _ = f p * ((f p)⁻¹ * f p') * ν * f q' := by rw [key]
    _ = f p' * ν * f q' := by group

theorem conj_inv_mem (D : CellData P n f ν) {μ : G} (h : n * μ * n⁻¹ ∈ P) :
    n⁻¹ * μ * n ∈ P := by
  have : n⁻¹ * μ * n = (n * n)⁻¹ * (n * μ * n⁻¹) * (n * n) := by group
  rw [this]
  exact P.mul_mem (P.mul_mem (P.inv_mem D.sq_mem) h) D.sq_mem

theorem map_conj_inv (D : CellData P n f ν) {μ : G} (hμ : μ ∈ P) (h : n * μ * n⁻¹ ∈ P) :
    f (n⁻¹ * μ * n) = ν⁻¹ * f μ * ν := by
  have h' := D.conj _ (D.conj_inv_mem h) (by
    have : n * (n⁻¹ * μ * n) * n⁻¹ = μ := by group
    rw [this]; exact hμ)
  have : n * (n⁻¹ * μ * n) * n⁻¹ = μ := by group
  rw [this] at h'
  rw [h']
  group

theorem map_n_mul_n (D : CellData P n f ν) {q : G} (hq : q ∈ P) (h : n * q * n ∈ P) :
    f (n * q * n) = ν * f q * ν := by
  have h₁ : n * q * n⁻¹ = (n * q * n) * (n * n)⁻¹ := by group
  have hm : n * q * n⁻¹ ∈ P := by
    rw [h₁]; exact P.mul_mem h (P.inv_mem D.sq_mem)
  have h₂ : n * q * n = (n * q * n⁻¹) * (n * n) := by group
  rw [h₂, D.map_mul _ hm _ D.sq_mem, D.conj _ hq hm, D.sq]
  group

/-- Goodness is invariant under multiplying by elements of `P ∩ n⁻¹ P n` on both sides. -/
theorem cellGood_mul (D : CellData P n f ν) {μ r μ' : G} (hμ : μ ∈ P) (hμc : n * μ * n⁻¹ ∈ P)
    (hr : r ∈ P) (hμ' : μ' ∈ P) (hμ'c : n * μ' * n⁻¹ ∈ P) (h : CellGood P n f ν r) :
    CellGood P n f ν (μ * r * μ') := by
  obtain ⟨p₁, hp₁, p₂, hp₂, heq, hval⟩ := h
  have hi := D.conj_inv_mem hμ'c
  refine ⟨n * μ * n⁻¹ * p₁, P.mul_mem hμc hp₁, p₂ * (n⁻¹ * μ' * n), P.mul_mem hp₂ hi, ?_, ?_⟩
  · calc n * (μ * r * μ') * n = (n * μ * n⁻¹) * (n * r * n) * (n⁻¹ * μ' * n) := by group
      _ = _ := by rw [heq]; group
  · rw [D.map_mul _ (P.mul_mem hμ hr) _ hμ', D.map_mul _ hμ _ hr,
      D.map_mul _ hμc _ hp₁, D.map_mul _ hp₂ _ hi, D.conj _ hμ hμc, D.map_conj_inv hμ' hμ'c]
    calc ν * (f μ * f r * f μ') * ν = ν * f μ * ν⁻¹ * (ν * f r * ν) * (ν⁻¹ * f μ' * ν) := by
          group
      _ = _ := by rw [hval]; group

end CellData

open Classical in
/-- The extension of `f` across the double coset `P n P`. -/
def cellExtendFun (P : Subgroup G) (n : G) (f : G → H) (ν : H) (g : G) : H :=
  if hc : ∃ pq : G × G, pq.1 ∈ P ∧ pq.2 ∈ P ∧ g = pq.1 * n * pq.2 then
    f hc.choose.1 * ν * f hc.choose.2
  else f g

namespace CellData

variable {P : Subgroup G} {n : G} {f : G → H} {ν : H}

theorem cellExtendFun_of_mem (D : CellData P n f ν) {g : G} (hg : g ∈ P) :
    cellExtendFun P n f ν g = f g := by
  have hc : ¬ ∃ pq : G × G, pq.1 ∈ P ∧ pq.2 ∈ P ∧ g = pq.1 * n * pq.2 := by
    rintro ⟨pq, h₁, h₂, rfl⟩
    exact D.cell_not_mem h₁ h₂ hg
  simp only [cellExtendFun, hc, ↓reduceDIte]

theorem cellExtendFun_cell (D : CellData P n f ν) {p q : G} (hp : p ∈ P) (hq : q ∈ P) :
    cellExtendFun P n f ν (p * n * q) = f p * ν * f q := by
  have hc : ∃ pq : G × G, pq.1 ∈ P ∧ pq.2 ∈ P ∧ p * n * q = pq.1 * n * pq.2 :=
    ⟨(p, q), hp, hq, rfl⟩
  simp only [cellExtendFun, hc, ↓reduceDIte]
  obtain ⟨h₁, h₂, h₃⟩ := hc.choose_spec
  exact (D.cell_eq hp hq h₁ h₂ h₃).symm

variable (cover : ∀ g ∉ P, ∃ p ∈ P, ∃ q ∈ P, g = p * n * q)
  (good : ∀ q ∈ P, n * q * n ∉ P → CellGood P n f ν q)
include cover

theorem cellExtendFun_mul_mem (D : CellData P n f ν) (g : G) {p : G} (hp : p ∈ P) :
    cellExtendFun P n f ν (g * p) = cellExtendFun P n f ν g * f p := by
  by_cases hg : g ∈ P
  · rw [D.cellExtendFun_of_mem hg, D.cellExtendFun_of_mem (P.mul_mem hg hp), D.map_mul _ hg _ hp]
  · obtain ⟨p₁, hp₁, q₁, hq₁, rfl⟩ := cover g hg
    rw [D.cellExtendFun_cell hp₁ hq₁, mul_assoc, D.cellExtendFun_cell hp₁ (P.mul_mem hq₁ hp),
      D.map_mul _ hq₁ _ hp]
    group

include good

theorem cellExtendFun_mul_n (D : CellData P n f ν) (g : G) :
    cellExtendFun P n f ν (g * n) = cellExtendFun P n f ν g * ν := by
  by_cases hg : g ∈ P
  · have : g * n = g * n * 1 := by group
    rw [this, D.cellExtendFun_cell hg P.one_mem, D.map_one, D.cellExtendFun_of_mem hg, mul_one]
  · obtain ⟨p, hp, q, hq, rfl⟩ := cover g hg
    rw [D.cellExtendFun_cell hp hq]
    by_cases hqn : n * q * n ∈ P
    · have : p * n * q * n = p * (n * q * n) := by group
      rw [this, D.cellExtendFun_of_mem (P.mul_mem hp hqn), D.map_mul _ hp _ hqn,
        D.map_n_mul_n hq hqn]
      group
    · obtain ⟨p₁, hp₁, p₂, hp₂, heq, hval⟩ := good q hq hqn
      have : p * n * q * n = (p * p₁) * n * p₂ := by
        rw [show p * n * q * n = p * (n * q * n) by group, heq]; group
      rw [this, D.cellExtendFun_cell (P.mul_mem hp hp₁) hp₂, D.map_mul _ hp _ hp₁]
      calc f p * f p₁ * ν * f p₂ = f p * (f p₁ * ν * f p₂) := by group
        _ = f p * (ν * f q * ν) := by rw [hval]
        _ = _ := by group

theorem cellExtendFun_mul (D : CellData P n f ν) (g g' : G) :
    cellExtendFun P n f ν (g * g') = cellExtendFun P n f ν g * cellExtendFun P n f ν g' := by
  by_cases hg' : g' ∈ P
  · rw [D.cellExtendFun_mul_mem cover g hg', D.cellExtendFun_of_mem hg']
  · obtain ⟨p, hp, q, hq, rfl⟩ := cover g' hg'
    rw [show g * (p * n * q) = g * p * n * q by group, D.cellExtendFun_mul_mem cover _ hq,
      D.cellExtendFun_mul_n cover good, D.cellExtendFun_mul_mem cover _ hp,
      D.cellExtendFun_cell hp hq]
    group

/-- The homomorphism extending `f` across `P ∪ P n P`. -/
def cellExtend (D : CellData P n f ν) : G →* H where
  toFun := cellExtendFun P n f ν
  map_one' := by rw [D.cellExtendFun_of_mem P.one_mem, D.map_one]
  map_mul' := D.cellExtendFun_mul cover good

theorem cellExtend_of_mem (D : CellData P n f ν) {g : G} (hg : g ∈ P) :
    D.cellExtend cover good g = f g :=
  D.cellExtendFun_of_mem hg

theorem cellExtend_n (D : CellData P n f ν) : D.cellExtend cover good n = ν := by
  change cellExtendFun P n f ν n = ν
  have h := D.cellExtendFun_cell P.one_mem P.one_mem
  rw [one_mul, mul_one, D.map_one, one_mul, mul_one] at h
  exact h

end CellData

end CellExtension


/-- Binary special linear group. -/
local notation "SL2" A => Matrix.SpecialLinearGroup (Fin 2) A

/-- Ternary special linear group. -/
local notation "SL3" A => Matrix.SpecialLinearGroup (Fin 3) A

open BinaryPresentation Matrix.SpecialLinearGroup

section BinaryIdentities

variable {F : Type u} [Field F]

theorem coe_diag (u : Fˣ) :
    ((BinaryPresentation.diag u : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![(u : F), 0; 0, (u : F)⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Root.contractingMatrix]

theorem coe_upper (t : F) :
    ((upper t : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvection_coe]

theorem coe_lower (t : F) :
    ((lower t : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; t, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvection_coe]

theorem coe_weylMatrix :
    ((BinaryUpper.weylMatrix : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := rfl

theorem upper_add (s t : F) : upper (s + t) = upper s * upper t := by
  ext i j
  rw [coe_mul, coe_upper, coe_upper, coe_upper]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, add_comm]

theorem diag_mul_upper (u : Fˣ) (s : F) :
    BinaryPresentation.diag u * upper s = upper ((u : F) ^ 2 * s) * BinaryPresentation.diag u := by
  ext i j
  rw [coe_mul, coe_mul, coe_upper, coe_upper, coe_diag]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
  field_simp

theorem diag_mul_weylMatrix (u : Fˣ) :
    BinaryPresentation.diag u * BinaryUpper.weylMatrix = BinaryUpper.weylMatrix * BinaryPresentation.diag u⁻¹ := by
  ext i j
  rw [coe_mul, coe_mul, coe_diag, coe_diag, coe_weylMatrix]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

theorem weylMatrix_mul_weylMatrix :
    (BinaryUpper.weylMatrix : SL2 F) * BinaryUpper.weylMatrix = BinaryPresentation.diag (-1) := by
  ext i j
  rw [coe_mul, coe_diag, coe_weylMatrix]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

theorem weylMatrix_mul_lower (t : F) :
    BinaryUpper.weylMatrix * lower t = upper (-t) * BinaryUpper.weylMatrix := by
  ext i j
  rw [coe_mul, coe_mul, coe_lower, coe_upper, coe_weylMatrix]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

/-- An upper triangular binary matrix is a product of an upper unipotent and a diagonal. -/
theorem eq_upper_mul_diag (g : SL2 F) (hg : g 1 0 = 0) :
    g = upper (g 0 0 * g 0 1) * BinaryPresentation.diag (Units.mk0 (g 0 0) (by
      intro h0
      have h := det_two g
      rw [h0, hg] at h
      simp at h)) := by
  have hdet := det_two g
  rw [hg, mul_zero, sub_zero] at hdet
  have h0 : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  ext i j
  rw [coe_mul, coe_upper, coe_diag]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, hg]
  · field_simp
  · field_simp
    linear_combination hdet

/-- The Bruhat decomposition of `w * upper t * w`. -/
theorem weylMatrix_mul_upper_mul_weylMatrix {t : F} (ht : t ≠ 0) :
    BinaryUpper.weylMatrix * upper t * BinaryUpper.weylMatrix =
      upper (-t⁻¹) * BinaryUpper.weylMatrix * (upper (-t) * BinaryPresentation.diag (Units.mk0 t ht)) := by
  ext i j
  rw [coe_mul, coe_mul, coe_mul, coe_mul, coe_mul, coe_upper, coe_upper, coe_upper, coe_diag,
    coe_weylMatrix]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, ht]

end BinaryIdentities

section TernaryCells

variable {F : Type u} [Field F]

theorem det_three (g : SL3 F) :
    g 0 0 * g 1 1 * g 2 2 - g 0 0 * g 1 2 * g 2 1 - g 0 1 * g 1 0 * g 2 2 +
      g 0 1 * g 1 2 * g 2 0 + g 0 2 * g 1 0 * g 2 1 - g 0 2 * g 1 1 * g 2 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_three] at h
  exact h

/-- The stabilizer in ternary `SL` of the line through the first basis vector. -/
def parabolic : Subgroup (SL3 F) where
  carrier := {g | g 1 0 = 0 ∧ g 2 0 = 0}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    simp [coe_mul, mul_apply, Fin.sum_univ_three, hg1, hg2, hh1, hh2]
  one_mem' := by simp
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    simp [coe_inv, adjugate_fin_three, hg1, hg2]

theorem mem_parabolic {g : SL3 F} : g ∈ parabolic ↔ g 1 0 = 0 ∧ g 2 0 = 0 := Iff.rfl

theorem parabolic_det {g : SL3 F} (hg : g ∈ parabolic) :
    g 0 0 * (g 1 1 * g 2 2 - g 1 2 * g 2 1) = 1 := by
  have h := det_three g
  rw [hg.1, hg.2] at h
  linear_combination h

theorem parabolic_apply_ne_zero {g : SL3 F} (hg : g ∈ parabolic) : g 0 0 ≠ 0 :=
  left_ne_zero_of_mul_eq_one (parabolic_det hg)

theorem right_mem_parabolic (X : SL2 F) : right X ∈ parabolic := by
  constructor <;> simp [rightMatrix]

theorem left_mem_parabolic {Y : SL2 F} (hY : Y 1 0 = 0) : left Y ∈ parabolic := by
  constructor <;> simp [leftMatrix, hY]

/-- The left block copy of the binary Weyl matrix. -/
def cellWeyl : SL3 F := left BinaryUpper.weylMatrix

/-- The right block copy of the binary Weyl matrix. -/
def rightWeyl : SL3 F := right BinaryUpper.weylMatrix

/-- The elementary matrix with entry `t` at position `(0, 2)`. -/
def corner (t : F) : SL3 F := ⟨!![1, 0, t; 0, 1, 0; 0, 0, 1], by simp [det_fin_three]⟩

theorem coe_cellWeyl :
    ((cellWeyl : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cellWeyl, leftMatrix, coe_weylMatrix]

theorem coe_cellWeyl_inv :
    ((cellWeyl⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  rw [coe_inv, coe_cellWeyl, adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_rightWeyl :
    ((rightWeyl : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rightWeyl, rightMatrix, coe_weylMatrix]

theorem coe_corner (t : F) :
    ((corner t : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, t; 0, 1, 0; 0, 0, 1] := rfl

theorem corner_mem_parabolic (t : F) : corner t ∈ parabolic := by
  constructor <;> simp [coe_corner]

theorem cellWeyl_not_mem : (cellWeyl : SL3 F) ∉ parabolic := by
  intro h
  have := h.1
  simp [coe_cellWeyl] at this

theorem cellWeyl_mul_cellWeyl :
    (cellWeyl : SL3 F) * cellWeyl = left (BinaryPresentation.diag (-1)) := by
  rw [cellWeyl, ← map_mul, weylMatrix_mul_weylMatrix]

theorem cellWeyl_mul_cellWeyl_mem : (cellWeyl : SL3 F) * cellWeyl ∈ parabolic := by
  rw [cellWeyl_mul_cellWeyl]
  exact left_mem_parabolic (by simp [coe_diag])

/-- Two ternary matrices agreeing on a column `j` differ by a matrix with `j`-th column `e_j`. -/
theorem inv_mul_apply_of_col {A B : SL3 F} {j : Fin 3} (h : ∀ k, A k j = B k j) (i : Fin 3) :
    (A⁻¹ * B) i j = if i = j then 1 else 0 := by
  have : (A⁻¹ * B) i j = (A⁻¹ * A) i j := by
    simp only [coe_mul, mul_apply, h]
  rw [this, inv_mul_cancel, coe_one, one_apply]

theorem conj_apply_one_zero (μ : SL3 F) : (cellWeyl * μ * cellWeyl⁻¹ : SL3 F) 1 0 = -μ 0 1 := by
  simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_cellWeyl, coe_cellWeyl_inv]
  simp

theorem conj_apply_two_zero (μ : SL3 F) : (cellWeyl * μ * cellWeyl⁻¹ : SL3 F) 2 0 = -μ 2 1 := by
  simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_cellWeyl, coe_cellWeyl_inv]
  simp

theorem conj_mem_parabolic_iff (μ : SL3 F) :
    cellWeyl * μ * cellWeyl⁻¹ ∈ parabolic ↔ μ 0 1 = 0 ∧ μ 2 1 = 0 := by
  rw [mem_parabolic, conj_apply_one_zero, conj_apply_two_zero, neg_eq_zero, neg_eq_zero]

theorem sandwich_mem_parabolic_iff (q : SL3 F) :
    cellWeyl * q * cellWeyl ∈ parabolic ↔ q 0 1 = 0 ∧ q 2 1 = 0 := by
  rw [mem_parabolic]
  simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_cellWeyl]
  simp

/-- Ternary `SL` is the union of `P` and `P n P`. -/
theorem cover (g : SL3 F) (hg : g ∉ parabolic) :
    ∃ p ∈ parabolic, ∃ q ∈ parabolic, g = p * cellWeyl * q := by
  have key : ∀ p : SL3 F, p ∈ parabolic → (∀ k, (p * cellWeyl : SL3 F) k 0 = g k 0) →
      ∃ p ∈ parabolic, ∃ q ∈ parabolic, g = p * cellWeyl * q := by
    intro p hp hcol
    refine ⟨p, hp, (p * cellWeyl)⁻¹ * g, ⟨?_, ?_⟩, by group⟩
    · rw [inv_mul_apply_of_col hcol]; simp
    · rw [inv_mul_apply_of_col hcol]; simp
  by_cases h1 : g 1 0 = 0
  · have h2 : g 2 0 ≠ 0 := fun h2 => hg ⟨h1, h2⟩
    refine key ⟨!![1, g 0 0, 0; 0, 0, -(g 2 0)⁻¹; 0, g 2 0, 0], by simp [det_fin_three, h2]⟩
      ⟨by simp, by simp⟩ ?_
    intro k
    fin_cases k <;> simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_cellWeyl] <;> simp [h1]
  · refine key ⟨!![1, g 0 0, 0; 0, g 1 0, 0; 0, g 2 0, (g 1 0)⁻¹], by simp [det_fin_three, h1]⟩
      ⟨by simp, by simp⟩ ?_
    intro k
    fin_cases k <;> simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_cellWeyl] <;> simp

theorem cellWeyl_conj_corner (c : F) :
    cellWeyl * corner c * cellWeyl⁻¹ = right (upper c) := by
  ext i j
  simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_cellWeyl, coe_cellWeyl_inv, coe_corner,
    coe_right]
  fin_cases i <;> fin_cases j <;> simp [rightMatrix, coe_upper]

theorem cellWeyl_conj_right_upper (d : F) :
    cellWeyl * right (upper d) * cellWeyl⁻¹ = corner (-d) := by
  ext i j
  simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_cellWeyl, coe_cellWeyl_inv, coe_corner,
    coe_right]
  fin_cases i <;> fin_cases j <;> simp [rightMatrix, coe_upper]

theorem cellWeyl_conj_left_diag (α : Fˣ) :
    cellWeyl * left (BinaryPresentation.diag α) * cellWeyl⁻¹ = left (BinaryPresentation.diag α⁻¹) := by
  ext i j
  simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_cellWeyl, coe_cellWeyl_inv, coe_left]
  fin_cases i <;> fin_cases j <;> simp [leftMatrix, coe_diag]

theorem cellWeyl_conj_right_diag (w : Fˣ) :
    cellWeyl * right (BinaryPresentation.diag w) * cellWeyl⁻¹ =
      left (BinaryPresentation.diag w) * right (BinaryPresentation.diag w) := by
  ext i j
  simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_cellWeyl, coe_cellWeyl_inv, coe_left,
    coe_right]
  fin_cases i <;> fin_cases j <;> simp [leftMatrix, rightMatrix, coe_diag]

theorem cellWeyl_braid : (cellWeyl : SL3 F) * rightWeyl * cellWeyl = rightWeyl * cellWeyl * rightWeyl := by
  ext i j
  simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_cellWeyl, coe_rightWeyl]
  fin_cases i <;> fin_cases j <;> simp

theorem cellWeyl_sandwich_left_upper {t : F} (ht : t ≠ 0) :
    cellWeyl * left (upper t) * cellWeyl = left (upper (-t⁻¹)) * cellWeyl *
      left (upper (-t) * BinaryPresentation.diag (Units.mk0 t ht)) := by
  rw [cellWeyl, ← map_mul, ← map_mul, ← map_mul, ← map_mul, weylMatrix_mul_upper_mul_weylMatrix ht]

/-- An element of `P ∩ n⁻¹ P n` factors through the four families of generators. -/
theorem exists_levi_decomposition {μ : SL3 F} (hμ : μ ∈ parabolic) (h01 : μ 0 1 = 0)
    (h21 : μ 2 1 = 0) : ∃ (c d : F) (α w : Fˣ), μ = corner c * right (upper d) *
      left (BinaryPresentation.diag α) * right (BinaryPresentation.diag w) := by
  have hdet := parabolic_det hμ
  rw [h21, mul_zero, sub_zero, ← mul_assoc] at hdet
  have h0011 : μ 0 0 * μ 1 1 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have h00 : μ 0 0 ≠ 0 := left_ne_zero_of_mul h0011
  have h11 : μ 1 1 ≠ 0 := right_ne_zero_of_mul h0011
  have h22 : μ 2 2 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  have hinv : (μ 0 0 * μ 1 1)⁻¹ = μ 2 2 := inv_eq_of_mul_eq_one_right hdet
  refine ⟨μ 0 2 / μ 2 2, μ 1 2 / μ 2 2, Units.mk0 _ h00, Units.mk0 _ (mul_ne_zero h00 h11), ?_⟩
  ext i j
  simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_corner, coe_left, coe_right]
  fin_cases i <;> fin_cases j <;>
    simp [leftMatrix, rightMatrix, coe_diag, coe_upper, hμ.1, hμ.2, h01, h21, hinv]
  · field_simp
  · field_simp
  · field_simp

end TernaryCells

section TernaryCellData

variable {F : Type u} [Field F] {H : Type v} [Group H]

theorem diag_apply_one_zero (u : Fˣ) : (BinaryPresentation.diag u : SL2 F) 1 0 = 0 := by
  simp [coe_diag]

theorem upper_apply_one_zero (t : F) : (upper t : SL2 F) 1 0 = 0 := by
  simp [coe_upper]

/-- Compatibility with conjugation by `n` on `P ∩ n⁻¹ P n` follows from four generator
families. -/
theorem conj_of_generators {f : (SL3 F) → H} {ν : H}
    (hmul : ∀ p ∈ parabolic, ∀ q ∈ parabolic, f (p * q) = f p * f q)
    (hc : ∀ c, f (right (upper c)) = ν * f (corner c) * ν⁻¹)
    (hr : ∀ d, f (corner (-d)) = ν * f (right (upper d)) * ν⁻¹)
    (hl : ∀ α : Fˣ, f (left (BinaryPresentation.diag α⁻¹)) =
      ν * f (left (BinaryPresentation.diag α)) * ν⁻¹)
    (hd : ∀ w : Fˣ, f (left (BinaryPresentation.diag w) * right (BinaryPresentation.diag w)) =
      ν * f (right (BinaryPresentation.diag w)) * ν⁻¹) :
    ∀ μ ∈ parabolic, cellWeyl * μ * cellWeyl⁻¹ ∈ parabolic →
      f (cellWeyl * μ * cellWeyl⁻¹) = ν * f μ * ν⁻¹ := by
  intro μ hμ hμc
  obtain ⟨h01, h21⟩ := (conj_mem_parabolic_iff μ).mp hμc
  obtain ⟨c, d, α, w, rfl⟩ := exists_levi_decomposition hμ h01 h21
  have m1 := corner_mem_parabolic c
  have m2 := right_mem_parabolic (upper d)
  have m3 := left_mem_parabolic (diag_apply_one_zero α)
  have m4 := right_mem_parabolic (BinaryPresentation.diag w)
  have e : cellWeyl * (corner c * right (upper d) * left (BinaryPresentation.diag α) *
      right (BinaryPresentation.diag w)) * cellWeyl⁻¹ =
      (cellWeyl * corner c * cellWeyl⁻¹) * (cellWeyl * right (upper d) * cellWeyl⁻¹) *
      (cellWeyl * left (BinaryPresentation.diag α) * cellWeyl⁻¹) *
      (cellWeyl * right (BinaryPresentation.diag w) * cellWeyl⁻¹) := by group
  rw [e, cellWeyl_conj_corner, cellWeyl_conj_right_upper, cellWeyl_conj_left_diag,
    cellWeyl_conj_right_diag]
  have n1 := right_mem_parabolic (upper c)
  have n2 := corner_mem_parabolic (-d)
  have n3 := left_mem_parabolic (diag_apply_one_zero α⁻¹)
  have n4 := mul_mem (left_mem_parabolic (diag_apply_one_zero w))
    (right_mem_parabolic (BinaryPresentation.diag w))
  rw [hmul _ (mul_mem (mul_mem n1 n2) n3) _ n4, hmul _ (mul_mem n1 n2) _ n3, hmul _ n1 _ n2,
    hmul _ (mul_mem (mul_mem m1 m2) m3) _ m4, hmul _ (mul_mem m1 m2) _ m3, hmul _ m1 _ m2,
    hc, hr, hl, hd]
  group

/-- The compatibility condition of the cell extension reduces to two double coset
representatives. -/
theorem cellGood_of_reps {f : (SL3 F) → H} {ν : H} (D : CellData parabolic cellWeyl f ν)
    (hn : CellGood parabolic cellWeyl f ν rightWeyl)
    (hu : ∀ t : F, t ≠ 0 → CellGood parabolic cellWeyl f ν (left (upper t))) :
    ∀ q ∈ parabolic, cellWeyl * q * cellWeyl ∉ parabolic → CellGood parabolic cellWeyl f ν q := by
  intro q hq hqn
  rw [sandwich_mem_parabolic_iff] at hqn
  have hdet := parabolic_det hq
  have h00 := parabolic_apply_ne_zero hq
  have key : ∀ μ r : SL3 F, μ ∈ parabolic → μ 0 1 = 0 → μ 2 1 = 0 →
      CellGood parabolic cellWeyl f ν r → r ∈ parabolic →
      (∀ k, (μ * r : SL3 F) k 0 = q k 0) → (∀ k, (μ * r : SL3 F) k 1 = q k 1) →
      CellGood parabolic cellWeyl f ν q := by
    intro μ r hμ h01 h21 hr hrP hc0 hc1
    have hμ' : (μ * r)⁻¹ * q ∈ parabolic :=
      ⟨by rw [inv_mul_apply_of_col hc0]; simp, by rw [inv_mul_apply_of_col hc0]; simp⟩
    have hμ'c : cellWeyl * ((μ * r)⁻¹ * q) * cellWeyl⁻¹ ∈ parabolic := by
      rw [conj_mem_parabolic_iff]
      exact ⟨by rw [inv_mul_apply_of_col hc1]; simp, by rw [inv_mul_apply_of_col hc1]; simp⟩
    have := D.cellGood_mul hμ ((conj_mem_parabolic_iff μ).mpr ⟨h01, h21⟩) hrP hμ' hμ'c hr
    rwa [show μ * r * ((μ * r)⁻¹ * q) = q by group] at this
  by_cases h21 : q 2 1 = 0
  · have h01 : q 0 1 ≠ 0 := fun h => hqn ⟨h, h21⟩
    rw [h21, mul_zero, sub_zero, ← mul_assoc] at hdet
    have h0011 : q 0 0 * q 1 1 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have h11 : q 1 1 ≠ 0 := right_ne_zero_of_mul h0011
    refine key ⟨!![q 0 0, 0, 0; 0, q 1 1, 0; 0, 0, (q 0 0 * q 1 1)⁻¹],
      by simp [det_fin_three]; field_simp⟩ (left (upper (q 0 1 / q 0 0))) ⟨by simp, by simp⟩
      (by simp) (by simp) (hu _ (div_ne_zero h01 h00))
      (left_mem_parabolic (upper_apply_one_zero _)) ?_ ?_
    · intro k
      fin_cases k <;> simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_left] <;>
        simp [leftMatrix, coe_upper, hq.1, hq.2]
    · intro k
      fin_cases k <;> simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_left] <;>
        simp [leftMatrix, coe_upper, h21]
      field_simp
  · refine key ⟨!![q 0 0, 0, q 0 1; 0, (q 0 0 * q 2 1)⁻¹, q 1 1; 0, 0, q 2 1],
      by simp [det_fin_three]; field_simp⟩ rightWeyl ⟨by simp, by simp⟩ (by simp) (by simp) hn
      (right_mem_parabolic _) ?_ ?_
    · intro k
      fin_cases k <;> simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_rightWeyl] <;>
        simp [hq.1, hq.2]
    · intro k
      fin_cases k <;> simp only [coe_mul, mul_apply, Fin.sum_univ_three, coe_rightWeyl] <;> simp

end TernaryCellData

section TernaryRelationsSection

variable {F : Type u} [Field F] {H : Type v} [Group H]

theorem upper_zero : (upper 0 : SL2 F) = 1 := by
  ext i j
  rw [coe_upper]
  fin_cases i <;> fin_cases j <;> simp

theorem binaryDiag_one : (BinaryPresentation.diag 1 : SL2 F) = 1 :=
  map_one (Root.contractingMatrixHom (A := F) (by decide : (0 : Fin 2) ≠ 1))

theorem binaryDiag_mul (u w : Fˣ) :
    (BinaryPresentation.diag (u * w) : SL2 F) =
      BinaryPresentation.diag u * BinaryPresentation.diag w :=
  map_mul (Root.contractingMatrixHom (A := F) (by decide : (0 : Fin 2) ≠ 1)) u w

theorem binaryDiag_inv (u : Fˣ) :
    (BinaryPresentation.diag u⁻¹ : SL2 F) = (BinaryPresentation.diag u)⁻¹ :=
  map_inv (Root.contractingMatrixHom (A := F) (by decide : (0 : Fin 2) ≠ 1)) u

theorem diag_conj_upper (u : Fˣ) (s : F) :
    BinaryPresentation.diag u * upper s * (BinaryPresentation.diag u)⁻¹ = upper ((u : F) ^ 2 * s) := by
  rw [diag_mul_upper, mul_inv_cancel_right]

theorem weylMatrix_conj_diag (u : Fˣ) :
    BinaryUpper.weylMatrix * BinaryPresentation.diag u * BinaryUpper.weylMatrix⁻¹ =
      (BinaryPresentation.diag u⁻¹ : SL2 F) := by
  have e := diag_mul_weylMatrix (F := F) u⁻¹
  rw [inv_inv] at e
  rw [← e, mul_inv_cancel_right]

theorem weylMatrix_inv_conj_upper (t : F) :
    (BinaryUpper.weylMatrix : SL2 F)⁻¹ * upper (-t) * BinaryUpper.weylMatrix = lower t := by
  rw [mul_assoc, ← weylMatrix_mul_lower, inv_mul_cancel_left]

/-- The point `t` of the root group of `e₀ - e₂`, obtained from the upper root group of the
second homomorphism by conjugating with the Weyl element of the first. -/
def cornerPoint (φ₁ φ₂ : (SL2 F) →* H) (t : F) : H :=
  φ₁ BinaryUpper.weylMatrix * φ₂ (upper (-t)) * (φ₁ BinaryUpper.weylMatrix)⁻¹

/-- The relations between two homomorphisms `φ₁ φ₂ : SL₂(F) →* H` satisfied by the two block
embeddings of `SL₂(F)` into `SL₃(F)`, sufficient for both to factor through one homomorphism
out of `SL₃(F)` (`TernaryRelations.exists_lift`). Here `x₃ = cornerPoint φ₁ φ₂`. -/
structure TernaryRelations (φ₁ φ₂ : (SL2 F) →* H) : Prop where
  torus_upper : ∀ (u : Fˣ) (t : F), φ₁ (BinaryPresentation.diag u) * φ₂ (upper t) *
    (φ₁ (BinaryPresentation.diag u))⁻¹ = φ₂ (upper ((u : F)⁻¹ * t))
  torus_lower : ∀ (u : Fˣ) (t : F), φ₁ (BinaryPresentation.diag u) * φ₂ (lower t) *
    (φ₁ (BinaryPresentation.diag u))⁻¹ = φ₂ (lower ((u : F) * t))
  weyl_torus : ∀ u : Fˣ, φ₁ BinaryUpper.weylMatrix * φ₂ (BinaryPresentation.diag u) *
    (φ₁ BinaryUpper.weylMatrix)⁻¹ = φ₁ (BinaryPresentation.diag u) * φ₂ (BinaryPresentation.diag u)
  commutator : ∀ c s : F, φ₂ (upper c) * φ₁ (upper s) * (φ₂ (upper c))⁻¹ =
    φ₁ (upper s) * cornerPoint φ₁ φ₂ (-(c * s))
  commute_upper_corner : ∀ c t : F, Commute (φ₂ (upper c)) (cornerPoint φ₁ φ₂ t)
  commute_lower_upper : ∀ c s : F, Commute (φ₂ (lower c)) (φ₁ (upper s))
  lower_corner : ∀ c t : F, φ₂ (lower c) * cornerPoint φ₁ φ₂ t * (φ₂ (lower c))⁻¹ =
    cornerPoint φ₁ φ₂ t * φ₁ (upper (-(c * t)))
  commute_corner : ∀ s t : F, Commute (φ₁ (upper s)) (cornerPoint φ₁ φ₂ t)
  braid : φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix * φ₁ BinaryUpper.weylMatrix =
    φ₂ BinaryUpper.weylMatrix * φ₁ BinaryUpper.weylMatrix * φ₂ BinaryUpper.weylMatrix

theorem cornerPoint_add (φ₁ φ₂ : (SL2 F) →* H) (s t : F) :
    cornerPoint φ₁ φ₂ (s + t) = cornerPoint φ₁ φ₂ s * cornerPoint φ₁ φ₂ t := by
  simp only [cornerPoint, neg_add, upper_add, map_mul]
  group

theorem cornerPoint_zero (φ₁ φ₂ : (SL2 F) →* H) : cornerPoint φ₁ φ₂ 0 = 1 := by
  simp [cornerPoint]

/-- The point of the unipotent radical of the parabolic with coordinates `s, t`. -/
def radicalPoint (φ₁ φ₂ : (SL2 F) →* H) (s t : F) : H :=
  φ₁ (upper s) * cornerPoint φ₁ φ₂ t

theorem radicalPoint_zero (φ₁ φ₂ : (SL2 F) →* H) : radicalPoint φ₁ φ₂ 0 0 = 1 := by
  rw [radicalPoint, cornerPoint_zero, upper_zero, map_one, one_mul]

/-- Conjugation of binary `SL` by `diag(c, 1)`. -/
def conjDiag (c : Fˣ) : (SL2 F) →* (SL2 F) where
  toFun X := ⟨!![X 0 0, c * X 0 1; (c : F)⁻¹ * X 1 0, X 1 1], by
    have h := det_two X
    have hc : (c : F) * (c : F)⁻¹ = 1 := mul_inv_cancel₀ c.ne_zero
    rw [det_fin_two_of]
    linear_combination h - X 0 1 * X 1 0 * hc⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' X Y := by
    have hc : (c : F) ≠ 0 := c.ne_zero
    ext i j
    simp only [coe_mul]
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two] <;> field_simp

theorem coe_conjDiag (c : Fˣ) (X : SL2 F) :
    ((conjDiag c X : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      !![X 0 0, c * X 0 1; (c : F)⁻¹ * X 1 0, X 1 1] := rfl

theorem conjDiag_upper (c : Fˣ) (t : F) : conjDiag c (upper t) = upper ((c : F) * t) := by
  ext i j
  rw [coe_conjDiag, coe_upper, coe_upper]
  fin_cases i <;> fin_cases j <;> simp

theorem conjDiag_lower (c : Fˣ) (t : F) : conjDiag c (lower t) = lower ((c : F)⁻¹ * t) := by
  ext i j
  rw [coe_conjDiag, coe_lower, coe_lower]
  fin_cases i <;> fin_cases j <;> simp

namespace TernaryRelations

variable {φ₁ φ₂ : (SL2 F) →* H}

theorem radicalPoint_add (R : TernaryRelations φ₁ φ₂) (s t s' t' : F) :
    radicalPoint φ₁ φ₂ (s + s') (t + t') = radicalPoint φ₁ φ₂ s t * radicalPoint φ₁ φ₂ s' t' := by
  simp only [radicalPoint]
  calc φ₁ (upper (s + s')) * cornerPoint φ₁ φ₂ (t + t') =
        φ₁ (upper s) * (φ₁ (upper s') * cornerPoint φ₁ φ₂ t) * cornerPoint φ₁ φ₂ t' := by
          rw [upper_add, map_mul, cornerPoint_add]; group
    _ = φ₁ (upper s) * (cornerPoint φ₁ φ₂ t * φ₁ (upper s')) * cornerPoint φ₁ φ₂ t' := by
          rw [(R.commute_corner s' t).eq]
    _ = _ := by group

theorem torus_conj_cornerPoint (R : TernaryRelations φ₁ φ₂) (c : Fˣ) (t : F) :
    φ₁ (BinaryPresentation.diag c) * cornerPoint φ₁ φ₂ t * (φ₁ (BinaryPresentation.diag c))⁻¹ =
      cornerPoint φ₁ φ₂ ((c : F) * t) := by
  have hw : φ₁ (BinaryPresentation.diag c) * φ₁ BinaryUpper.weylMatrix =
      φ₁ BinaryUpper.weylMatrix * φ₁ (BinaryPresentation.diag c⁻¹) := by
    rw [← map_mul, ← map_mul, diag_mul_weylMatrix]
  have ht := R.torus_upper c⁻¹ (-t)
  rw [Units.val_inv_eq_inv_val, inv_inv] at ht
  calc φ₁ (BinaryPresentation.diag c) * cornerPoint φ₁ φ₂ t * (φ₁ (BinaryPresentation.diag c))⁻¹
      = (φ₁ (BinaryPresentation.diag c) * φ₁ BinaryUpper.weylMatrix) * φ₂ (upper (-t)) *
          (φ₁ (BinaryPresentation.diag c) * φ₁ BinaryUpper.weylMatrix)⁻¹ := by
        simp only [cornerPoint]; group
    _ = φ₁ BinaryUpper.weylMatrix * (φ₁ (BinaryPresentation.diag c⁻¹) * φ₂ (upper (-t)) *
          (φ₁ (BinaryPresentation.diag c⁻¹))⁻¹) * (φ₁ BinaryUpper.weylMatrix)⁻¹ := by
        rw [hw]; group
    _ = cornerPoint φ₁ φ₂ ((c : F) * t) := by rw [ht, cornerPoint, mul_neg]

theorem torus_conj_radicalPoint (R : TernaryRelations φ₁ φ₂) (c : Fˣ) (s t : F) :
    φ₁ (BinaryPresentation.diag c) * radicalPoint φ₁ φ₂ s t * (φ₁ (BinaryPresentation.diag c))⁻¹ =
      radicalPoint φ₁ φ₂ ((c : F) ^ 2 * s) ((c : F) * t) := by
  have h1 : φ₁ (BinaryPresentation.diag c) * φ₁ (upper s) * (φ₁ (BinaryPresentation.diag c))⁻¹ =
      φ₁ (upper ((c : F) ^ 2 * s)) := by
    rw [← map_inv, ← map_mul, ← map_mul, diag_conj_upper]
  calc φ₁ (BinaryPresentation.diag c) * radicalPoint φ₁ φ₂ s t * (φ₁ (BinaryPresentation.diag c))⁻¹
      = (φ₁ (BinaryPresentation.diag c) * φ₁ (upper s) * (φ₁ (BinaryPresentation.diag c))⁻¹) *
          (φ₁ (BinaryPresentation.diag c) * cornerPoint φ₁ φ₂ t *
            (φ₁ (BinaryPresentation.diag c))⁻¹) := by
        simp only [radicalPoint]; group
    _ = _ := by rw [h1, R.torus_conj_cornerPoint, radicalPoint]

theorem right_conj_radicalPoint_upper (R : TernaryRelations φ₁ φ₂) (c s t : F) :
    φ₂ (upper c) * radicalPoint φ₁ φ₂ s t * (φ₂ (upper c))⁻¹ =
      radicalPoint φ₁ φ₂ ((upper c : SL2 F) 1 1 * s - (upper c : SL2 F) 1 0 * t)
        ((upper c : SL2 F) 0 0 * t - (upper c : SL2 F) 0 1 * s) := by
  have h00 : (upper c : SL2 F) 0 0 = 1 := by simp [coe_upper]
  have h01 : (upper c : SL2 F) 0 1 = c := by simp [coe_upper]
  have h10 : (upper c : SL2 F) 1 0 = 0 := by simp [coe_upper]
  have h11 : (upper c : SL2 F) 1 1 = 1 := by simp [coe_upper]
  rw [h00, h01, h10, h11, show (1 : F) * s - 0 * t = s by ring,
    show (1 : F) * t - c * s = -(c * s) + t by ring]
  calc φ₂ (upper c) * radicalPoint φ₁ φ₂ s t * (φ₂ (upper c))⁻¹ =
        (φ₂ (upper c) * φ₁ (upper s) * (φ₂ (upper c))⁻¹) *
          (φ₂ (upper c) * cornerPoint φ₁ φ₂ t * (φ₂ (upper c))⁻¹) := by
        simp only [radicalPoint]; group
    _ = φ₁ (upper s) * (cornerPoint φ₁ φ₂ (-(c * s)) * cornerPoint φ₁ φ₂ t) := by
        rw [R.commutator, (R.commute_upper_corner c t).eq, mul_inv_cancel_right, mul_assoc]
    _ = _ := by rw [radicalPoint, cornerPoint_add]

theorem right_conj_radicalPoint_lower (R : TernaryRelations φ₁ φ₂) (c s t : F) :
    φ₂ (lower c) * radicalPoint φ₁ φ₂ s t * (φ₂ (lower c))⁻¹ =
      radicalPoint φ₁ φ₂ ((lower c : SL2 F) 1 1 * s - (lower c : SL2 F) 1 0 * t)
        ((lower c : SL2 F) 0 0 * t - (lower c : SL2 F) 0 1 * s) := by
  have h00 : (lower c : SL2 F) 0 0 = 1 := by simp [coe_lower]
  have h01 : (lower c : SL2 F) 0 1 = 0 := by simp [coe_lower]
  have h10 : (lower c : SL2 F) 1 0 = c := by simp [coe_lower]
  have h11 : (lower c : SL2 F) 1 1 = 1 := by simp [coe_lower]
  rw [h00, h01, h10, h11, show (1 : F) * s - c * t = s + -(c * t) by ring,
    show (1 : F) * t - 0 * s = t by ring]
  calc φ₂ (lower c) * radicalPoint φ₁ φ₂ s t * (φ₂ (lower c))⁻¹ =
        (φ₂ (lower c) * φ₁ (upper s) * (φ₂ (lower c))⁻¹) *
          (φ₂ (lower c) * cornerPoint φ₁ φ₂ t * (φ₂ (lower c))⁻¹) := by
        simp only [radicalPoint]; group
    _ = φ₁ (upper s) * (cornerPoint φ₁ φ₂ t * φ₁ (upper (-(c * t)))) := by
        rw [R.lower_corner, (R.commute_lower_upper c s).eq, mul_inv_cancel_right]
    _ = φ₁ (upper s) * φ₁ (upper (-(c * t))) * cornerPoint φ₁ φ₂ t := by
        rw [← (R.commute_corner (-(c * t)) t).eq, mul_assoc]
    _ = _ := by rw [radicalPoint, upper_add, map_mul]

/-- Conjugation of the unipotent radical by the right block. -/
theorem right_conj_radicalPoint (R : TernaryRelations φ₁ φ₂) (X : SL2 F) (s t : F) :
    φ₂ X * radicalPoint φ₁ φ₂ s t * (φ₂ X)⁻¹ =
      radicalPoint φ₁ φ₂ (X 1 1 * s - X 1 0 * t) (X 0 0 * t - X 0 1 * s) := by
  induction X using Matrix.SL2.transvection_induction generalizing s t with
  | htransvec i j hij c =>
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact R.right_conj_radicalPoint_upper c s t
    · exact R.right_conj_radicalPoint_lower c s t
    · exact absurd rfl hij
  | hmul A B hA hB =>
    calc φ₂ (A * B) * radicalPoint φ₁ φ₂ s t * (φ₂ (A * B))⁻¹ =
          φ₂ A * (φ₂ B * radicalPoint φ₁ φ₂ s t * (φ₂ B)⁻¹) * (φ₂ A)⁻¹ := by
          rw [map_mul]; group
      _ = _ := by
          rw [hB, hA]
          congr 1 <;> simp only [coe_mul, mul_apply, Fin.sum_univ_two] <;> ring

/-- Conjugation of the right block by the torus of the left block. -/
theorem torus_conj_right (R : TernaryRelations φ₁ φ₂) (c : Fˣ) (X : SL2 F) :
    (φ₁ (BinaryPresentation.diag c))⁻¹ * φ₂ X * φ₁ (BinaryPresentation.diag c) =
      φ₂ (conjDiag c X) := by
  have key : (MulAut.conj (φ₁ (BinaryPresentation.diag c))⁻¹).toMonoidHom.comp φ₂ =
      φ₂.comp (conjDiag c) := by
    apply BinaryPresentation.hom_ext
    · intro t
      have h := R.torus_upper c⁻¹ t
      rw [Units.val_inv_eq_inv_val, inv_inv, binaryDiag_inv, map_inv] at h
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [h, conjDiag_upper]
    · intro t
      have h := R.torus_lower c⁻¹ t
      rw [Units.val_inv_eq_inv_val, binaryDiag_inv, map_inv] at h
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [h, conjDiag_lower]
  have := DFunLike.congr_fun key X
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
  exact this

end TernaryRelations

open Classical in
/-- The unit `g₀₀` of an element of the parabolic (and `1` outside it). -/
def parabolicUnit (g : SL3 F) : Fˣ :=
  if hg : g ∈ parabolic then Units.mk0 (g 0 0) (parabolic_apply_ne_zero hg) else 1

theorem coe_parabolicUnit {g : SL3 F} (hg : g ∈ parabolic) : (parabolicUnit g : F) = g 0 0 := by
  simp only [parabolicUnit, hg, ↓reduceDIte, Units.val_mk0]

open Classical in
/-- The binary `SL` factor of the Levi decomposition of an element of the parabolic: the
lower right block with its first row scaled by `g₀₀` (and `1` outside the parabolic). -/
def leviRight (g : SL3 F) : SL2 F :=
  if hg : g ∈ parabolic then
    ⟨!![g 0 0 * g 1 1, g 0 0 * g 1 2; g 2 1, g 2 2], by
      rw [det_fin_two_of]; linear_combination parabolic_det hg⟩
  else 1

theorem coe_leviRight {g : SL3 F} (hg : g ∈ parabolic) :
    (leviRight g : Matrix (Fin 2) (Fin 2) F) = !![g 0 0 * g 1 1, g 0 0 * g 1 2; g 2 1, g 2 2] := by
  simp only [leviRight, hg, ↓reduceDIte]

/-- The first unipotent radical coordinate of an element of the parabolic. -/
def radicalFst (g : SL3 F) : F := g 0 0 * (g 0 1 * g 2 2 - g 0 2 * g 2 1)

/-- The second unipotent radical coordinate of an element of the parabolic. -/
def radicalSnd (g : SL3 F) : F := g 0 0 * (g 0 2 * g 1 1 - g 0 1 * g 1 2)

theorem mul_apply_three (p q : SL3 F) (i j : Fin 3) :
    (p * q : SL3 F) i j = p i 0 * q 0 j + p i 1 * q 1 j + p i 2 * q 2 j := by
  simp only [coe_mul, mul_apply, Fin.sum_univ_three]

theorem parabolicUnit_mul {p q : SL3 F} (hp : p ∈ parabolic) (hq : q ∈ parabolic) :
    parabolicUnit (p * q) = parabolicUnit p * parabolicUnit q := by
  ext
  rw [Units.val_mul, coe_parabolicUnit (mul_mem hp hq), coe_parabolicUnit hp,
    coe_parabolicUnit hq, mul_apply_three, hq.1, hq.2]
  ring

theorem leviRight_mul {p q : SL3 F} (hp : p ∈ parabolic) (hq : q ∈ parabolic) :
    leviRight (p * q) = conjDiag (parabolicUnit q) (leviRight p) * leviRight q := by
  have hq0 := parabolic_apply_ne_zero hq
  ext i j
  rw [coe_mul, coe_conjDiag, coe_leviRight (mul_mem hp hq), coe_leviRight hp, coe_leviRight hq,
    coe_parabolicUnit hq]
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, mul_apply_three, hp.1, hp.2, hq.1, hq.2] <;>
    field_simp

theorem radicalFst_mul {p q : SL3 F} (hp : p ∈ parabolic) (hq : q ∈ parabolic) :
    radicalFst (p * q) = radicalFst p +
      p 0 0 ^ 2 * (radicalFst q * p 2 2 - radicalSnd q * p 2 1) := by
  have hdet := parabolic_det hq
  simp only [radicalFst, radicalSnd, mul_apply_three, hp.2, hq.1, hq.2]
  linear_combination (p 0 0 * (p 0 1 * p 2 2 - p 0 2 * p 2 1)) * hdet

theorem radicalSnd_mul {p q : SL3 F} (hp : p ∈ parabolic) (hq : q ∈ parabolic) :
    radicalSnd (p * q) = radicalSnd p +
      p 0 0 ^ 2 * (radicalSnd q * p 1 1 - radicalFst q * p 1 2) := by
  have hdet := parabolic_det hq
  simp only [radicalFst, radicalSnd, mul_apply_three, hp.1, hq.1, hq.2]
  linear_combination (p 0 0 * (p 0 2 * p 1 1 - p 0 1 * p 1 2)) * hdet

/-- The Levi factor value `h₁(g₀₀) φ₂(leviRight g)`. -/
def leviPoint (φ₁ φ₂ : (SL2 F) →* H) (g : SL3 F) : H :=
  φ₁ (BinaryPresentation.diag (parabolicUnit g)) * φ₂ (leviRight g)

/-- The map on the parabolic: radical part times Levi part. -/
def parabolicMap (φ₁ φ₂ : (SL2 F) →* H) (g : SL3 F) : H :=
  radicalPoint φ₁ φ₂ (radicalFst g) (radicalSnd g) * leviPoint φ₁ φ₂ g

namespace TernaryRelations

variable {φ₁ φ₂ : (SL2 F) →* H}

theorem leviPoint_mul (R : TernaryRelations φ₁ φ₂) {p q : SL3 F} (hp : p ∈ parabolic)
    (hq : q ∈ parabolic) : leviPoint φ₁ φ₂ (p * q) = leviPoint φ₁ φ₂ p * leviPoint φ₁ φ₂ q := by
  simp only [leviPoint]
  rw [parabolicUnit_mul hp hq, leviRight_mul hp hq, binaryDiag_mul, map_mul, map_mul,
    ← R.torus_conj_right]
  group

theorem leviPoint_conj (R : TernaryRelations φ₁ φ₂) {p : SL3 F} (hp : p ∈ parabolic) (s t : F) :
    leviPoint φ₁ φ₂ p * radicalPoint φ₁ φ₂ s t * (leviPoint φ₁ φ₂ p)⁻¹ =
      radicalPoint φ₁ φ₂ (p 0 0 ^ 2 * (s * p 2 2 - t * p 2 1))
        (p 0 0 ^ 2 * (t * p 1 1 - s * p 1 2)) := by
  calc leviPoint φ₁ φ₂ p * radicalPoint φ₁ φ₂ s t * (leviPoint φ₁ φ₂ p)⁻¹ =
        φ₁ (BinaryPresentation.diag (parabolicUnit p)) *
          (φ₂ (leviRight p) * radicalPoint φ₁ φ₂ s t * (φ₂ (leviRight p))⁻¹) *
          (φ₁ (BinaryPresentation.diag (parabolicUnit p)))⁻¹ := by
        simp only [leviPoint]; group
    _ = _ := by
        rw [R.right_conj_radicalPoint, R.torus_conj_radicalPoint, coe_parabolicUnit hp]
        simp only [coe_leviRight hp, of_apply, cons_val', cons_val_zero, cons_val_one,
          empty_val', cons_val_fin_one]
        congr 1 <;> ring

theorem parabolicMap_mul (R : TernaryRelations φ₁ φ₂) {p q : SL3 F} (hp : p ∈ parabolic)
    (hq : q ∈ parabolic) :
    parabolicMap φ₁ φ₂ (p * q) = parabolicMap φ₁ φ₂ p * parabolicMap φ₁ φ₂ q := by
  simp only [parabolicMap]
  rw [radicalFst_mul hp hq, radicalSnd_mul hp hq, R.radicalPoint_add, R.leviPoint_mul hp hq,
    ← R.leviPoint_conj hp]
  group

end TernaryRelations

theorem parabolicMap_right (φ₁ φ₂ : (SL2 F) →* H) (X : SL2 F) :
    parabolicMap φ₁ φ₂ (right X) = φ₂ X := by
  have hX := right_mem_parabolic X
  have hu : parabolicUnit (right X) = 1 := by
    ext; rw [coe_parabolicUnit hX]; simp [rightMatrix]
  have hl : leviRight (right X) = X := by
    ext i j
    rw [coe_leviRight hX]
    fin_cases i <;> fin_cases j <;> simp [rightMatrix]
  have h1 : radicalFst (right X) = 0 := by simp [radicalFst, rightMatrix]
  have h2 : radicalSnd (right X) = 0 := by simp [radicalSnd, rightMatrix]
  rw [parabolicMap, leviPoint, hu, hl, h1, h2, radicalPoint_zero, binaryDiag_one, map_one,
    one_mul, one_mul]

theorem parabolicMap_left (φ₁ φ₂ : (SL2 F) →* H) {Y : SL2 F} (hY : Y 1 0 = 0) :
    parabolicMap φ₁ φ₂ (left Y) = φ₁ Y := by
  have hYP := left_mem_parabolic hY
  have hdet := det_two Y
  rw [hY, mul_zero, sub_zero] at hdet
  have hu : parabolicUnit (left Y) = Units.mk0 (Y 0 0) (left_ne_zero_of_mul_eq_one hdet) := by
    ext; rw [coe_parabolicUnit hYP]; simp [leftMatrix]
  have hl : leviRight (left Y) = 1 := by
    ext i j
    rw [coe_leviRight hYP]
    fin_cases i <;> fin_cases j <;> simp [leftMatrix, hY, hdet]
  have h1 : radicalFst (left Y) = Y 0 0 * Y 0 1 := by simp [radicalFst, leftMatrix]
  have h2 : radicalSnd (left Y) = 0 := by simp [radicalSnd, leftMatrix]
  have e := eq_upper_mul_diag Y hY
  rw [parabolicMap, leviPoint, hu, hl, h1, h2, radicalPoint, cornerPoint_zero, mul_one, map_one,
    mul_one, ← map_mul]
  exact congrArg φ₁ e.symm

theorem parabolicMap_corner (φ₁ φ₂ : (SL2 F) →* H) (t : F) :
    parabolicMap φ₁ φ₂ (corner t) = cornerPoint φ₁ φ₂ t := by
  have hc := corner_mem_parabolic t
  have hu : parabolicUnit (corner t) = 1 := by
    ext; rw [coe_parabolicUnit hc]; simp [coe_corner]
  have hl : leviRight (corner t) = 1 := by
    ext i j
    rw [coe_leviRight hc]
    fin_cases i <;> fin_cases j <;> simp [coe_corner]
  have h1 : radicalFst (corner t) = 0 := by simp [radicalFst, coe_corner]
  have h2 : radicalSnd (corner t) = t := by simp [radicalSnd, coe_corner]
  rw [parabolicMap, leviPoint, hu, hl, h1, h2, radicalPoint, upper_zero, binaryDiag_one]
  simp only [map_one, one_mul, mul_one]

namespace TernaryRelations

variable {φ₁ φ₂ : (SL2 F) →* H}

theorem cellData (R : TernaryRelations φ₁ φ₂) :
    CellData parabolic cellWeyl (parabolicMap φ₁ φ₂) (φ₁ BinaryUpper.weylMatrix) where
  not_mem := cellWeyl_not_mem
  sq_mem := cellWeyl_mul_cellWeyl_mem
  map_mul := fun _ hp _ hq => R.parabolicMap_mul hp hq
  conj := by
    refine conj_of_generators (fun _ hp _ hq => R.parabolicMap_mul hp hq) ?_ ?_ ?_ ?_
    · intro c
      rw [parabolicMap_right, parabolicMap_corner]
      have h := R.torus_upper (-1) (-c)
      have e : ((-1 : Fˣ) : F)⁻¹ * -c = c := by simp
      rw [← weylMatrix_mul_weylMatrix, map_mul, e] at h
      rw [← h, cornerPoint]
      group
    · intro d
      rw [parabolicMap_corner, parabolicMap_right, cornerPoint, neg_neg]
    · intro α
      rw [parabolicMap_left _ _ (diag_apply_one_zero _), parabolicMap_left _ _ (diag_apply_one_zero _),
        ← map_inv, ← map_mul, ← map_mul, weylMatrix_conj_diag]
    · intro w
      rw [R.parabolicMap_mul (left_mem_parabolic (diag_apply_one_zero w)) (right_mem_parabolic _),
        parabolicMap_left _ _ (diag_apply_one_zero _), parabolicMap_right, R.weyl_torus]
  sq := by
    rw [cellWeyl_mul_cellWeyl, parabolicMap_left _ _ (diag_apply_one_zero _),
      ← weylMatrix_mul_weylMatrix, map_mul]

theorem cellGood_rightWeyl (R : TernaryRelations φ₁ φ₂) :
    CellGood parabolic cellWeyl (parabolicMap φ₁ φ₂) (φ₁ BinaryUpper.weylMatrix) rightWeyl := by
  refine ⟨rightWeyl, right_mem_parabolic _, rightWeyl, right_mem_parabolic _, cellWeyl_braid, ?_⟩
  rw [rightWeyl, parabolicMap_right]
  exact R.braid

theorem cellGood_left_upper (_R : TernaryRelations φ₁ φ₂) (t : F) (ht : t ≠ 0) :
    CellGood parabolic cellWeyl (parabolicMap φ₁ φ₂) (φ₁ BinaryUpper.weylMatrix)
      (left (upper t)) := by
  have h10 : (upper (-t) * BinaryPresentation.diag (Units.mk0 t ht) : SL2 F) 1 0 = 0 := by
    simp [coe_mul, mul_apply, Fin.sum_univ_two, coe_upper, coe_diag]
  refine ⟨left (upper (-t⁻¹)), left_mem_parabolic (upper_apply_one_zero _),
    left (upper (-t) * BinaryPresentation.diag (Units.mk0 t ht)), left_mem_parabolic h10,
    cellWeyl_sandwich_left_upper ht, ?_⟩
  rw [parabolicMap_left _ _ (upper_apply_one_zero _), parabolicMap_left _ _ (upper_apply_one_zero _),
    parabolicMap_left _ _ h10, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
    weylMatrix_mul_upper_mul_weylMatrix ht]

/-- **Lift.** Two homomorphisms `SL₂(F) →* H` satisfying the ternary relations are the
restrictions of one homomorphism `SL₃(F) →* H` to the two block embeddings. -/
theorem exists_lift (R : TernaryRelations φ₁ φ₂) :
    ∃ Φ : (SL3 F) →* H, Φ.comp left = φ₁ ∧ Φ.comp right = φ₂ := by
  let D := R.cellData
  have good := cellGood_of_reps D R.cellGood_rightWeyl R.cellGood_left_upper
  refine ⟨D.cellExtend cover good, ?_, ?_⟩
  · apply BinaryPresentation.hom_ext
    · intro t
      rw [MonoidHom.comp_apply, D.cellExtend_of_mem cover good
        (left_mem_parabolic (upper_apply_one_zero t)), parabolicMap_left _ _ (upper_apply_one_zero t)]
    · intro t
      have e : left (lower t) = cellWeyl⁻¹ * left (upper (-t)) * cellWeyl := by
        rw [cellWeyl, ← map_inv, ← map_mul, ← map_mul, weylMatrix_inv_conj_upper]
      rw [MonoidHom.comp_apply, e, map_mul, map_mul, map_inv, D.cellExtend_n cover good,
        D.cellExtend_of_mem cover good (left_mem_parabolic (upper_apply_one_zero _)),
        parabolicMap_left _ _ (upper_apply_one_zero _), ← map_inv, ← map_mul, ← map_mul,
        weylMatrix_inv_conj_upper]
  · ext X
    rw [MonoidHom.comp_apply, D.cellExtend_of_mem cover good (right_mem_parabolic X),
      parabolicMap_right]

end TernaryRelations

end TernaryRelationsSection

end Langlands.GroupScheme.SpecialLinear.TernaryPresentation
