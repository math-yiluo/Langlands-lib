import Langlands.Representation.Whittaker.Iwasawa
import Langlands.Group.GL.CartanProof

/-!
# Left cosets in a minuscule spherical double coset

For a field with a valuation and a uniformizing element `ϖ`, let `K` be the
integral subgroup of `GL_(n+1)` and `t_S` the diagonal matrix with `ϖ` in the
positions of a subset `S` and `1` elsewhere. Every left coset `x K` inside the
double coset `K t_S' K` has a unique representative `n t_S` with `|S| = |S'|`,
where `n` is the identity plus entries `c a b` in the positions `a ∈ S`, `b ∉ S`,
`a < b`, and these entries run through a fixed set of residue representatives.
-/

noncomputable section

namespace Langlands.Unramified.MinusculeCosets

open Matrix Langlands.Conductor Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa

universe uF uΓ uΛ

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀}

/-! ### Radical matrices -/

section Radical

variable {m : ℕ}

/-- The positions `(a, b)` with `a ∈ S`, `b ∉ S` and `a < b`. -/
def IsRadicalPair (S : Finset (Fin m)) (a b : Fin m) : Prop :=
  a ∈ S ∧ b ∉ S ∧ a < b

instance (S : Finset (Fin m)) (a b : Fin m) : Decidable (IsRadicalPair S a b) := by
  unfold IsRadicalPair
  infer_instance

theorem IsRadicalPair.ne {S : Finset (Fin m)} {a b : Fin m} (h : IsRadicalPair S a b) :
    a ≠ b :=
  h.2.2.ne

/-- The part of `c` supported on the radical pairs of `S`. -/
def radicalPart (S : Finset (Fin m)) (c : Fin m → Fin m → F) : Matrix (Fin m) (Fin m) F :=
  fun a b => if IsRadicalPair S a b then c a b else 0

theorem radicalPart_mul (S : Finset (Fin m)) (c d : Fin m → Fin m → F) :
    radicalPart S c * radicalPart S d = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro e _
  by_cases h1 : IsRadicalPair S a e
  · by_cases h2 : IsRadicalPair S e b
    · exact absurd h2.1 h1.2.1
    · simp [radicalPart, h2]
  · simp [radicalPart, h1]

theorem radicalPart_add (S : Finset (Fin m)) (c d : Fin m → Fin m → F) :
    radicalPart S c + radicalPart S d = radicalPart S (c + d) := by
  ext a b
  simp only [radicalPart, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

/-- The matrix `1 + radicalPart S c`. -/
def radicalMatrix (S : Finset (Fin m)) (c : Fin m → Fin m → F) : Matrix (Fin m) (Fin m) F :=
  1 + radicalPart S c

theorem radicalMatrix_mul (S : Finset (Fin m)) (c d : Fin m → Fin m → F) :
    radicalMatrix S c * radicalMatrix S d = radicalMatrix S (c + d) := by
  rw [radicalMatrix, radicalMatrix, radicalMatrix, ← radicalPart_add]
  simp only [add_mul, mul_add, one_mul, mul_one, radicalPart_mul, add_zero]
  abel

theorem radicalMatrix_zero (S : Finset (Fin m)) :
    radicalMatrix S (0 : Fin m → Fin m → F) = 1 := by
  ext a b
  simp [radicalMatrix, radicalPart]

/-- The invertible matrix `1 + radicalPart S c`, with inverse `1 + radicalPart S (-c)`. -/
def radicalElement (S : Finset (Fin m)) (c : Fin m → Fin m → F) :
    Matrix.GeneralLinearGroup (Fin m) F :=
  ofInverse (radicalMatrix S c) (radicalMatrix S (-c))
    (by rw [radicalMatrix_mul, add_neg_cancel, radicalMatrix_zero])
    (by rw [radicalMatrix_mul, neg_add_cancel, radicalMatrix_zero])

theorem radicalElement_apply (S : Finset (Fin m)) (c : Fin m → Fin m → F) (a b : Fin m) :
    radicalElement S c a b =
      (if a = b then 1 else 0) + if IsRadicalPair S a b then c a b else 0 := by
  change (1 + radicalPart S c) a b = _
  rw [Matrix.add_apply, Matrix.one_apply]
  rfl

theorem radicalElement_inv (S : Finset (Fin m)) (c : Fin m → Fin m → F) :
    (radicalElement S c)⁻¹ = radicalElement S (-c) :=
  Units.ext rfl

theorem radicalElement_mul (S : Finset (Fin m)) (c d : Fin m → Fin m → F) :
    radicalElement S c * radicalElement S d = radicalElement S (c + d) :=
  Units.ext (radicalMatrix_mul S c d)

theorem radicalElement_mem_upperUnipotent (S : Finset (Fin m)) (c : Fin m → Fin m → F) :
    radicalElement S c ∈ upperUnipotent m F := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · change radicalElement S c a b = 0
    have hab : a ≠ b := (ne_of_lt hba).symm
    have hp : ¬IsRadicalPair S a b := fun h => absurd h.2.2 (not_lt.mpr hba.le)
    simp [radicalElement_apply, hab, hp]
  · change radicalElement S c a a = 1
    have hp : ¬IsRadicalPair S a a := fun h => h.ne rfl
    simp [radicalElement_apply, hp]

/-- The diagonal exponent `1` on `S` and `0` off `S`. -/
def subsetExponent (S : Finset (Fin m)) : Fin m → ℤ :=
  fun j => if j ∈ S then 1 else 0

/-- The diagonal matrix with `ϖ` on `S` and `1` off `S`. -/
abbrev subsetTorus (ϖ : Fˣ) (S : Finset (Fin m)) : Matrix.GeneralLinearGroup (Fin m) F :=
  torus ϖ (subsetExponent S)

theorem subsetTorus_apply (ϖ : Fˣ) (S : Finset (Fin m)) (a b : Fin m) :
    subsetTorus ϖ S a b = if a = b then (if a ∈ S then (ϖ : F) else 1) else 0 := by
  change (diagonal fun i => ((ϖ ^ subsetExponent S i : Fˣ) : F)) a b = _
  rw [Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a ∈ S <;> simp [subsetExponent, ha]
  · simp [hab]

theorem subsetExponent_injective :
    Function.Injective (subsetExponent : Finset (Fin m) → Fin m → ℤ) := by
  intro S S' h
  ext j
  have hj := congrFun h j
  simp only [subsetExponent] at hj
  by_cases hS : j ∈ S <;> by_cases hS' : j ∈ S' <;> simp_all

/-- The chosen coset representative `radicalElement S c * subsetTorus ϖ S`. -/
def cosetRep (ϖ : Fˣ) (S : Finset (Fin m)) (c : Fin m → Fin m → F) :
    Matrix.GeneralLinearGroup (Fin m) F :=
  radicalElement S c * subsetTorus ϖ S

/-- Conjugating a radical element by the subset torus divides its radical entries by `ϖ`. -/
theorem torusConj_apply (ϖ : Fˣ) (S : Finset (Fin m)) (c : Fin m → Fin m → F) (a b : Fin m) :
    ((subsetTorus ϖ S)⁻¹ * radicalElement S c * subsetTorus ϖ S) a b =
      (if a = b then 1 else 0) + if IsRadicalPair S a b then (ϖ : F)⁻¹ * c a b else 0 := by
  rw [subsetTorus, torus_inv, torus, diagonalUnits_mul_mul_apply, radicalElement_apply]
  by_cases hab : a = b
  · subst hab
    have hp : ¬IsRadicalPair S a a := fun h => h.ne rfl
    simp only [hp, ↓reduceIte, add_zero, mul_one]
    simp only [Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
    exact inv_mul_cancel₀ (zpow_ne_zero _ ϖ.ne_zero)
  · by_cases hp : IsRadicalPair S a b
    · simp [hab, hp, subsetExponent, hp.1, hp.2.1]
    · simp [hab, hp]

theorem mul_subsetTorus_apply (ϖ : Fˣ) (g : Matrix.GeneralLinearGroup (Fin m) F)
    (S : Finset (Fin m)) (a j : Fin m) :
    (g * subsetTorus ϖ S) a j = g a j * if j ∈ S then (ϖ : F) else 1 := by
  change (g.val * diagonal fun i => ((ϖ ^ subsetExponent S i : Fˣ) : F)) a j = _
  rw [Matrix.mul_diagonal]
  by_cases hj : j ∈ S <;> simp [subsetExponent, hj]

theorem subsetTorus_mul_apply (ϖ : Fˣ) (g : Matrix.GeneralLinearGroup (Fin m) F)
    (S : Finset (Fin m)) (a j : Fin m) :
    (subsetTorus ϖ S * g) a j = (if a ∈ S then (ϖ : F) else 1) * g a j := by
  change ((diagonal fun i => ((ϖ ^ subsetExponent S i : Fˣ) : F)) * g.val) a j = _
  rw [Matrix.diagonal_mul]
  by_cases ha : a ∈ S <;> simp [subsetExponent, ha]

theorem mul_subsetTorus_inv_apply (ϖ : Fˣ) (g : Matrix.GeneralLinearGroup (Fin m) F)
    (S : Finset (Fin m)) (a j : Fin m) :
    (g * (subsetTorus ϖ S)⁻¹) a j = g a j * if j ∈ S then (ϖ : F)⁻¹ else 1 := by
  rw [subsetTorus, torus_inv]
  change (g.val * diagonal fun i => (((ϖ ^ subsetExponent S i)⁻¹ : Fˣ) : F)) a j = _
  rw [Matrix.mul_diagonal]
  by_cases hj : j ∈ S <;> simp [subsetExponent, hj]

theorem det_subsetTorus (ϖ : Fˣ) (S : Finset (Fin m)) :
    (subsetTorus ϖ S : Matrix (Fin m) (Fin m) F).det = (ϖ : F) ^ S.card := by
  classical
  change (diagonal fun i => ((ϖ ^ subsetExponent S i : Fˣ) : F)).det = _
  rw [Matrix.det_diagonal]
  have h : ∀ i, ((ϖ ^ subsetExponent S i : Fˣ) : F) = if i ∈ S then (ϖ : F) else 1 := by
    intro i
    by_cases hi : i ∈ S <;> simp [subsetExponent, hi]
  simp only [h]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- A permutation carrying `S'` onto `S` conjugates `t_S` into `t_S'`. -/
theorem subsetTorus_conj (ϖ : Fˣ) {S S' : Finset (Fin m)} {σ : Equiv.Perm (Fin m)}
    (hσ : ∀ a, σ a ∈ S ↔ a ∈ S') :
    Cartan.permGL σ * subsetTorus ϖ S * Cartan.permGL σ.symm = subsetTorus ϖ S' := by
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  rw [Cartan.permGL_mul_mul_apply, Equiv.symm_symm, subsetTorus_apply, subsetTorus_apply]
  simp only [σ.injective.eq_iff, hσ]

/-- Two subsets of the same size are related by a permutation. -/
theorem exists_perm_mem_iff {S S' : Finset (Fin m)} (h : S.card = S'.card) :
    ∃ σ : Equiv.Perm (Fin m), ∀ a, σ a ∈ S ↔ a ∈ S' := by
  have h1 : Fintype.card {x // x ∈ S'} = Fintype.card {x // x ∈ S} := by
    rw [Fintype.card_coe, Fintype.card_coe, h]
  have h2 : Fintype.card {x // x ∉ S'} = Fintype.card {x // x ∉ S} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2),
    fun a => ?_⟩
  by_cases ha : a ∈ S'
  · simp only [Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos ha,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl, ha, iff_true]
    exact (Fintype.equivOfCardEq h1 ⟨a, ha⟩).2
  · simp only [Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg ha,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr, ha, iff_false]
    exact (Fintype.equivOfCardEq h2 ⟨a, ha⟩).2

/-- An upper triangular matrix with unit diagonal, as an invertible matrix. -/
def unipotentOf (A : Matrix (Fin m) (Fin m) F) (hA : A.IsUpperTriangular)
    (hd : ∀ i, A i i = 1) : Matrix.GeneralLinearGroup (Fin m) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero A (by
    rw [Matrix.det_of_isUpperTriangular hA, Finset.prod_eq_one fun i _ => hd i]
    exact one_ne_zero)

theorem unipotentOf_apply (A : Matrix (Fin m) (Fin m) F) (hA : A.IsUpperTriangular)
    (hd : ∀ i, A i i = 1) (a b : Fin m) : unipotentOf A hA hd a b = A a b :=
  rfl

theorem unipotentOf_mem (A : Matrix (Fin m) (Fin m) F) (hA : A.IsUpperTriangular)
    (hd : ∀ i, A i i = 1) : unipotentOf A hA hd ∈ upperUnipotent m F :=
  ⟨hA, hd⟩

theorem det_eq_one_of_mem_upperUnipotent {g : Matrix.GeneralLinearGroup (Fin m) F}
    (hg : g ∈ upperUnipotent m F) : (g : Matrix (Fin m) (Fin m) F).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular hg.1, Finset.prod_eq_one fun i _ => hg.2 i]

theorem glDet_eq_one_of_mem_upperUnipotent {g : Matrix.GeneralLinearGroup (Fin m) F}
    (hg : g ∈ upperUnipotent m F) : Matrix.GeneralLinearGroup.det g = 1 :=
  Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact det_eq_one_of_mem_upperUnipotent hg)

end Radical

/-! ### Valuation facts -/

section Valuation

variable {ϖ : Fˣ}

theorem le_of_lt_one (hϖ : IsUniformizingElement v ϖ) {x : F} (hx : v x < 1) :
    v x ≤ v (ϖ : F) := by
  by_cases h0 : x = 0
  · rw [h0, map_zero]
    exact zero_le
  obtain ⟨k, hk⟩ := hϖ.2 x h0
  have hpos := valuation_pos v ϖ
  rw [hk] at hx ⊢
  have hk1 : 0 < k := by
    by_contra hle
    have := (one_le_zpow_iff_right_of_lt_one₀ hpos hϖ.1).mpr (not_lt.mp hle)
    exact absurd hx (not_lt.mpr this)
  calc v (ϖ : F) ^ k ≤ v (ϖ : F) ^ (1 : ℤ) :=
        (zpow_le_zpow_iff_right_of_lt_one₀ hpos hϖ.1).mpr hk1
    _ = v (ϖ : F) := zpow_one _

theorem uniformizer_mem (hϖ : IsUniformizingElement v ϖ) : (ϖ : F) ∈ v.integer :=
  (Valuation.mem_integer_iff v _).2 hϖ.1.le

/-- An element whose quotient by `ϖ` is integral has valuation below one. -/
theorem lt_one_of_inv_mul_mem (hϖ : IsUniformizingElement v ϖ) {x : F}
    (hx : (ϖ : F)⁻¹ * x ∈ v.integer) : v x < 1 := by
  have h := (Valuation.mem_integer_iff v _).1 hx
  rw [map_mul, map_inv₀] at h
  have hpos := valuation_pos v ϖ
  have hle : v x ≤ v (ϖ : F) := by
    rwa [inv_mul_le_iff₀ hpos, mul_one] at h
  exact lt_of_le_of_lt hle hϖ.1

theorem inv_mul_mem_of_lt_one (hϖ : IsUniformizingElement v ϖ) {x : F} (hx : v x < 1) :
    (ϖ : F)⁻¹ * x ∈ v.integer := by
  rw [Valuation.mem_integer_iff, map_mul, map_inv₀]
  have hpos := valuation_pos v ϖ
  rw [inv_mul_le_iff₀ hpos, mul_one]
  exact le_of_lt_one hϖ hx

end Valuation

/-! ### Integral matrices -/

section Integral

variable {n : ℕ}

theorem entry_mem {k : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hk : k ∈ integralSubgroup v.integer n) (i j : Fin (n + 1)) : k i j ∈ v.integer :=
  ((mem_integralSubgroup v.integer n k).1 hk).1 i j

theorem mul_entry_mem {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) F}
    (hA : ∀ i j, A i j ∈ v.integer) (hB : ∀ i j, B i j ∈ v.integer) (i j : Fin (n + 1)) :
    (A * B) i j ∈ v.integer := by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem valuation_det_eq_one {k : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hk : k ∈ integralSubgroup v.integer n) : v (k : Matrix (Fin (n + 1)) (Fin (n + 1)) F).det = 1 := by
  have h1 := (Valuation.mem_integer_iff v _).1
    (Cartan.det_mem_integer (k : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (entry_mem hk))
  have h2 := (Valuation.mem_integer_iff v _).1
    (Cartan.det_mem_integer ((k⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F) (entry_mem (inv_mem hk)))
  have hprod : v (k : Matrix (Fin (n + 1)) (Fin (n + 1)) F).det *
      v ((k⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.det_one, map_one]
  refine le_antisymm h1 (not_lt.1 fun hlt => ?_)
  have := mul_lt_one_of_lt_of_le hlt h2
  rw [hprod] at this
  exact lt_irrefl _ this

/-- An integral matrix whose determinant has valuation one is integral invertible. -/
theorem mem_integralSubgroup_of_det {g : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hg : ∀ i j, g i j ∈ v.integer)
    (hdet : v (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F).det = 1) :
    g ∈ integralSubgroup v.integer n := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) v.integer := fun i j => ⟨g i j, hg i j⟩
  have hA : A.map v.integer.subtype = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) := rfl
  have hdetA : ((A.det : v.integer) : F) = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F).det := by
    rw [← hA]
    exact RingHom.map_det v.integer.subtype A
  have hunit : IsUnit A.det := by
    rw [(Valuation.integer.integers v).isUnit_iff_valuation_eq_one]
    change v ((A.det : v.integer) : F) = 1
    rw [hdetA, hdet]
  exact ⟨Matrix.GeneralLinearGroup.mk'' A hunit, Matrix.GeneralLinearGroup.ext fun i j => rfl⟩

theorem radicalElement_mem {S : Finset (Fin (n + 1))} {c : Fin (n + 1) → Fin (n + 1) → F}
    (hc : ∀ a b, IsRadicalPair S a b → c a b ∈ v.integer) :
    radicalElement S c ∈ integralSubgroup v.integer n := by
  have key : ∀ d : Fin (n + 1) → Fin (n + 1) → F,
      (∀ a b, IsRadicalPair S a b → d a b ∈ v.integer) →
        ∀ a b, radicalElement S d a b ∈ v.integer := by
    intro d hd a b
    rw [radicalElement_apply]
    refine add_mem ?_ ?_
    · split_ifs
      · exact one_mem _
      · exact zero_mem _
    · split_ifs with h
      · exact hd a b h
      · exact zero_mem _
  rw [mem_integralSubgroup]
  refine ⟨key c hc, ?_⟩
  rw [radicalElement_inv]
  exact key (-c) fun a b h => neg_mem (hc a b h)

theorem subsetTorus_entry_mem {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
    (S : Finset (Fin (n + 1))) (a b : Fin (n + 1)) : subsetTorus ϖ S a b ∈ v.integer := by
  rw [subsetTorus_apply]
  split_ifs
  · exact uniformizer_mem hϖ
  · exact one_mem _
  · exact zero_mem _

end Integral

/-! ### Conjugation of radical elements by the subset torus -/

section Conjugation

variable {n : ℕ} {ϖ : Fˣ}

theorem torusConj_mem (hϖ : IsUniformizingElement v ϖ) {S : Finset (Fin (n + 1))}
    {c : Fin (n + 1) → Fin (n + 1) → F} (hc : ∀ a b, IsRadicalPair S a b → v (c a b) < 1) :
    (subsetTorus ϖ S)⁻¹ * radicalElement S c * subsetTorus ϖ S ∈
      integralSubgroup v.integer n := by
  have key : ∀ d : Fin (n + 1) → Fin (n + 1) → F,
      (∀ a b, IsRadicalPair S a b → v (d a b) < 1) → ∀ a b,
        ((subsetTorus ϖ S)⁻¹ * radicalElement S d * subsetTorus ϖ S) a b ∈ v.integer := by
    intro d hd a b
    rw [torusConj_apply]
    refine add_mem ?_ ?_
    · split_ifs
      · exact one_mem _
      · exact zero_mem _
    · split_ifs with h
      · exact inv_mul_mem_of_lt_one hϖ (hd a b h)
      · exact zero_mem _
  rw [mem_integralSubgroup]
  refine ⟨key c hc, ?_⟩
  have hinv : ((subsetTorus ϖ S)⁻¹ * radicalElement S c * subsetTorus ϖ S)⁻¹ =
      (subsetTorus ϖ S)⁻¹ * radicalElement S (-c) * subsetTorus ϖ S := by
    rw [← radicalElement_inv]
    group
  rw [hinv]
  exact key (-c) fun a b h => by rw [Pi.neg_apply, Pi.neg_apply, Valuation.map_neg]; exact hc a b h

theorem lt_one_of_torusConj_mem (hϖ : IsUniformizingElement v ϖ) {S : Finset (Fin (n + 1))}
    {c : Fin (n + 1) → Fin (n + 1) → F}
    (h : (subsetTorus ϖ S)⁻¹ * radicalElement S c * subsetTorus ϖ S ∈
      integralSubgroup v.integer n)
    {a b : Fin (n + 1)} (hab : IsRadicalPair S a b) : v (c a b) < 1 := by
  have he := entry_mem h a b
  simp only [torusConj_apply, hab.ne, hab, ↓reduceIte, zero_add] at he
  exact lt_one_of_inv_mul_mem hϖ he

theorem cosetRep_inv_mul (S : Finset (Fin (n + 1))) (c c' : Fin (n + 1) → Fin (n + 1) → F) :
    (cosetRep ϖ S c)⁻¹ * cosetRep ϖ S c' =
      (subsetTorus ϖ S)⁻¹ * radicalElement S (c' - c) * subsetTorus ϖ S := by
  rw [cosetRep, cosetRep, _root_.mul_inv_rev, radicalElement_inv, mul_assoc,
    ← mul_assoc _ _ (_ * _), ← mul_assoc, mul_assoc _ (radicalElement S (-c)), radicalElement_mul,
    neg_add_eq_sub]

/-- Two representatives with the same subset lie in the same left coset exactly when
their radical entries agree modulo the maximal ideal. -/
theorem cosetRep_inv_mul_mem_of_congr (hϖ : IsUniformizingElement v ϖ)
    {S : Finset (Fin (n + 1))} {c c' : Fin (n + 1) → Fin (n + 1) → F}
    (h : ∀ a b, IsRadicalPair S a b → v (c' a b - c a b) < 1) :
    (cosetRep ϖ S c)⁻¹ * cosetRep ϖ S c' ∈ integralSubgroup v.integer n := by
  rw [cosetRep_inv_mul]
  exact torusConj_mem hϖ fun a b hab => by rw [Pi.sub_apply, Pi.sub_apply]; exact h a b hab

/-- Distinct representatives lie in distinct left cosets. -/
theorem eq_of_cosetRep_inv_mul_mem (hϖ : IsUniformizingElement v ϖ)
    {S S' : Finset (Fin (n + 1))} {c c' : Fin (n + 1) → Fin (n + 1) → F}
    (h : (cosetRep ϖ S c)⁻¹ * cosetRep ϖ S' c' ∈ integralSubgroup v.integer n) :
    S = S' ∧ ∀ a b, IsRadicalPair S a b → v (c' a b - c a b) < 1 := by
  have hS : S = S' := by
    apply subsetExponent_injective
    apply iwasawa_exponent_unique hϖ (radicalElement_mem_upperUnipotent S c)
      (radicalElement_mem_upperUnipotent S' c') h (one_mem _)
    change cosetRep ϖ S c * ((cosetRep ϖ S c)⁻¹ * cosetRep ϖ S' c') = cosetRep ϖ S' c' * 1
    rw [mul_inv_cancel_left, mul_one]
  subst hS
  refine ⟨rfl, fun a b hab => ?_⟩
  rw [cosetRep_inv_mul] at h
  have := lt_one_of_torusConj_mem hϖ h hab
  rwa [Pi.sub_apply, Pi.sub_apply] at this

end Conjugation

/-! ### The double coset of a subset torus -/

section DoubleCoset

variable {n : ℕ} {ϖ : Fˣ}

theorem unipotent_mem_integralSubgroup {g : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hg : g ∈ upperUnipotent (n + 1) F) (he : ∀ a b, g a b ∈ v.integer) :
    g ∈ integralSubgroup v.integer n :=
  mem_integralSubgroup_of_det he (by rw [det_eq_one_of_mem_upperUnipotent hg, map_one])

/-- Every representative with integral radical entries lies in `K t_S' K` when `|S| = |S'|`. -/
theorem cosetRep_mem_doubleCoset {S S' : Finset (Fin (n + 1))} (h : S.card = S'.card)
    {c : Fin (n + 1) → Fin (n + 1) → F} (hc : ∀ a b, IsRadicalPair S a b → c a b ∈ v.integer) :
    ∃ k₁ ∈ integralSubgroup v.integer n, ∃ k₂ ∈ integralSubgroup v.integer n,
      cosetRep ϖ S c = k₁ * subsetTorus ϖ S' * k₂ := by
  obtain ⟨σ, hσ⟩ := exists_perm_mem_iff h.symm
  refine ⟨radicalElement S c * Cartan.permGL σ,
    mul_mem (radicalElement_mem hc) (Cartan.permGL_mem σ), Cartan.permGL σ.symm,
    Cartan.permGL_mem _, ?_⟩
  rw [cosetRep, ← subsetTorus_conj ϖ hσ]
  simp only [mul_assoc]

theorem doubleCoset_entry_mem (hϖ : IsUniformizingElement v ϖ)
    {k₁ k₂ : Matrix.GeneralLinearGroup (Fin (n + 1)) F} (hk₁ : k₁ ∈ integralSubgroup v.integer n)
    (hk₂ : k₂ ∈ integralSubgroup v.integer n) (S : Finset (Fin (n + 1))) (a b : Fin (n + 1)) :
    (k₁ * subsetTorus ϖ S * k₂) a b ∈ v.integer := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact mul_entry_mem (mul_entry_mem (entry_mem hk₁) (subsetTorus_entry_mem hϖ S))
    (entry_mem hk₂) a b

theorem doubleCoset_inv_entry_mem (hϖ : IsUniformizingElement v ϖ)
    {k₁ k₂ : Matrix.GeneralLinearGroup (Fin (n + 1)) F} (hk₁ : k₁ ∈ integralSubgroup v.integer n)
    (hk₂ : k₂ ∈ integralSubgroup v.integer n) (S : Finset (Fin (n + 1))) (a b : Fin (n + 1)) :
    (ϖ : F) * ((k₁ * subsetTorus ϖ S * k₂)⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) a b ∈
      v.integer := by
  have he : (k₁ * subsetTorus ϖ S * k₂)⁻¹ = k₂⁻¹ * (subsetTorus ϖ S)⁻¹ * k₁⁻¹ := by group
  rw [he, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Finset.mul_sum]
  refine sum_mem fun f _ => ?_
  rw [mul_subsetTorus_inv_apply]
  have hd : (ϖ : F) * (if f ∈ S then (ϖ : F)⁻¹ else 1) ∈ v.integer := by
    split_ifs
    · rw [mul_inv_cancel₀ ϖ.ne_zero]
      exact one_mem _
    · rw [mul_one]
      exact uniformizer_mem hϖ
  have := mul_mem (mul_mem (entry_mem (inv_mem hk₂) a f) hd) (entry_mem (inv_mem hk₁) f b)
  convert this using 1
  ring

/-- The exponents of a bounded Iwasawa torus part are zero or one. -/
theorem exponent_eq_zero_or_one (hϖ : IsUniformizingElement v ϖ)
    {u : Matrix.GeneralLinearGroup (Fin (n + 1)) F} (hu : u ∈ upperUnipotent (n + 1) F)
    {lam : Fin (n + 1) → ℤ} (hb : ∀ a b, (u * torus ϖ lam) a b ∈ v.integer)
    (hb' : ∀ a b, (ϖ : F) * ((u * torus ϖ lam)⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) a b ∈
      v.integer) (j : Fin (n + 1)) : lam j = 0 ∨ lam j = 1 := by
  have hpos := valuation_pos v ϖ
  have h1 : (u * torus ϖ lam) j j = (ϖ : F) ^ lam j := by
    change (u.val * diagonal fun i => ((ϖ ^ lam i : Fˣ) : F)) j j = _
    rw [Matrix.mul_diagonal, hu.2 j, one_mul, Units.val_zpow_eq_zpow_val]
  have h2 : ((u * torus ϖ lam)⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) j j =
      (ϖ : F) ^ (-lam j) := by
    rw [_root_.mul_inv_rev, torus_inv]
    change (diagonal (fun i => (((ϖ ^ lam i)⁻¹ : Fˣ) : F)) * (u⁻¹ :
      Matrix.GeneralLinearGroup (Fin (n + 1)) F).val) j j = _
    rw [Matrix.diagonal_mul, (inv_mem hu).2 j, mul_one, Units.val_inv_eq_inv_val,
      Units.val_zpow_eq_zpow_val, zpow_neg]
  have hle1 := (Valuation.mem_integer_iff v _).1 (hb j j)
  have hle2 := (Valuation.mem_integer_iff v _).1 (hb' j j)
  rw [h1, map_zpow₀, zpow_le_one_iff_right_of_lt_one₀ hpos hϖ.1] at hle1
  rw [h2, ← zpow_one_add₀ ϖ.ne_zero, map_zpow₀,
    zpow_le_one_iff_right_of_lt_one₀ hpos hϖ.1] at hle2
  omega

/-- A bounded element `u t_S` with `u` upper unipotent lies in a left coset `n t_S K`. -/
theorem exists_cosetRep_of_bounds {S : Finset (Fin (n + 1))}
    {u : Matrix.GeneralLinearGroup (Fin (n + 1)) F} (hu : u ∈ upperUnipotent (n + 1) F)
    (hb : ∀ a b, (u * subsetTorus ϖ S) a b ∈ v.integer)
    (hb' : ∀ a b, (ϖ : F) *
      ((u * subsetTorus ϖ S)⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) a b ∈ v.integer) :
    ∃ c : Fin (n + 1) → Fin (n + 1) → F, (∀ a b, c a b ∈ v.integer) ∧
      (cosetRep ϖ S c)⁻¹ * (u * subsetTorus ϖ S) ∈ integralSubgroup v.integer n := by
  classical
  have hcol : ∀ a j, j ∉ S → (u * subsetTorus ϖ S) a j = u a j := by
    intro a j hj
    rw [mul_subsetTorus_apply]
    simp [hj]
  have huint : ∀ a j, j ∉ S → u a j ∈ v.integer := fun a j hj => hcol a j hj ▸ hb a j
  -- `U` replaces the columns of `u` in `S` by unit vectors.
  let Um : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    fun a j => if j ∈ S then (if a = j then 1 else 0) else u a j
  have hUut : Um.IsUpperTriangular := by
    intro a j hja
    simp only [Um]
    split_ifs with hj haj
    · exact absurd haj (ne_of_gt hja)
    · rfl
    · exact hu.1 hja
  have hUd : ∀ i, Um i i = 1 := by
    intro i
    by_cases hi : i ∈ S <;> simp [Um, hi, hu.2 i]
  let U := unipotentOf Um hUut hUd
  have hUu : U ∈ upperUnipotent (n + 1) F := unipotentOf_mem _ _ _
  have hUK : U ∈ integralSubgroup v.integer n := by
    refine unipotent_mem_integralSubgroup hUu fun a j => ?_
    rw [unipotentOf_apply]
    simp only [Um]
    split_ifs with hj haj
    · exact one_mem _
    · exact zero_mem _
    · exact huint a j hj
  -- `E` keeps only the entries of `u` with row and column outside `S`.
  let Em : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    fun a j => if a ∉ S ∧ j ∉ S then u a j else (if a = j then 1 else 0)
  have hEut : Em.IsUpperTriangular := by
    intro a j hja
    simp only [Em]
    split_ifs with h haj
    · exact hu.1 hja
    · exact absurd haj (ne_of_gt hja)
    · rfl
  have hEd : ∀ i, Em i i = 1 := by
    intro i
    by_cases hi : i ∈ S <;> simp [Em, hi, hu.2 i]
  let E := unipotentOf Em hEut hEd
  have hEu : E ∈ upperUnipotent (n + 1) F := unipotentOf_mem _ _ _
  have hEK : E ∈ integralSubgroup v.integer n := by
    refine unipotent_mem_integralSubgroup hEu fun a j => ?_
    rw [unipotentOf_apply]
    simp only [Em]
    split_ifs with h haj
    · exact huint a j h.2
    · exact one_mem _
    · exact zero_mem _
  have hEt : E * subsetTorus ϖ S = subsetTorus ϖ S * E := by
    apply Matrix.GeneralLinearGroup.ext
    intro a j
    rw [mul_subsetTorus_apply, subsetTorus_mul_apply, unipotentOf_apply]
    simp only [Em]
    by_cases ha : a ∈ S <;> by_cases hj : j ∈ S
    · simp [ha, hj, mul_comm]
    · have haj : a ≠ j := fun h => hj (h ▸ ha)
      simp [ha, hj, haj]
    · have haj : a ≠ j := fun h => ha (h ▸ hj)
      simp [ha, hj, haj]
    · simp [ha, hj]
  -- `c = b⁻¹ U t_S` is integral.
  have hcK : (u * subsetTorus ϖ S)⁻¹ * U * subsetTorus ϖ S ∈ integralSubgroup v.integer n := by
    apply mem_integralSubgroup_of_det
    · intro a j
      rw [mul_assoc, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply]
      by_cases hj : j ∈ S
      · have hUt : ∀ f, (U * subsetTorus ϖ S) f j = if f = j then (ϖ : F) else 0 := by
          intro f
          rw [mul_subsetTorus_apply, unipotentOf_apply]
          simp only [Um, hj, ↓reduceIte]
          split_ifs <;> simp
        simp only [hUt, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rw [mul_comm]
        exact hb' a j
      · have hUt : ∀ f, (U * subsetTorus ϖ S) f j = (u * subsetTorus ϖ S) f j := by
          intro f
          rw [hcol f j hj, mul_subsetTorus_apply, unipotentOf_apply]
          simp [Um, hj]
        simp only [hUt]
        rw [← Matrix.mul_apply, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    · rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv, map_mul,
        glDet_eq_one_of_mem_upperUnipotent hu, glDet_eq_one_of_mem_upperUnipotent hUu]
      simp
  -- `N = U E⁻¹` is a radical element.
  have hEinv : ∀ f j, j ∈ S →
      ((E⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
        f j = if f = j then 1 else 0 := by
    intro f j hj
    have h := congrArg (fun M : Matrix.GeneralLinearGroup (Fin (n + 1)) F =>
      (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F) f j) (inv_mul_cancel E)
    have hEj : ∀ g, E g j = if g = j then 1 else 0 := by
      intro g
      rw [unipotentOf_apply]
      simp [Em, hj]
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, hEj, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
    exact h
  have hrow : ∀ a f, a ∉ S → U a f = E a f := by
    intro a f ha
    rw [unipotentOf_apply, unipotentOf_apply]
    simp only [Um, Em]
    by_cases hf : f ∈ S <;> simp [hf, ha]
  have hNu : U * E⁻¹ ∈ upperUnipotent (n + 1) F := mul_mem hUu (inv_mem hEu)
  have hNK : U * E⁻¹ ∈ integralSubgroup v.integer n := mul_mem hUK (inv_mem hEK)
  have hNentry : ∀ a j, ¬IsRadicalPair S a j → (U * E⁻¹) a j = if a = j then 1 else 0 := by
    intro a j hp
    by_cases hj : j ∈ S
    · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply]
      simp only [hEinv _ j hj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte]
      rw [unipotentOf_apply]
      simp [Um, hj]
    · by_cases ha : a ∈ S
      · have hja : ¬a < j := fun h => hp ⟨ha, hj, h⟩
        rcases (not_lt.1 hja).lt_or_eq with h | h
        · rw [hNu.1 h]
          simp [ne_of_gt h]
        · subst h
          rw [hNu.2]
          simp
      · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply]
        simp only [hrow a _ ha]
        rw [← Matrix.mul_apply, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]
  have hNrad : U * E⁻¹ = radicalElement S (fun a j => (U * E⁻¹) a j) := by
    apply Matrix.GeneralLinearGroup.ext
    intro a j
    rw [radicalElement_apply]
    by_cases hp : IsRadicalPair S a j
    · simp [hp, hp.ne]
    · rw [hNentry a j hp]
      simp [hp]
  refine ⟨fun a j => (U * E⁻¹) a j, fun a j => entry_mem hNK a j, ?_⟩
  rw [cosetRep, ← hNrad]
  have h2 : (subsetTorus ϖ S)⁻¹ * E = E * (subsetTorus ϖ S)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, hEt, inv_mul_cancel_left]
  have hc : (U * E⁻¹ * subsetTorus ϖ S)⁻¹ * (u * subsetTorus ϖ S) =
      E * ((u * subsetTorus ϖ S)⁻¹ * U * subsetTorus ϖ S)⁻¹ := by
    calc (U * E⁻¹ * subsetTorus ϖ S)⁻¹ * (u * subsetTorus ϖ S)
        = (subsetTorus ϖ S)⁻¹ * E * U⁻¹ * (u * subsetTorus ϖ S) := by group
      _ = E * (subsetTorus ϖ S)⁻¹ * U⁻¹ * (u * subsetTorus ϖ S) := by rw [h2]
      _ = E * ((u * subsetTorus ϖ S)⁻¹ * U * subsetTorus ϖ S)⁻¹ := by group
  rw [hc]
  exact mul_mem hEK (inv_mem hcK)

/-- Every element of `K t_S' K` lies in a left coset `n t_S K` with `|S| = |S'|`. -/
theorem exists_cosetRep_of_mem_doubleCoset (hϖ : IsUniformizingElement v ϖ)
    {S' : Finset (Fin (n + 1))} {g k₁ k₂ : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hk₁ : k₁ ∈ integralSubgroup v.integer n) (hk₂ : k₂ ∈ integralSubgroup v.integer n)
    (hg : g = k₁ * subsetTorus ϖ S' * k₂) :
    ∃ S : Finset (Fin (n + 1)), S.card = S'.card ∧ ∃ c : Fin (n + 1) → Fin (n + 1) → F,
      (∀ a b, c a b ∈ v.integer) ∧ (cosetRep ϖ S c)⁻¹ * g ∈ integralSubgroup v.integer n := by
  classical
  obtain ⟨u, hu, lam, k, hk, hgk⟩ := exists_iwasawa hϖ g
  have hk' : k₂ * k⁻¹ ∈ integralSubgroup v.integer n := mul_mem hk₂ (inv_mem hk)
  have hbeq : u * torus ϖ lam = k₁ * subsetTorus ϖ S' * (k₂ * k⁻¹) := by
    rw [← mul_assoc, ← hg, hgk, mul_inv_cancel_right]
  have hb : ∀ a b, (u * torus ϖ lam) a b ∈ v.integer := by
    rw [hbeq]
    exact doubleCoset_entry_mem hϖ hk₁ hk' S'
  have hb' : ∀ a b, (ϖ : F) *
      ((u * torus ϖ lam)⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) a b ∈ v.integer := by
    rw [hbeq]
    exact doubleCoset_inv_entry_mem hϖ hk₁ hk' S'
  have h01 := exponent_eq_zero_or_one hϖ hu hb hb'
  let S : Finset (Fin (n + 1)) := Finset.univ.filter fun j => lam j = 1
  have hlam : lam = subsetExponent S := by
    funext j
    rcases h01 j with h | h <;> simp [subsetExponent, S, h]
  have hcard : S.card = S'.card := by
    have hdet : v ((u * torus ϖ lam : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F).det =
        v ((k₁ * subsetTorus ϖ S' * (k₂ * k⁻¹) : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) F).det := by
      rw [hbeq]
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, map_mul] at hdet
    rw [det_eq_one_of_mem_upperUnipotent hu, valuation_det_eq_one hk₁,
      valuation_det_eq_one hk₂, valuation_det_eq_one (inv_mem hk), hlam, det_subsetTorus,
      det_subsetTorus] at hdet
    simp only [map_one, one_mul, mul_one, map_pow] at hdet
    exact (pow_right_strictAnti₀ (valuation_pos v ϖ) hϖ.1).injective hdet
  rw [hlam] at hb hb'
  obtain ⟨c, hc, hcK⟩ := exists_cosetRep_of_bounds hu hb hb'
  refine ⟨S, hcard, c, hc, ?_⟩
  have hg' : g = u * subsetTorus ϖ S * k := by rw [hgk, hlam]
  rw [hg', ← mul_assoc]
  exact mul_mem hcK hk

end DoubleCoset

/-! ### Representatives labelled by residues -/

section Labelled

variable {n : ℕ} {ϖ : Fˣ} {Λ : Type*} {σ : Λ → F}

/-- The radical pairs of `S`, as a type. -/
abbrev RadicalPairs {m : ℕ} (S : Finset (Fin m)) :=
  {p : Fin m × Fin m // IsRadicalPair S p.1 p.2}

/-- Radical entries from labels: `σ (w (a, b))` on the radical pairs and `0` elsewhere. -/
def liftCoeff {m : ℕ} (σ : Λ → F) (S : Finset (Fin m)) (w : RadicalPairs S → Λ) :
    Fin m → Fin m → F :=
  fun a b => if h : IsRadicalPair S a b then σ (w ⟨(a, b), h⟩) else 0

/-- The index set: a subset of size `i` and a label for each of its radical pairs. -/
abbrev CosetIndex (Λ : Type*) (m i : ℕ) :=
  Σ S : {S : Finset (Fin m) // S.card = i}, (RadicalPairs S.1 → Λ)

/-- The representative `cosetRep ϖ S (liftCoeff σ S w)` of the index `⟨S, w⟩`. -/
def labelledRep {m i : ℕ} (ϖ : Fˣ) (σ : Λ → F) (α : CosetIndex Λ m i) :
    Matrix.GeneralLinearGroup (Fin m) F :=
  cosetRep ϖ α.1.1 (liftCoeff σ α.1.1 α.2)

/-- Every labelled representative lies in `K t_S' K` when `|S'| = i`. -/
theorem labelledRep_mem_doubleCoset {i : ℕ} (hσ : ∀ x, σ x ∈ v.integer)
    {S' : Finset (Fin (n + 1))} (hS' : S'.card = i) (α : CosetIndex Λ (n + 1) i) :
    ∃ k₁ ∈ integralSubgroup v.integer n, ∃ k₂ ∈ integralSubgroup v.integer n,
      labelledRep ϖ σ α = k₁ * subsetTorus ϖ S' * k₂ := by
  refine cosetRep_mem_doubleCoset (α.1.2.trans hS'.symm) fun a b hab => ?_
  simp only [liftCoeff, hab, ↓reduceDIte]
  exact hσ _

/-- Each left coset of `K` contains at most one labelled representative, provided that
distinct labels have residues at distance one. -/
theorem labelledRep_unique (hϖ : IsUniformizingElement v ϖ)
    (hinj : ∀ x y, v (σ x - σ y) < 1 → x = y) {i : ℕ} {α β : CosetIndex Λ (n + 1) i}
    {g : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hα : (labelledRep ϖ σ α)⁻¹ * g ∈ integralSubgroup v.integer n)
    (hβ : (labelledRep ϖ σ β)⁻¹ * g ∈ integralSubgroup v.integer n) : α = β := by
  have h : (labelledRep ϖ σ α)⁻¹ * labelledRep ϖ σ β ∈ integralSubgroup v.integer n := by
    have := mul_mem hα (inv_mem hβ)
    rwa [_root_.mul_inv_rev, inv_inv, ← mul_assoc, mul_assoc _ g, mul_inv_cancel,
      mul_one] at this
  obtain ⟨⟨S, hS⟩, w⟩ := α
  obtain ⟨⟨S', hS'⟩, w'⟩ := β
  obtain ⟨rfl, hc⟩ := eq_of_cosetRep_inv_mul_mem hϖ h
  congr
  funext p
  have hp := hc p.1.1 p.1.2 p.2
  simp only [liftCoeff, p.2, ↓reduceDIte] at hp
  exact (hinj _ _ hp).symm

/-- Every element of `K t_S' K` lies in the left coset of a labelled representative,
provided that every integral element is congruent to some label. -/
theorem exists_labelledRep (hϖ : IsUniformizingElement v ϖ)
    (hsurj : ∀ z ∈ v.integer, ∃ x, v (z - σ x) < 1) {i : ℕ} {S' : Finset (Fin (n + 1))}
    (hS' : S'.card = i) {g k₁ k₂ : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hk₁ : k₁ ∈ integralSubgroup v.integer n) (hk₂ : k₂ ∈ integralSubgroup v.integer n)
    (hg : g = k₁ * subsetTorus ϖ S' * k₂) :
    ∃ α : CosetIndex Λ (n + 1) i, (labelledRep ϖ σ α)⁻¹ * g ∈ integralSubgroup v.integer n := by
  obtain ⟨S, hS, c, hc, hcK⟩ := exists_cosetRep_of_mem_doubleCoset hϖ hk₁ hk₂ hg
  choose lab hlab using hsurj
  let w : RadicalPairs S → Λ := fun p => lab (c p.1.1 p.1.2) (hc _ _)
  refine ⟨⟨⟨S, hS.trans hS'⟩, w⟩, ?_⟩
  have hcong : (cosetRep ϖ S (liftCoeff σ S w))⁻¹ * cosetRep ϖ S c ∈
      integralSubgroup v.integer n := by
    refine cosetRep_inv_mul_mem_of_congr hϖ fun a b hab => ?_
    simp only [liftCoeff, hab, ↓reduceDIte]
    exact hlab _ _
  have := mul_mem hcong hcK
  rwa [← mul_assoc, mul_assoc _ (cosetRep ϖ S c), mul_inv_cancel, mul_one] at this

end Labelled

end Langlands.Unramified.MinusculeCosets
