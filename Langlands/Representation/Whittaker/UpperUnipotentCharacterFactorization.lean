import Langlands.Group.GL.Transvection
import Langlands.Representation.Classification.SupercuspidalDerivativeVanishing

/-!
# Characters of the upper unipotent group factor through the first superdiagonal

Every homomorphism `η` from the actual upper-unipotent group `U_(n+1)` of `GL_(n+1)(F)`
into a commutative group is determined by its values on the adjacent elementary matrices:
`η u = ∏ i, η (1 + u_(i,i+1) E_(i,i+1))`. Consequently `η` is trivial on every block
unipotent matrix `[[I_(k+1), Y], [0, I]]` as soon as it is trivial on the adjacent
elementary matrices in position `(k, k+1)`.
-/

noncomputable section

namespace Langlands.Whittaker.UpperUnipotentCharacter

open GeneralLinear
open GeneralLinear.Mirabolic (radical successor successor_first successor_last radicalElement
  radicalElement_first radicalElement_last radicalElement_bottom radicalElement_add
  radicalElement_zero radicalToUpperUnipotent levi levi_conjugate_radicalElement)
open Classification.SupercuspidalDerivativeVanishing (IsBlockUnipotent exists_successor_eq)

universe uF uM

variable {F : Type uF} [Field F]

/-! ## Elementary upper unipotent matrices -/

theorem transvection_apply {k : ℕ} (i j : Fin k) (c : F) (a b : Fin k) :
    Matrix.transvection i j c a b =
      (if a = b then 1 else 0) + (if i = a ∧ j = b then c else 0) := by
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

/-- A transvection strictly above the diagonal, as an actual upper-unipotent element. -/
def upperTransvection {k : ℕ} (i j : Fin k) (hij : i < j) (c : F) : upperUnipotent k F :=
  ⟨transvectionUnit i j (ne_of_lt hij) c, by
    refine ⟨fun a b hba => ?_, fun a => ?_⟩
    · have hba' : b < a := hba
      change Matrix.transvection i j c a b = 0
      rw [transvection_apply]
      have h1 : a ≠ b := ne_of_gt hba'
      have h2 : ¬ (i = a ∧ j = b) := by
        rintro ⟨rfl, rfl⟩
        exact lt_asymm hij hba'
      simp [h1, h2]
    · change Matrix.transvection i j c a a = 1
      rw [transvection_apply]
      have h2 : ¬ (i = a ∧ j = a) := by
        rintro ⟨rfl, h⟩
        exact (ne_of_lt hij) h.symm
      simp [h2]⟩

theorem upperTransvection_zero {k : ℕ} (i j : Fin k) (hij : i < j) :
    upperTransvection i j hij (0 : F) = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact Matrix.transvection_zero i j

/-- The adjacent elementary matrix `1 + x E_(i,i+1)` in `U_(n+1)`. -/
def adjacentUnit {n : ℕ} (i : Fin n) (x : F) : upperUnipotent (n + 1) F :=
  upperTransvection i.castSucc i.succ Fin.castSucc_lt_succ x

theorem adjacentUnit_zero {n : ℕ} (i : Fin n) : adjacentUnit i (0 : F) = 1 :=
  upperTransvection_zero _ _ _

/-- The adjacent elementary matrices form an additive one-parameter subgroup. -/
theorem adjacentUnit_add {n : ℕ} (i : Fin n) (x y : F) :
    adjacentUnit i (x + y) = adjacentUnit i x * adjacentUnit i y := by
  apply Subtype.ext
  apply Units.ext
  exact (Matrix.transvection_mul_transvection_same _ _
    (ne_of_lt Fin.castSucc_lt_succ) x y).symm

/-- The additive character `x ↦ η (1 + x E_(i,i+1))` attached to `η`. -/
def adjacentCharacter {M : Type uM} [CommGroup M] {n : ℕ}
    (η : upperUnipotent (n + 1) F →* M) (i : Fin n) : Multiplicative F →* M where
  toFun x := η (adjacentUnit i x.toAdd)
  map_one' := by
    change η (adjacentUnit i 0) = 1
    rw [adjacentUnit_zero, map_one]
  map_mul' x y := by
    change η (adjacentUnit i (x.toAdd + y.toAdd)) = _
    rw [adjacentUnit_add, map_mul]

@[simp] theorem adjacentCharacter_apply {M : Type uM} [CommGroup M] {n : ℕ}
    (η : upperUnipotent (n + 1) F →* M) (i : Fin n) (x : F) :
    adjacentCharacter η i (Multiplicative.ofAdd x) = η (adjacentUnit i x) := rfl

/-! ## The successor embedding on upper unipotent matrices -/

theorem successor_mem_upperUnipotent {n : ℕ} (g : mirabolic n F)
    (hg : g.val ∈ upperUnipotent (n + 1) F) :
    (successor g).val ∈ upperUnipotent (n + 2) F := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · have hba' : b < a := hba
    change (successor g).val.val a b = 0
    clear hba
    induction a using Fin.lastCases with
    | last =>
      rw [(successor g).property b]
      simp [ne_of_lt hba']
    | cast a =>
      induction b using Fin.lastCases with
      | last => exact absurd hba' (not_lt_of_ge (Fin.le_last _))
      | cast b =>
        rw [successor_first]
        exact hg.1 (Fin.castSucc_lt_castSucc_iff.mp hba')
  · change (successor g).val.val a a = 1
    induction a using Fin.lastCases with
    | last =>
      rw [(successor g).property (Fin.last (n + 1))]
      simp
    | cast a =>
      rw [successor_first]
      exact hg.2 a

/-- The successor embedding `g ↦ diag(g, 1)`, restricted to upper unipotent matrices. -/
def successorUnipotent (n : ℕ) : upperUnipotent (n + 1) F →* upperUnipotent (n + 2) F :=
  ((mirabolic (n + 1) F).subtype.comp
      (successor.comp (Subgroup.inclusion (upperUnipotent_le_mirabolic (n := n) (F := F))))).codRestrict
    (upperUnipotent (n + 2) F) (fun g => successor_mem_upperUnipotent _ g.property)

theorem successorUnipotent_val {n : ℕ} (g : upperUnipotent (n + 1) F) :
    (successorUnipotent n g).val = (levi g.val).val := rfl

@[simp] theorem successorUnipotent_first {n : ℕ} (g : upperUnipotent (n + 1) F)
    (i j : Fin (n + 1)) :
    (successorUnipotent n g).val.val i.castSucc j.castSucc = g.val.val i j :=
  successor_first (⟨g.val, upperUnipotent_le_mirabolic g.property⟩ : mirabolic n F) i j

@[simp] theorem successorUnipotent_last {n : ℕ} (g : upperUnipotent (n + 1) F)
    (i : Fin (n + 1)) :
    (successorUnipotent n g).val.val i.castSucc (Fin.last (n + 1)) = 0 :=
  successor_last (⟨g.val, upperUnipotent_le_mirabolic g.property⟩ : mirabolic n F) i

@[simp] theorem successorUnipotent_bottom {n : ℕ} (g : upperUnipotent (n + 1) F)
    (j : Fin (n + 2)) :
    (successorUnipotent n g).val.val (Fin.last (n + 1)) j =
      if j = Fin.last (n + 1) then 1 else 0 :=
  (successor (⟨g.val, upperUnipotent_le_mirabolic g.property⟩ : mirabolic n F)).property j

/-- The successor of an adjacent elementary matrix is adjacent in the same position. -/
theorem successorUnipotent_adjacentUnit {n : ℕ} (i : Fin n) (x : F) :
    successorUnipotent n (adjacentUnit i x) = adjacentUnit i.castSucc x := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  change (successorUnipotent n (adjacentUnit i x)).val.val a b =
    Matrix.transvection i.castSucc.castSucc i.castSucc.succ x a b
  rw [transvection_apply, Fin.succ_castSucc]
  induction a using Fin.lastCases with
  | last =>
    rw [successorUnipotent_bottom]
    by_cases hb : b = Fin.last (n + 1)
    · subst hb
      simp
    · simp [hb, Ne.symm hb]
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      rw [successorUnipotent_last]
      simp [Fin.castSucc_ne_last]
    | cast b =>
      rw [successorUnipotent_first]
      change Matrix.transvection i.castSucc i.succ x a b = _
      rw [transvection_apply]
      simp only [Fin.castSucc_inj]

/-! ## Radical columns -/

/-- The radical column matrix `[[I, c], [0, 1]]` as an element of `U_(n+2)`. -/
def radicalUnipotent (n : ℕ) (c : Fin (n + 1) → F) : upperUnipotent (n + 2) F :=
  radicalToUpperUnipotent (radicalElement c)

theorem radicalUnipotent_val (n : ℕ) (c : Fin (n + 1) → F) :
    (radicalUnipotent n c).val = (radicalElement c).val.val := rfl

theorem radicalUnipotent_add (n : ℕ) (c d : Fin (n + 1) → F) :
    radicalUnipotent n (c + d) = radicalUnipotent n c * radicalUnipotent n d := by
  unfold radicalUnipotent
  rw [radicalElement_add, map_mul]

theorem radicalUnipotent_zero (n : ℕ) : radicalUnipotent n (0 : Fin (n + 1) → F) = 1 := by
  unfold radicalUnipotent
  rw [radicalElement_zero, map_one]

/-- The last radical coordinate gives the last adjacent elementary matrix. -/
theorem radicalUnipotent_single_last (n : ℕ) (x : F) :
    radicalUnipotent n (Pi.single (Fin.last n) x) = adjacentUnit (Fin.last n) x := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  change (radicalElement (Pi.single (Fin.last n) x)).val.val.val a b =
    Matrix.transvection (Fin.last n).castSucc (Fin.last n).succ x a b
  rw [transvection_apply, Fin.succ_last]
  induction b using Fin.lastCases with
  | last =>
    induction a using Fin.lastCases with
    | last =>
      rw [radicalElement_bottom]
      simp [Fin.castSucc_ne_last]
    | cast a =>
      rw [radicalElement_last]
      by_cases ha : a = Fin.last n
      · subst ha
        simp [Fin.castSucc_ne_last]
      · have h1 : ¬ ((Fin.last n).castSucc = a.castSucc) := fun h =>
          ha (Fin.castSucc_injective _ h).symm
        simp [ha, h1, Fin.castSucc_ne_last]
  | cast b =>
    rw [radicalElement_first]
    simp [(Fin.castSucc_ne_last b).symm]

private theorem commutator_eq_one {M : Type uM} [CommGroup M] (a b : M) :
    a⁻¹ * (b * a * b⁻¹) = 1 := by
  rw [mul_comm b a, mul_inv_cancel_right, inv_mul_cancel]

/-- A radical column supported strictly above the last row is a commutator. -/
theorem character_radicalUnipotent_single_castSucc {M : Type uM} [CommGroup M] (n : ℕ)
    (η : upperUnipotent (n + 2) F →* M) (k : Fin n) (x : F) :
    η (radicalUnipotent n (Pi.single k.castSucc x)) = 1 := by
  let g : upperUnipotent (n + 1) F :=
    upperTransvection k.castSucc (Fin.last n) (Fin.castSucc_lt_last k) x
  let v : Fin (n + 1) → F := Pi.single (Fin.last n) 1
  have hmul : g.val.val.mulVec v = v + Pi.single k.castSucc x := by
    change (Matrix.transvection k.castSucc (Fin.last n) x).mulVec v = _
    rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
    ext a
    simp [v, Pi.single_apply]
  have hconj := levi_conjugate_radicalElement g.val v
  rw [hmul, radicalElement_add, Subgroup.coe_mul] at hconj
  have hB := eq_inv_mul_of_mul_eq hconj.symm
  have hcomm : radicalUnipotent n (Pi.single k.castSucc x) =
      (radicalUnipotent n v)⁻¹ *
        (successorUnipotent n g * radicalUnipotent n v * (successorUnipotent n g)⁻¹) := by
    apply Subtype.ext
    have h2 := congrArg Subtype.val hB
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2 ⊢
    exact h2
  rw [hcomm, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact commutator_eq_one _ _

/-- On radical columns a character only sees the last coordinate. -/
theorem character_radicalUnipotent {M : Type uM} [CommGroup M] (n : ℕ)
    (η : upperUnipotent (n + 2) F →* M) (c : Fin (n + 1) → F) :
    η (radicalUnipotent n c) = η (adjacentUnit (Fin.last n) (c (Fin.last n))) := by
  let φ : (Fin (n + 1) → F) →+ Additive M :=
    { toFun := fun v => Additive.ofMul (η (radicalUnipotent n v))
      map_zero' := by
        rw [radicalUnipotent_zero, map_one]
        rfl
      map_add' := fun v w => by
        rw [radicalUnipotent_add, map_mul]
        rfl }
  have hφ : φ c = φ (Pi.single (Fin.last n) (c (Fin.last n))) := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum, Fin.sum_univ_castSucc]
    have hz : ∀ k : Fin n, φ (Pi.single k.castSucc (c k.castSucc)) = 0 := by
      intro k
      change Additive.ofMul (η (radicalUnipotent n (Pi.single k.castSucc (c k.castSucc)))) = 0
      rw [character_radicalUnipotent_single_castSucc]
      rfl
    simp only [hz, Finset.sum_const_zero, zero_add]
  have h := congrArg Additive.toMul hφ
  change η (radicalUnipotent n c) =
    η (radicalUnipotent n (Pi.single (Fin.last n) (c (Fin.last n)))) at h
  rw [h, radicalUnipotent_single_last]

/-! ## Decomposition `U_(n+2) = V_(n+2) ⋊ U_(n+1)` -/

/-- Every element of `U_(n+2)` is a radical column times the successor of an element of
`U_(n+1)` with the same upper-left entries. -/
theorem exists_radical_mul_successor (n : ℕ) (u : upperUnipotent (n + 2) F) :
    ∃ h : upperUnipotent (n + 1) F,
      (∀ i j : Fin (n + 1), h.val.val i j = u.val.val i.castSucc j.castSucc) ∧
      u = radicalUnipotent n (fun i => u.val.val i.castSucc (Fin.last (n + 1))) *
        successorUnipotent n h := by
  let c : Fin (n + 1) → F := fun i => u.val.val i.castSucc (Fin.last (n + 1))
  let um : mirabolic (n + 1) F := ⟨u.val, upperUnipotent_le_mirabolic u.property⟩
  let r : mirabolic (n + 1) F := (radicalElement c : radical (n + 1) F)
  let r' : mirabolic (n + 1) F := (radicalElement (-c) : radical (n + 1) F)
  have hrr' : r * r' = 1 := by
    have h := radicalElement_add c (-c)
    rw [add_neg_cancel, radicalElement_zero] at h
    exact congrArg Subtype.val h.symm
  let s := r' * um
  have hlast : ∀ j : Fin (n + 1), u.val.val (Fin.last (n + 1)) j.castSucc = 0 :=
    fun j => u.property.1 (Fin.castSucc_lt_last j)
  have hs : ∀ (i : Fin (n + 1)) (j : Fin (n + 2)),
      s.val.val i.castSucc j =
        u.val.val i.castSucc j + (-c i) * u.val.val (Fin.last (n + 1)) j := by
    intro i j
    change ((radicalElement (-c)).val.val.val * u.val.val) i.castSucc j = _
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [radicalElement_first, radicalElement_last, Pi.neg_apply, ite_mul, one_mul,
      zero_mul, Fin.castSucc_inj, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hs' : ∀ i j : Fin (n + 1), s.val.val i.castSucc j.castSucc =
      u.val.val i.castSucc j.castSucc := by
    intro i j
    rw [hs, hlast j, mul_zero, add_zero]
  have hcol : ∀ i : Fin (n + 1), s.val.val i.castSucc (Fin.last (n + 1)) = 0 := by
    intro i
    rw [hs, u.property.2 (Fin.last (n + 1)), mul_one]
    exact add_neg_cancel _
  have hrow : ∀ j : Fin (n + 1),
      s.val.val (Fin.last n).castSucc j.castSucc = if j = Fin.last n then 1 else 0 := by
    intro j
    rw [hs']
    by_cases hj : j = Fin.last n
    · subst hj
      simp only [↓reduceIte]
      exact u.property.2 (Fin.last n).castSucc
    · simp only [hj, ↓reduceIte]
      exact u.property.1 (Fin.castSucc_lt_castSucc_iff.mpr
        (lt_of_le_of_ne (Fin.le_last j) hj))
  obtain ⟨h, hh⟩ := exists_successor_eq s hcol hrow
  have hent : ∀ i j : Fin (n + 1), h.val.val i j = u.val.val i.castSucc j.castSucc := by
    intro i j
    rw [← successor_first h i j, hh, hs']
  have hU : h.val ∈ upperUnipotent (n + 1) F := by
    refine ⟨fun a b hba => ?_, fun a => ?_⟩
    · have hba' : b < a := hba
      change h.val.val a b = 0
      rw [hent]
      exact u.property.1 (Fin.castSucc_lt_castSucc_iff.mpr hba')
    · change h.val.val a a = 1
      rw [hent]
      exact u.property.2 _
  refine ⟨⟨h.val, hU⟩, hent, ?_⟩
  apply Subtype.ext
  have hum : um = r * successor h := by
    rw [hh]
    change um = r * (r' * um)
    rw [← mul_assoc, hrr', one_mul]
  have hval := congrArg Subtype.val hum
  exact hval

/-! ## The factorization -/

/-- A character of `U_(n+1)` with values in a commutative group is the product of its
values on the adjacent elementary matrices with the same first-superdiagonal entries. -/
theorem eq_prod_adjacentUnit {M : Type uM} [CommGroup M] :
    ∀ (n : ℕ) (η : upperUnipotent (n + 1) F →* M) (u : upperUnipotent (n + 1) F),
      η u = ∏ i : Fin n, η (adjacentUnit i (u.val.val i.castSucc i.succ))
  | 0, η, u => by
      have hu : u = 1 := by
        apply Subtype.ext
        apply Units.ext
        apply Matrix.ext
        intro i j
        have hij : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
        subst hij
        change u.val.val i i = (1 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) F) i i
        rw [Matrix.one_apply_eq]
        exact u.property.2 i
      rw [hu, map_one, Fin.prod_univ_zero]
  | n + 1, η, u => by
      obtain ⟨h, hent, hdec⟩ := exists_radical_mul_successor n u
      have hsplit : η u = η (radicalUnipotent n
            (fun i => u.val.val i.castSucc (Fin.last (n + 1)))) *
          (η.comp (successorUnipotent n)) h := by
        conv_lhs => rw [hdec]
        rw [map_mul]
        rfl
      rw [hsplit, character_radicalUnipotent,
        eq_prod_adjacentUnit n (η.comp (successorUnipotent n)) h, Fin.prod_univ_castSucc]
      conv_lhs => rw [mul_comm]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [MonoidHom.comp_apply, successorUnipotent_adjacentUnit, hent, Fin.succ_castSucc]

/-! ## Block unipotent matrices -/

/-- A block unipotent matrix `[[I_(k+1), Y], [0, I]]` has vanishing first-superdiagonal
entries outside position `(k, k+1)`. -/
theorem isBlockUnipotent_adjacent_eq_zero {n k : ℕ} {g : GeneralLinear (n + 1) F}
    (hg : IsBlockUnipotent (k + 1) g) (i : Fin n) (hi : i.val ≠ k) :
    g.val i.castSucc i.succ = 0 := by
  have hcond : i.succ.val < k + 1 ∨ k + 1 ≤ i.castSucc.val := by
    rcases Nat.lt_or_gt_of_ne hi with h | h
    · left
      simp only [Fin.val_succ]
      omega
    · right
      simp only [Fin.val_castSucc]
      omega
  rw [hg _ _ hcond]
  simp [ne_of_lt (Fin.castSucc_lt_succ (i := i))]

/-- A character trivial on the adjacent elementary matrices in position `(k, k+1)` is
trivial on every block unipotent matrix `[[I_(k+1), Y], [0, I]]`. -/
theorem character_eq_one_of_isBlockUnipotent {M : Type uM} [CommGroup M] {n : ℕ}
    (η : upperUnipotent (n + 1) F →* M) (k : Fin n)
    (hk : ∀ x : F, η (adjacentUnit k x) = 1) (u : upperUnipotent (n + 1) F)
    (hu : IsBlockUnipotent (k.val + 1) u.val) : η u = 1 := by
  rw [eq_prod_adjacentUnit n η u]
  apply Finset.prod_eq_one
  intro i _
  by_cases hik : i = k
  · subst hik
    exact hk _
  · rw [isBlockUnipotent_adjacent_eq_zero hu i (fun h => hik (Fin.ext h)), adjacentUnit_zero,
      map_one]

/-! ## Diagonal conjugation -/

/-- The invertible diagonal matrix with diagonal entries `d`. -/
def diagonalUnit {m : ℕ} (d : Fin m → Fˣ) : GeneralLinear m F where
  val := Matrix.diagonal fun i => (d i : F)
  inv := Matrix.diagonal fun i => (((d i)⁻¹ : Fˣ) : F)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

/-- Conjugation by a diagonal matrix multiplies the entry `(i, j)` by `d_i d_j⁻¹`. -/
theorem diagonalUnit_conj_apply {m : ℕ} (d : Fin m → Fˣ) (g : GeneralLinear m F)
    (i j : Fin m) :
    (diagonalUnit d * g * (diagonalUnit d)⁻¹).val i j =
      (d i : F) * g.val i j * (((d j)⁻¹ : Fˣ) : F) := by
  change (Matrix.diagonal (fun i => (d i : F)) * g.val *
    Matrix.diagonal (fun i => (((d i)⁻¹ : Fˣ) : F))) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem diagonalUnit_conj_mem {m : ℕ} (d : Fin m → Fˣ) {g : GeneralLinear m F}
    (hg : g ∈ upperUnipotent m F) :
    diagonalUnit d * g * (diagonalUnit d)⁻¹ ∈ upperUnipotent m F := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · have hba' : b < a := hba
    change (diagonalUnit d * g * (diagonalUnit d)⁻¹).val a b = 0
    rw [diagonalUnit_conj_apply, hg.1 hba', mul_zero, zero_mul]
  · change (diagonalUnit d * g * (diagonalUnit d)⁻¹).val a a = 1
    rw [diagonalUnit_conj_apply, hg.2 a, mul_one, Units.mul_inv]

/-- Conjugation `u ↦ t u t⁻¹` by the diagonal matrix `t = diag(d)` on `U_m`. -/
def diagonalConj {m : ℕ} (d : Fin m → Fˣ) : upperUnipotent m F →* upperUnipotent m F :=
  ((MulAut.conj (diagonalUnit d)).toMonoidHom.comp (upperUnipotent m F).subtype).codRestrict
    (upperUnipotent m F) (fun g => diagonalUnit_conj_mem d g.property)

theorem diagonalConj_val {m : ℕ} (d : Fin m → Fˣ) (u : upperUnipotent m F) :
    (diagonalConj d u).val = diagonalUnit d * u.val * (diagonalUnit d)⁻¹ := rfl

/-- The tail products `d_j = ∏_(k ≥ j) a_k`, so that `d_i = a_i d_(i+1)`. -/
def tailProduct {n : ℕ} (a : Fin n → Fˣ) (j : Fin (n + 1)) : Fˣ :=
  ∏ k : Fin n, if j.val ≤ k.val then a k else 1

theorem tailProduct_castSucc {n : ℕ} (a : Fin n → Fˣ) (i : Fin n) :
    tailProduct a i.castSucc = a i * tailProduct a i.succ := by
  unfold tailProduct
  have h : ∀ k : Fin n, (if i.castSucc.val ≤ k.val then a k else 1) =
      (if k = i then a k else 1) * (if i.succ.val ≤ k.val then a k else 1) := by
    intro k
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases hk : k = i
    · subst hk
      simp
    · have hne : k.val ≠ i.val := fun h => hk (Fin.ext h)
      by_cases hle : i.val ≤ k.val
      · have h1 : i.val + 1 ≤ k.val := by omega
        simp [hk, hle, h1]
      · have h1 : ¬ (i.val + 1 ≤ k.val) := by omega
        simp [hk, hle, h1]
  rw [Finset.prod_congr rfl (fun k _ => h k), Finset.prod_mul_distrib]
  simp

/-- Conjugation by `diag(d)` with tail products of `a` multiplies the first-superdiagonal
entry `(i, i+1)` by `a_i`. -/
theorem diagonalConj_tailProduct_adjacent {n : ℕ} (a : Fin n → Fˣ)
    (u : upperUnipotent (n + 1) F) (i : Fin n) :
    (diagonalConj (tailProduct a) u).val.val i.castSucc i.succ =
      (a i : F) * u.val.val i.castSucc i.succ := by
  rw [diagonalConj_val, diagonalUnit_conj_apply, tailProduct_castSucc]
  calc ((a i * tailProduct a i.succ : Fˣ) : F) * u.val.val i.castSucc i.succ *
        (((tailProduct a i.succ)⁻¹ : Fˣ) : F)
      = (a i : F) * u.val.val i.castSucc i.succ *
          ((tailProduct a i.succ : F) * (((tailProduct a i.succ)⁻¹ : Fˣ) : F)) := by
        push_cast
        ring
    _ = (a i : F) * u.val.val i.castSucc i.succ := by
        rw [Units.mul_inv, mul_one]

end Langlands.Whittaker.UpperUnipotentCharacter
