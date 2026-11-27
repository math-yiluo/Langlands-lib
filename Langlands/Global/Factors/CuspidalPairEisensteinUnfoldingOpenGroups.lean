import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingCellIntegral

/-! # The open cell as a semidirect product

The adelic upper unitriangular group `N₀(𝔸)` of `GL_N`, `N = r + t + 2`, is the semidirect
product of the normal radical `U'(𝔸) = {u'(Y)}` of the parabolic with exchanged block sizes
`(t + 1, r + 1)` and of the block diagonal group `N_(t+1)(𝔸) × N_(r+1)(𝔸)`. This module gives the
three homomorphisms of this decomposition, their continuity, their compatibility with rational
points and the stabilizer `Λ_(J₀)(F)` of the open cell. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open NumberField MeasureTheory Matrix

namespace Langlands.Global.CuspidalPairEisenstein.Unfolding

open RankinSelbergGlobal RowEchelon PrimitiveAdelicHeight

section Blocks

variable {R : Type*} [CommRing R] (r t : ℕ)

/-- The coordinates of the exchanged blocks `(t + 1, r + 1)` of `Fin (r + t + 2)`. -/
def swapBlocks : Fin (t + 1) ⊕ Fin (r + 1) ≃ Fin (r + t + 2) :=
  finSumFinEquiv.trans (finCongr (by omega))

theorem swapBlocks_inl_val (i : Fin (t + 1)) : (swapBlocks r t (Sum.inl i) : ℕ) = i := by
  simp [swapBlocks]

theorem swapBlocks_inr_val (i : Fin (r + 1)) : (swapBlocks r t (Sum.inr i) : ℕ) = t + 1 + i := by
  simp [swapBlocks]

variable {r t}

/-- A matrix in the exchanged block coordinates. -/
def toSum (x : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) R) :
    Matrix (Fin (t + 1) ⊕ Fin (r + 1)) (Fin (t + 1) ⊕ Fin (r + 1)) R :=
  x.submatrix (swapBlocks r t) (swapBlocks r t)

/-- A matrix in exchanged block coordinates, back in the standard coordinates. -/
def ofSum (x : Matrix (Fin (t + 1) ⊕ Fin (r + 1)) (Fin (t + 1) ⊕ Fin (r + 1)) R) :
    Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) R :=
  x.submatrix (swapBlocks r t).symm (swapBlocks r t).symm

omit [CommRing R] in
theorem toSum_ofSum (x : Matrix (Fin (t + 1) ⊕ Fin (r + 1)) (Fin (t + 1) ⊕ Fin (r + 1)) R) :
    toSum (ofSum x) = x := by
  ext i j
  simp [toSum, ofSum]

omit [CommRing R] in
theorem ofSum_toSum (x : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) R) : ofSum (toSum x) = x := by
  ext i j
  simp [toSum, ofSum]

theorem toSum_mul (x y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) R) :
    toSum (x * y) = toSum x * toSum y := by
  rw [toSum, toSum, toSum, submatrix_mul_equiv]

theorem toSum_one : toSum (1 : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) R) = 1 :=
  submatrix_one_equiv _

omit [CommRing R] in
theorem toSum_injective : Function.Injective (toSum (R := R) (r := r) (t := t)) := fun x y h => by
  rw [← ofSum_toSum x, h, ofSum_toSum]

theorem toSum_toBlocks₂₁ {x : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) R}
    (hx : IsUnitriangular x) : (toSum x).toBlocks₂₁ = 0 := by
  ext i j
  change x (swapBlocks r t (Sum.inr i)) (swapBlocks r t (Sum.inl j)) = 0
  apply hx.1
  dsimp only [id]
  rw [Fin.lt_def, swapBlocks_inl_val, swapBlocks_inr_val]
  omega

theorem toSum_eq_fromBlocks {x : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) R}
    (hx : IsUnitriangular x) :
    toSum x = fromBlocks (toSum x).toBlocks₁₁ (toSum x).toBlocks₁₂ 0 (toSum x).toBlocks₂₂ := by
  rw [← toSum_toBlocks₂₁ hx, fromBlocks_toBlocks]

theorem isUnitriangular_toBlocks₁₁ {x : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) R}
    (hx : IsUnitriangular x) : IsUnitriangular (toSum x).toBlocks₁₁ := by
  refine ⟨fun i j hji => hx.1 ?_, fun i => hx.2 _⟩
  dsimp only [id] at hji ⊢
  rw [Fin.lt_def, swapBlocks_inl_val, swapBlocks_inl_val]
  exact hji

theorem isUnitriangular_toBlocks₂₂ {x : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) R}
    (hx : IsUnitriangular x) : IsUnitriangular (toSum x).toBlocks₂₂ := by
  refine ⟨fun i j hji => hx.1 ?_, fun i => hx.2 _⟩
  dsimp only [id] at hji ⊢
  rw [Fin.lt_def, swapBlocks_inr_val, swapBlocks_inr_val]
  have : (j : ℕ) < i := hji
  omega

/-- Block upper triangular matrices with unitriangular diagonal blocks are unitriangular. -/
theorem isUnitriangular_ofSum {A : Matrix (Fin (t + 1)) (Fin (t + 1)) R}
    {B : Matrix (Fin (t + 1)) (Fin (r + 1)) R} {D : Matrix (Fin (r + 1)) (Fin (r + 1)) R}
    (hA : IsUnitriangular A) (hD : IsUnitriangular D) :
    IsUnitriangular (ofSum (fromBlocks A B 0 D)) := by
  have key : ∀ k : Fin (r + t + 2), ∃ s, swapBlocks r t s = k := fun k =>
    ⟨(swapBlocks r t).symm k, Equiv.apply_symm_apply _ _⟩
  refine ⟨fun k l hlk => ?_, fun k => ?_⟩
  · obtain ⟨s, rfl⟩ := key k
    obtain ⟨s', rfl⟩ := key l
    change fromBlocks A B 0 D ((swapBlocks r t).symm (swapBlocks r t s))
      ((swapBlocks r t).symm (swapBlocks r t s')) = 0
    simp only [Equiv.symm_apply_apply]
    have hlk' : (swapBlocks r t s' : ℕ) < swapBlocks r t s := hlk
    clear hlk
    rcases s with i | i <;> rcases s' with j | j
    · rw [swapBlocks_inl_val, swapBlocks_inl_val] at hlk'
      exact hA.1 (Fin.lt_def.mpr hlk')
    · rw [swapBlocks_inl_val, swapBlocks_inr_val] at hlk'
      omega
    · rfl
    · rw [swapBlocks_inr_val, swapBlocks_inr_val] at hlk'
      exact hD.1 (show j < i from Fin.lt_def.mpr (by omega))
  · obtain ⟨s, rfl⟩ := key k
    change fromBlocks A B 0 D ((swapBlocks r t).symm (swapBlocks r t s))
      ((swapBlocks r t).symm (swapBlocks r t s)) = 1
    simp only [Equiv.symm_apply_apply]
    rcases s with i | i
    · exact hA.2 i
    · exact hD.2 i

omit [CommRing R] in
theorem continuous_toBlocks₁₁ {X : Type*} [TopologicalSpace X] [TopologicalSpace R]
    {A : X → Matrix (Fin (t + 1) ⊕ Fin (r + 1)) (Fin (t + 1) ⊕ Fin (r + 1)) R}
    (hA : Continuous A) : Continuous fun x => (A x).toBlocks₁₁ :=
  hA.matrix_submatrix _ _

omit [CommRing R] in
theorem continuous_toBlocks₁₂ {X : Type*} [TopologicalSpace X] [TopologicalSpace R]
    {A : X → Matrix (Fin (t + 1) ⊕ Fin (r + 1)) (Fin (t + 1) ⊕ Fin (r + 1)) R}
    (hA : Continuous A) : Continuous fun x => (A x).toBlocks₁₂ :=
  hA.matrix_submatrix _ _

omit [CommRing R] in
theorem continuous_toBlocks₂₂ {X : Type*} [TopologicalSpace X] [TopologicalSpace R]
    {A : X → Matrix (Fin (t + 1) ⊕ Fin (r + 1)) (Fin (t + 1) ⊕ Fin (r + 1)) R}
    (hA : Continuous A) : Continuous fun x => (A x).toBlocks₂₂ :=
  hA.matrix_submatrix _ _

end Blocks

section Points

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

theorem toMat_ofUnitriangular_val (M : {M : Matrix (Fin n) (Fin n) (Adeles F) //
    IsUnitriangular M}) :
    ((toMat F n (ofUnitriangular F n M) : Matrix.GeneralLinearGroup (Fin n) (Adeles F)) :
      Matrix (Fin n) (Fin n) (Adeles F)) = M.1 :=
  toMat_ofUnitriangular F n M

theorem ofUnitriangular_eq_iff (M : {M : Matrix (Fin n) (Fin n) (Adeles F) // IsUnitriangular M})
    (x : unipotentAdelic F n) :
    ofUnitriangular F n M = x ↔ M.1 = (toMat F n x : Matrix (Fin n) (Fin n) (Adeles F)) := by
  constructor
  · rintro rfl
    exact (toMat_ofUnitriangular F n M).symm
  · intro h
    apply toMat_injective
    apply Units.ext
    rw [toMat_ofUnitriangular, h]

theorem ofUnitriangular_mk_eq_iff (M : Matrix (Fin n) (Fin n) (Adeles F)) (hM : IsUnitriangular M)
    (x : unipotentAdelic F n) :
    ofUnitriangular F n ⟨M, hM⟩ = x ↔ M = (toMat F n x : Matrix (Fin n) (Fin n) (Adeles F)) :=
  ofUnitriangular_eq_iff F n ⟨M, hM⟩ x

theorem ofUnitriangular_mul (M M' : {M : Matrix (Fin n) (Fin n) (Adeles F) // IsUnitriangular M}) :
    ofUnitriangular F n ⟨M.1 * M'.1, M.2.mul M'.2⟩ =
      ofUnitriangular F n M * ofUnitriangular F n M' := by
  rw [ofUnitriangular_eq_iff, map_mul, Units.val_mul, toMat_ofUnitriangular,
    toMat_ofUnitriangular]

theorem ofUnitriangular_one :
    ofUnitriangular F n ⟨1, isUnitriangular_one⟩ = 1 := by
  rw [ofUnitriangular_eq_iff, map_one, Units.val_one]

theorem ofUnitriangular_toMat (x : unipotentAdelic F n) :
    ofUnitriangular F n ⟨toMat F n x, isUnitriangular_toMat F n x⟩ = x := by
  rw [ofUnitriangular_eq_iff]

theorem continuous_toMat_val :
    Continuous fun x : unipotentAdelic F n =>
      ((toMat F n x : Matrix.GeneralLinearGroup (Fin n) (Adeles F)) :
        Matrix (Fin n) (Fin n) (Adeles F)) :=
  Units.continuous_val.comp (continuous_toMat F n)

end Points

section Semidirect

variable (F : Type u) [Field F] [NumberField F] (r t : ℕ)

/-- The radical `U'(𝔸)` in additive matrix coordinates. -/
abbrev Radical := Multiplicative (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F))

/-- The block diagonal group `N_(t+1)(𝔸) × N_(r+1)(𝔸)` of the exchanged blocks. -/
abbrev LeviPart := unipotentAdelic F (t + 1) × unipotentAdelic F (r + 1)

theorem toSum_openCellUnipotent (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    toSum (openCellUnipotent F r t Y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) =
      fromBlocks 1 Y 0 1 := by
  ext s s'
  change (openCellUnipotent F r t Y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F))
    (swapBlocks r t s) (swapBlocks r t s') = _
  rw [openCellUnipotent_apply]
  rcases s with i | i <;> rcases s' with j | j
  · have h1 : (Fin.cast (by omega) (swapBlocks r t (Sum.inl i)) : Fin (t + 1 + (r + 1))) =
        i.castAdd (r + 1) := Fin.ext (by simp [swapBlocks])
    have h2 : (Fin.cast (by omega) (swapBlocks r t (Sum.inl j)) : Fin (t + 1 + (r + 1))) =
        j.castAdd (r + 1) := Fin.ext (by simp [swapBlocks])
    rw [h1, h2, Shahidi.upper_first_first]
    simp [Matrix.one_apply]
  · have h1 : (Fin.cast (by omega) (swapBlocks r t (Sum.inl i)) : Fin (t + 1 + (r + 1))) =
        i.castAdd (r + 1) := Fin.ext (by simp [swapBlocks])
    have h2 : (Fin.cast (by omega) (swapBlocks r t (Sum.inr j)) : Fin (t + 1 + (r + 1))) =
        j.natAdd (t + 1) := Fin.ext (by simp [swapBlocks])
    rw [h1, h2, Shahidi.upper_first_second]
    simp
  · have h1 : (Fin.cast (by omega) (swapBlocks r t (Sum.inr i)) : Fin (t + 1 + (r + 1))) =
        i.natAdd (t + 1) := Fin.ext (by simp [swapBlocks])
    have h2 : (Fin.cast (by omega) (swapBlocks r t (Sum.inl j)) : Fin (t + 1 + (r + 1))) =
        j.castAdd (r + 1) := Fin.ext (by simp [swapBlocks])
    rw [h1, h2, Shahidi.upper_second_first]
    simp
  · have h1 : (Fin.cast (by omega) (swapBlocks r t (Sum.inr i)) : Fin (t + 1 + (r + 1))) =
        i.natAdd (t + 1) := Fin.ext (by simp [swapBlocks])
    have h2 : (Fin.cast (by omega) (swapBlocks r t (Sum.inr j)) : Fin (t + 1 + (r + 1))) =
        j.natAdd (t + 1) := Fin.ext (by simp [swapBlocks])
    rw [h1, h2, Shahidi.upper_second_second]
    simp [Matrix.one_apply]

theorem openCellUnipotent_eq_ofSum (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    (openCellUnipotent F r t Y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) =
      ofSum (fromBlocks 1 Y 0 1) := by
  rw [← toSum_openCellUnipotent, ofSum_toSum]

theorem isUnitriangular_openCellUnipotent (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    IsUnitriangular (openCellUnipotent F r t Y :
      Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) := by
  rw [openCellUnipotent_eq_ofSum]
  exact isUnitriangular_ofSum isUnitriangular_one isUnitriangular_one

theorem openCellUnipotent_add (Y Y' : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    openCellUnipotent F r t (Y + Y') = openCellUnipotent F r t Y * openCellUnipotent F r t Y' := by
  rw [openCellUnipotent, openCellUnipotent, openCellUnipotent, Shahidi.intertwiningUnipotent_add,
    map_mul]

theorem openCellUnipotent_zero : openCellUnipotent F r t 0 = 1 := by
  rw [openCellUnipotent, Shahidi.intertwiningUnipotent_zero, map_one]

/-- The inclusion `Y ↦ u'(Y)` of the radical into `N₀(𝔸)`. -/
def radicalHom : Radical F r t →* unipotentAdelic F (r + t + 2) where
  toFun Y := ofUnitriangular F _ ⟨_, isUnitriangular_openCellUnipotent F r t Y.toAdd⟩
  map_one' := by
    change ofUnitriangular F _ ⟨_, isUnitriangular_openCellUnipotent F r t 0⟩ = 1
    rw [ofUnitriangular_mk_eq_iff, MonoidHom.map_one, Units.val_one, openCellUnipotent_zero,
      Units.val_one]
  map_mul' Y Y' := by
    change ofUnitriangular F _ ⟨_, isUnitriangular_openCellUnipotent F r t (Y.toAdd + Y'.toAdd)⟩ =
      ofUnitriangular F _ ⟨_, isUnitriangular_openCellUnipotent F r t Y.toAdd⟩ *
        ofUnitriangular F _ ⟨_, isUnitriangular_openCellUnipotent F r t Y'.toAdd⟩
    rw [ofUnitriangular_mk_eq_iff, MonoidHom.map_mul, Units.val_mul, toMat_ofUnitriangular,
      toMat_ofUnitriangular, openCellUnipotent_add, Units.val_mul]

theorem toMat_radicalHom (Y : Radical F r t) :
    (toMat F _ (radicalHom F r t Y) : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) =
      openCellUnipotent F r t Y.toAdd :=
  toMat_ofUnitriangular F _ _

theorem isUnitriangular_ofSum_diag (A : unipotentAdelic F (t + 1)) (B : unipotentAdelic F (r + 1)) :
    IsUnitriangular (ofSum (fromBlocks (toMat F _ A : Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F))
      0 0 (toMat F _ B : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)))) :=
  isUnitriangular_ofSum (isUnitriangular_toMat F _ A) (isUnitriangular_toMat F _ B)

/-- The block diagonal inclusion `(A, B) ↦ diag(A, B)` into `N₀(𝔸)`. -/
def leviHom : LeviPart F r t →* unipotentAdelic F (r + t + 2) where
  toFun m := ofUnitriangular F _ ⟨_, isUnitriangular_ofSum_diag F r t m.1 m.2⟩
  map_one' := by
    rw [ofUnitriangular_eq_iff, MonoidHom.map_one, Units.val_one]
    apply toSum_injective
    rw [toSum_ofSum, toSum_one, Prod.fst_one, Prod.snd_one, MonoidHom.map_one, MonoidHom.map_one,
      Units.val_one, Units.val_one, fromBlocks_one]
  map_mul' m m' := by
    rw [ofUnitriangular_eq_iff, MonoidHom.map_mul, Units.val_mul, toMat_ofUnitriangular,
      toMat_ofUnitriangular]
    apply toSum_injective
    rw [toSum_mul, toSum_ofSum, toSum_ofSum, toSum_ofSum, fromBlocks_multiply, Prod.fst_mul,
      Prod.snd_mul, MonoidHom.map_mul, MonoidHom.map_mul, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem toMat_leviHom (m : LeviPart F r t) :
    toSum (toMat F _ (leviHom F r t m) : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) =
      fromBlocks (toMat F _ m.1 : Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F)) 0 0
        (toMat F _ m.2 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) := by
  change toSum (toMat F _ (ofUnitriangular F _ ⟨_, isUnitriangular_ofSum_diag F r t m.1 m.2⟩) :
    Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) = _
  rw [toMat_ofUnitriangular, toSum_ofSum]

/-- The projection to the diagonal blocks. -/
def projHom : unipotentAdelic F (r + t + 2) →* LeviPart F r t where
  toFun x := (ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₁₁ (isUnitriangular_toMat F _ x)⟩,
    ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₂₂ (isUnitriangular_toMat F _ x)⟩)
  map_one' := by
    ext1
    · change ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₁₁ (isUnitriangular_toMat F _ 1)⟩ = 1
      rw [ofUnitriangular_mk_eq_iff, MonoidHom.map_one, MonoidHom.map_one, Units.val_one,
        Units.val_one, toSum_one]
      ext i j
      simp [Matrix.toBlocks₁₁, Matrix.one_apply]
    · change ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₂₂ (isUnitriangular_toMat F _ 1)⟩ = 1
      rw [ofUnitriangular_mk_eq_iff, MonoidHom.map_one, MonoidHom.map_one, Units.val_one,
        Units.val_one, toSum_one]
      ext i j
      simp [Matrix.toBlocks₂₂, Matrix.one_apply]
  map_mul' x y := by
    have hx := toSum_eq_fromBlocks (isUnitriangular_toMat F _ x)
    have hy := toSum_eq_fromBlocks (isUnitriangular_toMat F _ y)
    have hxy : toSum (toMat F _ (x * y) : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) =
        toSum (toMat F _ x : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) *
          toSum (toMat F _ y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) := by
      rw [map_mul, Units.val_mul, toSum_mul]
    set X := toSum (toMat F _ x : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) with hX
    set Y := toSum (toMat F _ y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) with hY
    have key : toSum (toMat F _ (x * y) : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) =
        fromBlocks (X.toBlocks₁₁ * Y.toBlocks₁₁)
          (X.toBlocks₁₁ * Y.toBlocks₁₂ + X.toBlocks₁₂ * Y.toBlocks₂₂) 0
          (X.toBlocks₂₂ * Y.toBlocks₂₂) := by
      rw [hxy, hx, hy, fromBlocks_multiply]
      simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂,
        Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    ext1
    · change ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₁₁ (isUnitriangular_toMat F _ (x * y))⟩ =
        ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₁₁ (isUnitriangular_toMat F _ x)⟩ *
          ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₁₁ (isUnitriangular_toMat F _ y)⟩
      rw [ofUnitriangular_mk_eq_iff, key, toBlocks_fromBlocks₁₁, MonoidHom.map_mul, Units.val_mul,
        toMat_ofUnitriangular, toMat_ofUnitriangular]
    · change ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₂₂ (isUnitriangular_toMat F _ (x * y))⟩ =
        ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₂₂ (isUnitriangular_toMat F _ x)⟩ *
          ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₂₂ (isUnitriangular_toMat F _ y)⟩
      rw [ofUnitriangular_mk_eq_iff, key, toBlocks_fromBlocks₂₂, MonoidHom.map_mul, Units.val_mul,
        toMat_ofUnitriangular, toMat_ofUnitriangular]

theorem projHom_leviHom (m : LeviPart F r t) : projHom F r t (leviHom F r t m) = m := by
  ext1
  · change ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₁₁
      (isUnitriangular_toMat F _ (leviHom F r t m))⟩ = m.1
    rw [ofUnitriangular_mk_eq_iff, toMat_leviHom, toBlocks_fromBlocks₁₁]
  · change ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₂₂
      (isUnitriangular_toMat F _ (leviHom F r t m))⟩ = m.2
    rw [ofUnitriangular_mk_eq_iff, toMat_leviHom, toBlocks_fromBlocks₂₂]

theorem projHom_radicalHom (Y : Radical F r t) : projHom F r t (radicalHom F r t Y) = 1 := by
  ext1
  · change ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₁₁
      (isUnitriangular_toMat F _ (radicalHom F r t Y))⟩ = 1
    rw [ofUnitriangular_mk_eq_iff, toMat_radicalHom, toSum_openCellUnipotent,
      toBlocks_fromBlocks₁₁, MonoidHom.map_one, Units.val_one]
  · change ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₂₂
      (isUnitriangular_toMat F _ (radicalHom F r t Y))⟩ = 1
    rw [ofUnitriangular_mk_eq_iff, toMat_radicalHom, toSum_openCellUnipotent,
      toBlocks_fromBlocks₂₂, MonoidHom.map_one, Units.val_one]

theorem exists_radicalHom_eq (h : unipotentAdelic F (r + t + 2)) (hp : projHom F r t h = 1) :
    ∃ Y, radicalHom F r t Y = h := by
  set X := toSum (toMat F _ h : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) with hX
  have h11 : X.toBlocks₁₁ = 1 := by
    have := congrArg Prod.fst hp
    change ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₁₁ (isUnitriangular_toMat F _ h)⟩ =
      1 at this
    rw [ofUnitriangular_mk_eq_iff, MonoidHom.map_one, Units.val_one] at this
    exact this
  have h22 : X.toBlocks₂₂ = 1 := by
    have := congrArg Prod.snd hp
    change ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₂₂ (isUnitriangular_toMat F _ h)⟩ =
      1 at this
    rw [ofUnitriangular_mk_eq_iff, MonoidHom.map_one, Units.val_one] at this
    exact this
  refine ⟨Multiplicative.ofAdd X.toBlocks₁₂, ?_⟩
  apply toMat_injective
  apply Units.ext
  rw [toMat_radicalHom]
  apply toSum_injective
  rw [toSum_openCellUnipotent, toAdd_ofAdd, ← hX]
  have hb : X = fromBlocks X.toBlocks₁₁ X.toBlocks₁₂ 0 X.toBlocks₂₂ :=
    toSum_eq_fromBlocks (isUnitriangular_toMat F _ h)
  rw [h11, h22] at hb
  exact hb.symm

theorem continuous_radicalHom : Continuous (radicalHom F r t) := by
  refine (continuous_ofUnitriangular F _).comp (Continuous.subtype_mk ?_ _)
  have : (fun Y : Radical F r t => (openCellUnipotent F r t Y.toAdd :
      Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F))) =
      fun Y => ofSum (fromBlocks 1 Y.toAdd 0 1) := by
    funext Y
    exact openCellUnipotent_eq_ofSum F r t Y.toAdd
  rw [this]
  exact (continuous_const.matrix_fromBlocks continuous_toAdd continuous_const
    continuous_const).matrix_submatrix _ _

theorem isEmbedding_radicalHom : Topology.IsEmbedding (radicalHom F r t) := by
  refine Function.LeftInverse.isEmbedding (f := fun x : unipotentAdelic F (r + t + 2) =>
    Multiplicative.ofAdd (toSum (toMat F _ x :
      Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F))).toBlocks₁₂) ?_ ?_
    (continuous_radicalHom F r t)
  · intro Y
    simp only [toMat_radicalHom, toSum_openCellUnipotent, toBlocks_fromBlocks₁₂, ofAdd_toAdd]
  · exact continuous_ofAdd.comp (continuous_toBlocks₁₂
      ((continuous_toMat_val F _).matrix_submatrix _ _))

theorem continuous_leviHom : Continuous (leviHom F r t) := by
  refine (continuous_ofUnitriangular F _).comp (Continuous.subtype_mk ?_ _)
  exact (((continuous_toMat_val F _).comp continuous_fst).matrix_fromBlocks continuous_const
    continuous_const ((continuous_toMat_val F _).comp continuous_snd)).matrix_submatrix _ _

theorem continuous_projHom : Continuous (projHom F r t) := by
  have hX : Continuous fun x : unipotentAdelic F (r + t + 2) => toSum (toMat F _ x :
      Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) :=
    (continuous_toMat_val F _).matrix_submatrix _ _
  exact ((continuous_ofUnitriangular F _).comp (Continuous.subtype_mk
    (continuous_toBlocks₁₁ hX) _)).prodMk ((continuous_ofUnitriangular F _).comp
      (Continuous.subtype_mk (continuous_toBlocks₂₂ hX) _))

end Semidirect

section Rational

variable (F : Type u) [Field F] [NumberField F]

/-- A point of `N₀(𝔸)` is rational exactly when all entries of its matrix are rational. -/
theorem mem_Γ₀_iff_entries (n : ℕ) (x : unipotentAdelic F n) :
    x ∈ Γ₀ F n ↔ ∀ i j, ∃ c : F,
      (toMat F n x : Matrix (Fin n) (Fin n) (Adeles F)) i j = algebraMap F (Adeles F) c := by
  constructor
  · intro hx i j
    obtain ⟨δ, rfl⟩ := (mem_Γ₀_iff F n x).mp hx
    exact ⟨(δ : Matrix.GeneralLinearGroup (Fin n) F) i j, by rw [toMat_ratHom]; rfl⟩
  · intro h
    choose c hc using h
    have hx := isUnitriangular_toMat F n x
    have hM : IsUnitriangular (Matrix.of c) := by
      refine ⟨fun i j hji => ?_, fun i => ?_⟩
      · apply AdeleRing.algebraMap_injective (𝓞 F) F
        rw [Matrix.of_apply, ← hc, hx.1 hji, map_zero]
      · apply AdeleRing.algebraMap_injective (𝓞 F) F
        rw [Matrix.of_apply, ← hc, hx.2 i, map_one]
    refine (mem_Γ₀_iff F n x).mpr ⟨⟨RankinSelbergGlobal.Unfolding.unitriangularUnit (Matrix.of c) hM, hM⟩, ?_⟩
    apply toMat_injective
    apply Units.ext
    rw [toMat_ratHom]
    ext i j
    rw [AdelicGL.rational_apply, hc]
    rfl

theorem isDiscrete_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s : Set X}
    {t : Set Y} (hs : IsDiscrete s) (ht : IsDiscrete t) : IsDiscrete (s ×ˢ t) := by
  refine IsDiscrete.of_nhdsWithin fun x hx => ?_
  rw [show x = (x.1, x.2) from rfl, nhdsWithin_prod_eq, hs.nhdsWithin _ hx.1,
    ht.nhdsWithin _ hx.2, Filter.prod_pure_pure]

variable (r t : ℕ)

/-- The rational lattice `N_(t+1)(F) × N_(r+1)(F)` of the block diagonal group. -/
def leviLattice : Subgroup (LeviPart F r t) := (Γ₀ F (t + 1)).prod (Γ₀ F (r + 1))

theorem isDiscrete_leviLattice : IsDiscrete (leviLattice F r t : Set (LeviPart F r t)) := by
  change IsDiscrete ((Γ₀ F (t + 1) : Set (unipotentAdelic F (t + 1))) ×ˢ
    (Γ₀ F (r + 1) : Set (unipotentAdelic F (r + 1))))
  exact isDiscrete_prod (isDiscrete_Γ₀ F _) (isDiscrete_Γ₀ F _)

theorem toMat_entry_ofSum (A : Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F))
    (B : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F))
    (D : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) (i j : Fin (r + t + 2)) :
    ofSum (fromBlocks A B 0 D) i j =
      fromBlocks A B 0 D ((swapBlocks r t).symm i) ((swapBlocks r t).symm j) := rfl

theorem leviHom_mem_Γ₀ {m : LeviPart F r t} (hm : m ∈ leviLattice F r t) :
    leviHom F r t m ∈ Γ₀ F (r + t + 2) := by
  rw [mem_Γ₀_iff_entries]
  intro i j
  have h1 := (mem_Γ₀_iff_entries F _ m.1).mp hm.1
  have h2 := (mem_Γ₀_iff_entries F _ m.2).mp hm.2
  have e : (toMat F _ (leviHom F r t m) : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) =
      ofSum (fromBlocks (toMat F _ m.1 : Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F)) 0 0
        (toMat F _ m.2 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F))) := by
    rw [← toMat_leviHom, ofSum_toSum]
  rw [e, toMat_entry_ofSum]
  rcases (swapBlocks r t).symm i with a | a <;> rcases (swapBlocks r t).symm j with b | b
  · exact h1 a b
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · exact h2 a b

theorem projHom_mem_leviLattice {x : unipotentAdelic F (r + t + 2)} (hx : x ∈ Γ₀ F (r + t + 2)) :
    projHom F r t x ∈ leviLattice F r t := by
  have h := (mem_Γ₀_iff_entries F _ x).mp hx
  constructor
  · change _ ∈ Γ₀ F (t + 1)
    rw [mem_Γ₀_iff_entries]
    intro a b
    change ∃ c : F, (toMat F _ (ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₁₁
      (isUnitriangular_toMat F _ x)⟩) : Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F)) a b = _
    rw [toMat_ofUnitriangular]
    exact h _ _
  · change _ ∈ Γ₀ F (r + 1)
    rw [mem_Γ₀_iff_entries]
    intro a b
    change ∃ c : F, (toMat F _ (ofUnitriangular F _ ⟨_, isUnitriangular_toBlocks₂₂
      (isUnitriangular_toMat F _ x)⟩) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) a b = _
    rw [toMat_ofUnitriangular]
    exact h _ _

/-- The stabilizer `Λ_(J₀)(F)` of the open cell. -/
abbrev openLattice : Subgroup (unipotentAdelic F (r + t + 2)) :=
  patternRational F (r + t + 2) (openPivots r t)

theorem leviHom_mem_openLattice {m : LeviPart F r t} (hm : m ∈ leviLattice F r t) :
    leviHom F r t m ∈ openLattice F r t := by
  refine ⟨leviHom_mem_Γ₀ F r t hm, (mem_pattern_iff F _ _ _).mpr fun i hi j hj => ?_⟩
  have e : (toMat F _ (leviHom F r t m) : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) =
      ofSum (fromBlocks (toMat F _ m.1 : Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F)) 0 0
        (toMat F _ m.2 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F))) := by
    rw [← toMat_leviHom, ofSum_toSum]
  rw [e, toMat_entry_ofSum]
  simp only [openPivots, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have hi' : (swapBlocks r t).symm i = Sum.inl ⟨i, hi⟩ := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by rw [swapBlocks_inl_val])
  have hj' : (swapBlocks r t).symm j = Sum.inr ⟨(j : ℕ) - (t + 1), by have := j.2; omega⟩ := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by rw [swapBlocks_inr_val]; simp; omega)
  rw [hi', hj']
  rfl

theorem radicalHom_mem_pattern_iff (Y : Radical F r t) :
    radicalHom F r t Y ∈ pattern F (r + t + 2) (openPivots r t) ↔ Y = 1 := by
  constructor
  · intro h
    have hent := (mem_pattern_iff F _ _ _).mp h
    apply Multiplicative.toAdd.injective
    ext a b
    have hi : swapBlocks r t (Sum.inl a) ∈ openPivots r t := by
      simp only [openPivots, Finset.mem_filter, Finset.mem_univ, true_and, swapBlocks_inl_val]
      exact a.2
    have hj : swapBlocks r t (Sum.inr b) ∉ openPivots r t := by
      simp only [openPivots, Finset.mem_filter, Finset.mem_univ, true_and, swapBlocks_inr_val]
      omega
    have := hent _ hi _ hj
    rw [toMat_radicalHom, openCellUnipotent_eq_ofSum, toMat_entry_ofSum] at this
    simpa using this
  · rintro rfl
    rw [map_one]
    exact (pattern F _ _).one_mem

theorem comap_radicalHom_openLattice :
    (openLattice F r t).comap (radicalHom F r t) = ⊥ := by
  ext Y
  simp only [Subgroup.mem_comap, Subgroup.mem_bot]
  constructor
  · intro h
    exact (radicalHom_mem_pattern_iff F r t Y).mp h.2
  · rintro rfl
    rw [map_one]
    exact (openLattice F r t).one_mem

end Rational

end Langlands.Global.CuspidalPairEisenstein.Unfolding
