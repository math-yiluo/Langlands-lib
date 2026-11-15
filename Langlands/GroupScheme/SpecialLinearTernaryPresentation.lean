import Langlands.GroupScheme.SpecialLinearBinaryPresentation
import Langlands.GroupScheme.Examples.SU3MatrixFixedPoints

/-! # Block embeddings of binary SL into ternary SL -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.SpecialLinear.TernaryPresentation

open BinaryPresentation

/-- Binary special linear group. -/
local notation "SL2" A => Matrix.SpecialLinearGroup (Fin 2) A

/-- Ternary special linear group. -/
local notation "SL3" A => Matrix.SpecialLinearGroup (Fin 3) A

section Blocks

variable {R : Type u} [CommRing R]

/-- The underlying matrix of the block embedding at the indices `0, 1`. -/
def leftMatrix (g : SL2 R) : Matrix (Fin 3) (Fin 3) R :=
  !![(g : Matrix (Fin 2) (Fin 2) R) 0 0, (g : Matrix (Fin 2) (Fin 2) R) 0 1, 0;
    (g : Matrix (Fin 2) (Fin 2) R) 1 0, (g : Matrix (Fin 2) (Fin 2) R) 1 1, 0;
    0, 0, 1]

/-- The underlying matrix of the block embedding at the indices `1, 2`. -/
def rightMatrix (g : SL2 R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
    0, (g : Matrix (Fin 2) (Fin 2) R) 0 0, (g : Matrix (Fin 2) (Fin 2) R) 0 1;
    0, (g : Matrix (Fin 2) (Fin 2) R) 1 0, (g : Matrix (Fin 2) (Fin 2) R) 1 1]

theorem det_two (g : SL2 R) :
    (g : Matrix (Fin 2) (Fin 2) R) 0 0 * (g : Matrix (Fin 2) (Fin 2) R) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) R) 0 1 * (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  exact h

theorem det_leftMatrix (g : SL2 R) : (leftMatrix g).det = 1 := by
  rw [leftMatrix, Matrix.det_fin_three]
  simpa using det_two g

theorem det_rightMatrix (g : SL2 R) : (rightMatrix g).det = 1 := by
  rw [rightMatrix, Matrix.det_fin_three]
  simpa using det_two g

/-- The block embedding of binary `SL` at the indices `0, 1`. -/
def left : (SL2 R) →* (SL3 R) where
  toFun g := ⟨leftMatrix g, det_leftMatrix g⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [leftMatrix]
  map_mul' g h := by
    apply Subtype.ext
    change leftMatrix (g * h) = leftMatrix g * leftMatrix h
    ext i j
    rw [leftMatrix, Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [leftMatrix, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

/-- The block embedding of binary `SL` at the indices `1, 2`. -/
def right : (SL2 R) →* (SL3 R) where
  toFun g := ⟨rightMatrix g, det_rightMatrix g⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rightMatrix]
  map_mul' g h := by
    apply Subtype.ext
    change rightMatrix (g * h) = rightMatrix g * rightMatrix h
    ext i j
    rw [rightMatrix, Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [rightMatrix, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

@[simp]
theorem coe_left (g : SL2 R) : ((left g : SL3 R) : Matrix (Fin 3) (Fin 3) R) = leftMatrix g :=
  rfl

@[simp]
theorem coe_right (g : SL2 R) : ((right g : SL3 R) : Matrix (Fin 3) (Fin 3) R) = rightMatrix g :=
  rfl

theorem left_injective : Function.Injective (left (R := R)) := by
  intro g h hgh
  have hm := congrArg (fun k : SL3 R => (k : Matrix (Fin 3) (Fin 3) R)) hgh
  simp only [coe_left] at hm
  ext i j
  have := congrFun (congrFun hm (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [leftMatrix] using this

theorem right_injective : Function.Injective (right (R := R)) := by
  intro g h hgh
  have hm := congrArg (fun k : SL3 R => (k : Matrix (Fin 3) (Fin 3) R)) hgh
  simp only [coe_right] at hm
  ext i j
  have := congrFun (congrFun hm (Fin.succ i)) (Fin.succ j)
  fin_cases i <;> fin_cases j <;> simpa [rightMatrix] using this

/-- Both block embeddings commute with changing the coefficients. -/
theorem map_left {S : Type v} [CommRing S] (f : R →+* S) (g : SL2 R) :
    SpecialLinearGroup.map f (left g) = left (SpecialLinearGroup.map f g) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftMatrix, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

theorem map_right {S : Type v} [CommRing S] (f : R →+* S) (g : SL2 R) :
    SpecialLinearGroup.map f (right g) = right (SpecialLinearGroup.map f g) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rightMatrix, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

end Blocks

section Outer

variable {R : Type u} [CommRing R]

/-- The antidiagonal matrix `!![0, 0, 1; 0, -1, 0; 1, 0, 0]`. It equals the Hermitian form
`SU3Root.gram` of the Library's quasi-split `SU₃` coordinates. -/
def antidiagonal : Matrix (Fin 3) (Fin 3) R := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

theorem antidiagonal_mul_self : (antidiagonal : Matrix (Fin 3) (Fin 3) R) * antidiagonal = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antidiagonal, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_antidiagonal : (antidiagonal : Matrix (Fin 3) (Fin 3) R).det = 1 := by
  simp [antidiagonal, Matrix.det_fin_three]

/-- The matrix of the outer involution: `J (g⁻¹)ᵀ J` with `J` antidiagonal. -/
def outerMatrix (g : SL3 R) : Matrix (Fin 3) (Fin 3) R :=
  antidiagonal * ((g⁻¹ : SL3 R) : Matrix (Fin 3) (Fin 3) R)ᵀ * antidiagonal

theorem det_outerMatrix (g : SL3 R) : (outerMatrix g).det = 1 := by
  rw [outerMatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_antidiagonal,
    (g⁻¹).2, one_mul, one_mul]

/-- The outer automorphism `g ↦ J (g⁻¹)ᵀ J` of ternary `SL`. It exchanges the two block
embeddings (`outer_left`, `outer_right`). -/
def outer : (SL3 R) →* (SL3 R) where
  toFun g := ⟨outerMatrix g, det_outerMatrix g⟩
  map_one' := by
    apply Subtype.ext
    change outerMatrix 1 = 1
    rw [outerMatrix, inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one,
      antidiagonal_mul_self]
  map_mul' g h := by
    apply Subtype.ext
    change outerMatrix (g * h) = outerMatrix g * outerMatrix h
    rw [outerMatrix, outerMatrix, outerMatrix, _root_.mul_inv_rev,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc antidiagonal antidiagonal, antidiagonal_mul_self, Matrix.one_mul]

theorem coe_outer (g : SL3 R) :
    ((outer g : SL3 R) : Matrix (Fin 3) (Fin 3) R) = outerMatrix g := rfl

theorem outer_left (g : SL2 R) : outer (left g) = right g := by
  apply Subtype.ext
  rw [coe_outer, coe_right, outerMatrix, ← map_inv, coe_left]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [leftMatrix, rightMatrix, antidiagonal, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two]

theorem outer_right (g : SL2 R) : outer (right g) = left g := by
  apply Subtype.ext
  rw [coe_outer, coe_left, outerMatrix, ← map_inv, coe_right]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [leftMatrix, rightMatrix, antidiagonal, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two]

theorem outer_comp_left : (outer (R := R)).comp left = right := by
  ext g : 1
  exact outer_left g

theorem outer_comp_right : (outer (R := R)).comp right = left := by
  ext g : 1
  exact outer_right g

theorem transpose_antidiagonal :
    (antidiagonal : Matrix (Fin 3) (Fin 3) R)ᵀ = antidiagonal := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiagonal, Matrix.transpose_apply]

/-- The outer automorphism is an involution. -/
@[simp]
theorem outer_outer (g : SL3 R) : outer (outer g) = g := by
  apply Subtype.ext
  change outerMatrix (outer g) = g
  rw [outerMatrix, ← map_inv, coe_outer, outerMatrix, inv_inv, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose, transpose_antidiagonal]
  simp only [← Matrix.mul_assoc, antidiagonal_mul_self, Matrix.one_mul]
  simp only [Matrix.mul_assoc, antidiagonal_mul_self, Matrix.mul_one]

theorem outer_comp_outer : (outer (R := R)).comp outer = MonoidHom.id _ := by
  ext g : 1
  exact outer_outer g

/-- The outer involution as a multiplicative automorphism. -/
def outerEquiv : (SL3 R) ≃* (SL3 R) :=
  MulEquiv.ofBijective outer (Function.Involutive.bijective outer_outer)

@[simp]
theorem outerEquiv_apply (g : SL3 R) : outerEquiv g = outer g := rfl

@[simp]
theorem outerEquiv_symm_apply (g : SL3 R) : outerEquiv.symm g = outer g := by
  rw [MulEquiv.symm_apply_eq, outerEquiv_apply, outer_outer]

theorem map_antidiagonal {S : Type v} [CommRing S] (f : R →+* S) :
    f.mapMatrix (antidiagonal : Matrix (Fin 3) (Fin 3) R) = antidiagonal := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiagonal]

/-- The outer involution commutes with changing the coefficients. -/
theorem map_outer {S : Type v} [CommRing S] (f : R →+* S) (g : SL3 R) :
    SpecialLinearGroup.map f (outer g) = outer (SpecialLinearGroup.map f g) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_outer, coe_outer, outerMatrix, outerMatrix,
    ← map_inv, Matrix.SpecialLinearGroup.map_apply_coe, map_mul, map_mul, map_antidiagonal,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]

theorem map_comp_outer {S : Type v} [CommRing S] (f : R →+* S) :
    (SpecialLinearGroup.map f).comp (outer (R := R)) = outer.comp (SpecialLinearGroup.map f) := by
  ext g : 1
  exact map_outer f g

end Outer

section Unitary

variable {R : Type u} [CommRing R]

/-- The antidiagonal matrix is the Gram matrix of the Library's quasi-split `SU₃`. -/
theorem antidiagonal_eq_gram : (antidiagonal : Matrix (Fin 3) (Fin 3) R) = SU3Root.gram R := rfl

/-- The Library's inverse-adjoint twist of ternary `SL` is the outer involution after
conjugating the coefficients. -/
theorem unitaryTwist_eq_outer_map (c : SU3Root.RingInvolution R) (g : SL3 R) :
    SU3Root.unitaryTwist c g = outer (SpecialLinearGroup.map c.bar.toRingHom g) := by
  apply Subtype.ext
  change SU3Root.gram R * SU3Root.conjugateTranspose c ((g⁻¹ : SL3 R) : Matrix (Fin 3) (Fin 3) R) *
      SU3Root.gram R =
    antidiagonal * (((SpecialLinearGroup.map c.bar.toRingHom g)⁻¹ : SL3 R) :
      Matrix (Fin 3) (Fin 3) R)ᵀ * antidiagonal
  rw [← map_inv, Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

theorem map_bar_map_bar (c : SU3Root.RingInvolution R) (g : SL3 R) :
    SpecialLinearGroup.map c.bar.toRingHom (SpecialLinearGroup.map c.bar.toRingHom g) = g := by
  ext i j
  simp

/-- On matrices preserving the `SU₃` Hermitian form, the outer involution is entrywise
conjugation. -/
theorem outer_eq_map_of_preservesForm (c : SU3Root.RingInvolution R) (g : SL3 R)
    (hg : SU3Root.PreservesForm c (g : Matrix (Fin 3) (Fin 3) R)) :
    outer g = SpecialLinearGroup.map c.bar.toRingHom g := by
  have h : outer (SpecialLinearGroup.map c.bar.toRingHom g) = g := by
    rw [← unitaryTwist_eq_outer_map]
    exact (SU3Root.unitaryTwist_fixed_iff c g).mpr hg
  conv_lhs => rw [← h, outer_outer]

theorem outer_eq_map_of_mem_twistFixedSubgroup (c : SU3Root.RingInvolution R) (g : SL3 R)
    (hg : g ∈ SU3Root.twistFixedSubgroup c) :
    outer g = SpecialLinearGroup.map c.bar.toRingHom g :=
  outer_eq_map_of_preservesForm c g ((SU3Root.mem_twistFixedSubgroup c g).mp hg)

end Unitary

section Generation

variable {F : Type u} [Field F]

open Matrix.SpecialLinearGroup in
/-- Ternary `SL` over a field is generated by its two block copies of binary `SL`. -/
theorem range_left_sup_range_right :
    (left (R := F)).range ⊔ (right (R := F)).range = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hl : ∀ h : SL2 F, left h ∈ (left (R := F)).range ⊔ (right (R := F)).range :=
    fun h => Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨h, rfl⟩)
  have hr : ∀ h : SL2 F, right h ∈ (left (R := F)).range ⊔ (right (R := F)).range :=
    fun h => Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨h, rfl⟩)
  refine diagonal_transvection_induction'
    (fun g => g ∈ (left (R := F)).range ⊔ (right (R := F)).range) g ?_ ?_ ?_
  · intro i j hij c hc
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · have : diag2n hij c hc = left (diag2 c hc) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [diag2n_coe, leftMatrix]
      rw [this]; exact hl _
    · have : diag2n hij c hc = left (diag2 c hc) * right (diag2 c hc) := by
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [diag2n_coe, leftMatrix, rightMatrix, Matrix.mul_apply, Fin.sum_univ_three, hc]
      rw [this]; exact Subgroup.mul_mem _ (hl _) (hr _)
    · have : diag2n hij c hc = left (diag2 c⁻¹ (inv_ne_zero hc)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [diag2n_coe, leftMatrix]
      rw [this]; exact hl _
    · exact absurd rfl hij
    · have : diag2n hij c hc = right (diag2 c hc) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [diag2n_coe, rightMatrix]
      rw [this]; exact hr _
    · have : diag2n hij c hc =
          left (diag2 c⁻¹ (inv_ne_zero hc)) * right (diag2 c⁻¹ (inv_ne_zero hc)) := by
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [diag2n_coe, leftMatrix, rightMatrix, Matrix.mul_apply, Fin.sum_univ_three, hc]
      rw [this]; exact Subgroup.mul_mem _ (hl _) (hr _)
    · have : diag2n hij c hc = right (diag2 c⁻¹ (inv_ne_zero hc)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [diag2n_coe, rightMatrix]
      rw [this]; exact hr _
    · exact absurd rfl hij
  · intro i j hij t
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · have : transvection hij t = left (upper t) := by
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [transvection_coe, leftMatrix]
      rw [this]; exact hl _
    · have : transvection hij t =
          left (upper t) * right (upper 1) * left (upper (-t)) * right (upper (-1)) := by
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [transvection_coe, leftMatrix, rightMatrix, Matrix.mul_apply, Fin.sum_univ_three]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hl _) (hr _)) (hl _))
        (hr _)
    · have : transvection hij t = left (lower t) := by
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [transvection_coe, leftMatrix]
      rw [this]; exact hl _
    · exact absurd rfl hij
    · have : transvection hij t = right (upper t) := by
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [transvection_coe, rightMatrix]
      rw [this]; exact hr _
    · have : transvection hij t =
          right (lower 1) * left (lower t) * right (lower (-1)) * left (lower (-t)) := by
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [transvection_coe, leftMatrix, rightMatrix, Matrix.mul_apply, Fin.sum_univ_three]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hr _) (hl _)) (hr _))
        (hl _)
    · have : transvection hij t = right (lower t) := by
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [transvection_coe, rightMatrix]
      rw [this]; exact hr _
    · exact absurd rfl hij
  · intro A B hA hB
    exact Subgroup.mul_mem _ hA hB

/-- Homomorphisms out of ternary `SL` over a field are determined by their restrictions to
the two block copies of binary `SL`. -/
theorem hom_ext {H : Type w} [Group H] {φ ψ : (SL3 F) →* H}
    (hleft : φ.comp left = ψ.comp left) (hright : φ.comp right = ψ.comp right) : φ = ψ := by
  have hle : (left (R := F)).range ⊔ (right (R := F)).range ≤ φ.eqLocus ψ := by
    refine sup_le ?_ ?_
    · rintro _ ⟨h, rfl⟩
      exact DFunLike.congr_fun hleft h
    · rintro _ ⟨h, rfl⟩
      exact DFunLike.congr_fun hright h
  rw [range_left_sup_range_right] at hle
  ext g
  exact hle (Subgroup.mem_top g)

end Generation

end Langlands.GroupScheme.SpecialLinear.TernaryPresentation
