import Langlands.Group.GL.MirabolicRadical

/-! # Affine coordinates for the actual mirabolic matrix group -/

namespace Langlands.GeneralLinear.Mirabolic

universe u

variable {F : Type u} [CommRing F] {n : ℕ}

private def affineHead (g : mirabolic n F) : Matrix (Fin n) (Fin n) F :=
  fun i j => g.val.val i.castSucc j.castSucc

private theorem affineHead_one : affineHead (1 : mirabolic n F) = 1 := by
  ext i j
  simp [affineHead, Matrix.one_apply]

private theorem affineHead_mul (g h : mirabolic n F) :
    affineHead (g * h) = affineHead g * affineHead h := by
  ext i j
  change (g.val.val * h.val.val) i.castSucc j.castSucc = _
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hh : h.val.val (Fin.last n) j.castSucc = 0 := by
    simpa using h.property j.castSucc
  simp [hh, affineHead, Matrix.mul_apply]

/-- The actual invertible upper-left block, with inverse extracted from `g⁻¹`. -/
def linearPart : mirabolic n F →* Langlands.GeneralLinear n F where
  toFun g :=
    { val := affineHead g
      inv := affineHead g⁻¹
      val_inv := by rw [← affineHead_mul, mul_inv_cancel, affineHead_one]
      inv_val := by rw [← affineHead_mul, inv_mul_cancel, affineHead_one] }
  map_one' := Units.ext affineHead_one
  map_mul' g h := Units.ext (affineHead_mul g h)

@[simp] theorem linearPart_entry (g : mirabolic n F) (i j : Fin n) :
    (linearPart g).val i j = g.val.val i.castSucc j.castSucc := rfl

/-- The inverse of the leading block is the leading block of the actual inverse. -/
@[simp] theorem linearPart_inv_entry (g : mirabolic n F) (i j : Fin n) :
    ((linearPart g)⁻¹).val i j = (g⁻¹).val.val i.castSucc j.castSucc := rfl

theorem linearPart_mul (g h : mirabolic n F) :
    linearPart (g * h) = linearPart g * linearPart h :=
  map_mul linearPart g h

/-- The final column above its fixed bottom entry. -/
def columnPart (g : mirabolic n F) : Fin n → F :=
  fun i => g.val.val i.castSucc (Fin.last n)

@[simp] theorem columnPart_apply (g : mirabolic n F) (i : Fin n) :
    columnPart g i = g.val.val i.castSucc (Fin.last n) := rfl

/-- Mirabolic multiplication is the usual affine multiplication on these entries. -/
theorem columnPart_mul (g h : mirabolic n F) :
    columnPart (g * h) = columnPart g + (linearPart g).val.mulVec (columnPart h) := by
  funext i
  change (g.val.val * h.val.val) i.castSucc (Fin.last n) = _
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hh : h.val.val (Fin.last n) (Fin.last n) = 1 := by
    simpa using h.property (Fin.last n)
  simp [hh, columnPart, Matrix.mulVec, dotProduct, add_comm]

/-- Reassembly as the literal product `[[I,v],[0,1]] * diag(A,1)`. -/
def affineMatrix (A : Langlands.GeneralLinear n F) (v : Fin n → F) :
    mirabolic n F :=
  (radicalElement v).val * levi A

@[simp] theorem affineMatrix_first (A : Langlands.GeneralLinear n F)
    (v : Fin n → F) (i j : Fin n) :
    (affineMatrix A v).val.val i.castSucc j.castSucc = A.val i j := by
  change ((radicalElement v).val.val.val * (levi A).val.val)
    i.castSucc j.castSucc = _
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, radicalElement_first,
    radicalElement_last, levi_first, levi_bottom]

@[simp] theorem affineMatrix_last (A : Langlands.GeneralLinear n F)
    (v : Fin n → F) (i : Fin n) :
    (affineMatrix A v).val.val i.castSucc (Fin.last n) = v i := by
  change ((radicalElement v).val.val.val * (levi A).val.val)
    i.castSucc (Fin.last n) = _
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, radicalElement_first,
    radicalElement_last, levi_last, levi_bottom]

/-- The bottom row is the inherited mirabolic row `(0,...,0,1)`. -/
@[simp] theorem affineMatrix_bottom (A : Langlands.GeneralLinear n F)
    (v : Fin n → F) (j : Fin (n + 1)) :
    (affineMatrix A v).val.val (Fin.last n) j = if j = Fin.last n then 1 else 0 :=
  (affineMatrix A v).property j

@[simp] theorem linearPart_affineMatrix (A : Langlands.GeneralLinear n F)
    (v : Fin n → F) :
    linearPart (affineMatrix A v) = A := by
  apply Units.ext
  ext i j
  exact affineMatrix_first A v i j

@[simp] theorem columnPart_affineMatrix (A : Langlands.GeneralLinear n F)
    (v : Fin n → F) :
    columnPart (affineMatrix A v) = v := by
  funext i
  exact affineMatrix_last A v i

@[simp] theorem affineMatrix_parts (g : mirabolic n F) :
    affineMatrix (linearPart g) (columnPart g) = g := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · exact ((affineMatrix (linearPart g) (columnPart g)).property j).trans
      (g.property j).symm
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · exact affineMatrix_last _ _ i
    · exact affineMatrix_first _ _ i j

/-- The underlying set equivalence. The product on the coordinate space is
described by `affineCoordinates_mul`, rather than the direct-product group law. -/
def affineCoordinates :
    mirabolic n F ≃ Langlands.GeneralLinear n F × (Fin n → F) where
  toFun g := (linearPart g, columnPart g)
  invFun p := affineMatrix p.1 p.2
  left_inv := affineMatrix_parts
  right_inv p := Prod.ext (linearPart_affineMatrix p.1 p.2)
    (columnPart_affineMatrix p.1 p.2)

@[simp] theorem affineCoordinates_apply (g : mirabolic n F) :
    affineCoordinates g = (linearPart g, columnPart g) := rfl

@[simp] theorem affineCoordinates_symm_apply
    (p : Langlands.GeneralLinear n F × (Fin n → F)) :
    affineCoordinates.symm p = affineMatrix p.1 p.2 := rfl

theorem affineCoordinates_mul (g h : mirabolic n F) :
    affineCoordinates (g * h) =
      (linearPart g * linearPart h,
        columnPart g + (linearPart g).val.mulVec (columnPart h)) :=
  Prod.ext (map_mul linearPart g h) (columnPart_mul g h)

/-- The affine law `(A,v)(B,w) = (AB, v + A.val.mulVec w)` on reassembled matrices. -/
theorem affineMatrix_mul (A B : Langlands.GeneralLinear n F) (v w : Fin n → F) :
    affineMatrix A v * affineMatrix B w = affineMatrix (A * B) (v + A.val.mulVec w) := by
  apply affineCoordinates.injective
  rw [affineCoordinates_mul]
  simp

section Topology

variable [TopologicalSpace F]

/-- The invertible leading block is continuous in the inherited units topology. -/
theorem continuous_linearPart : Continuous (linearPart (n := n) (F := F)) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    intro i j
    exact (entry i.castSucc j.castSucc).continuous
  · apply continuous_matrix
    intro i j
    exact ((continuous_apply j.castSucc).comp
      ((continuous_apply i.castSucc).comp
        (Units.continuous_coe_inv :
          Continuous (fun g : Langlands.GeneralLinear (n + 1) F => (g⁻¹).val)))).comp
        continuous_subtype_val

theorem continuous_columnPart : Continuous (columnPart (n := n) (F := F)) :=
  continuous_pi fun i => (entry i.castSucc (Fin.last n)).continuous

variable [IsTopologicalRing F]

theorem continuous_affineMatrix :
    Continuous (fun p : Langlands.GeneralLinear n F × (Fin n → F) =>
      affineMatrix p.1 p.2) :=
  ((continuous_subtype_val.comp continuous_radicalElement).comp continuous_snd).mul
    (continuous_levi.comp continuous_fst)

/-- The actual mirabolic group has the product topology on its affine coordinates. -/
def affineHomeomorph :
    mirabolic n F ≃ₜ Langlands.GeneralLinear n F × (Fin n → F) where
  toEquiv := affineCoordinates
  continuous_toFun := continuous_linearPart.prodMk continuous_columnPart
  continuous_invFun := continuous_affineMatrix

@[simp] theorem affineHomeomorph_apply (g : mirabolic n F) :
    affineHomeomorph g = (linearPart g, columnPart g) := rfl

@[simp] theorem affineHomeomorph_symm_apply
    (p : Langlands.GeneralLinear n F × (Fin n → F)) :
    affineHomeomorph.symm p = affineMatrix p.1 p.2 := rfl

end Topology

end Langlands.GeneralLinear.Mirabolic
