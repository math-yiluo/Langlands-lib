import Langlands.Group.GL.MirabolicProjection
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # The two mixed mirabolic inducing subgroups of BZ77 §4.12 -/

namespace Langlands.GeneralLinear.Mirabolic.MixedProduct

universe u

variable {R : Type u} [CommRing R] {k r : ℕ}

/-! Concrete two-block calculations, including empty blocks. -/

namespace TwoBlock

variable {a b : ℕ}

private def label : Fin a ⊕ Fin b → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

/-- Internal upper two-block subgroup of actual matrix units. -/
def upper (a b : ℕ) (R : Type u) [CommRing R] :
    Subgroup (Matrix.GeneralLinearGroup (Fin a ⊕ Fin b) R) where
  carrier := {g | g.val.BlockTriangular label}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' := fun hg hh => hg.mul hh
  inv_mem' := by
    intro g hg
    let := g.invertible
    change (g⁻¹).val.BlockTriangular label
    simpa only [Matrix.GeneralLinearGroup.coe_inv] using
      Matrix.blockTriangular_inv_of_blockTriangular hg

theorem mem_upper (g : Matrix.GeneralLinearGroup (Fin a ⊕ Fin b) R) :
    g ∈ upper a b R ↔ ∀ i j, g.val (Sum.inr i) (Sum.inl j) = 0 := by
  constructor
  · intro hg i j
    exact hg (by simp [label] : label (Sum.inl j) < label (Sum.inr i))
  · intro hg i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact (by simp [label] at hij)
    · exact (by simp [label] at hij)
    · exact hg i j
    · exact (by simp [label] at hij)

def A (g : upper a b R) : Matrix (Fin a) (Fin a) R := g.val.val.toBlocks₁₁
def B (g : upper a b R) : Matrix (Fin a) (Fin b) R := g.val.val.toBlocks₁₂
def D (g : upper a b R) : Matrix (Fin b) (Fin b) R := g.val.val.toBlocks₂₂

theorem C_zero (g : upper a b R) : g.val.val.toBlocks₂₁ = 0 :=
  Matrix.ext fun i j => (mem_upper g.val).mp g.property i j

theorem display (g : upper a b R) :
    g.val.val = Matrix.fromBlocks (A g) (B g) 0 (D g) := by
  rw [← C_zero g]
  exact (Matrix.fromBlocks_toBlocks _).symm

theorem A_one : A (1 : upper a b R) = 1 := by ext i j; simp [A, Matrix.toBlocks₁₁, Matrix.one_apply]
theorem D_one : D (1 : upper a b R) = 1 := by ext i j; simp [D, Matrix.toBlocks₂₂, Matrix.one_apply]

theorem A_mul (g h : upper a b R) : A (g * h) = A g * A h := by
  change (g.val.val * h.val.val).toBlocks₁₁ = _
  rw [display g, display h, Matrix.fromBlocks_multiply]
  simp

theorem D_mul (g h : upper a b R) : D (g * h) = D g * D h := by
  change (g.val.val * h.val.val).toBlocks₂₂ = _
  rw [display g, display h, Matrix.fromBlocks_multiply]
  simp

/-- Both diagonal inverses are extracted from the actual matrix inverse. -/
def projection : upper a b R →*
    Langlands.GeneralLinear a R × Langlands.GeneralLinear b R where
  toFun g :=
    ({ val := A g
       inv := A g⁻¹
       val_inv := by rw [← A_mul, mul_inv_cancel, A_one]
       inv_val := by rw [← A_mul, inv_mul_cancel, A_one] },
     { val := D g
       inv := D g⁻¹
       val_inv := by rw [← D_mul, mul_inv_cancel, D_one]
       inv_val := by rw [← D_mul, inv_mul_cancel, D_one] })
  map_one' := Prod.ext (Units.ext A_one) (Units.ext D_one)
  map_mul' g h := Prod.ext (Units.ext (A_mul g h)) (Units.ext (D_mul g h))

/-- Literal upper block matrix with its explicit inverse. -/
def matrix (a₀ : Langlands.GeneralLinear a R) (d : Langlands.GeneralLinear b R)
    (x : Matrix (Fin a) (Fin b) R) : upper a b R :=
  ⟨{ val := Matrix.fromBlocks a₀.val x 0 d.val
     inv := Matrix.fromBlocks (a₀⁻¹).val (-(a₀⁻¹).val * x * (d⁻¹).val) 0 (d⁻¹).val
     val_inv := by
       rw [Matrix.fromBlocks_multiply]
       simp [Matrix.mul_assoc]
     inv_val := by
       rw [Matrix.fromBlocks_multiply]
       simp [Matrix.mul_assoc] },
    (mem_upper _).mpr fun _ _ => rfl⟩

@[simp] theorem projection_matrix (a₀ : Langlands.GeneralLinear a R)
    (d : Langlands.GeneralLinear b R) (x : Matrix (Fin a) (Fin b) R) :
    projection (matrix a₀ d x) = (a₀, d) := by
  apply Prod.ext <;> apply Units.ext <;> rfl

theorem matrix_parts (g : upper a b R) :
    matrix (projection g).1 (projection g).2 (B g) = g :=
  Subtype.ext (Units.ext (display g).symm)

def sectionMap : (Langlands.GeneralLinear a R × Langlands.GeneralLinear b R) →*
    upper a b R where
  toFun p := matrix p.1 p.2 0
  map_one' := Subtype.ext (Units.ext Matrix.fromBlocks_one)
  map_mul' p q := by
    apply Subtype.ext
    apply Units.ext
    change Matrix.fromBlocks (p.1 * q.1).val 0 0 (p.2 * q.2).val = _
    simp [matrix, Matrix.fromBlocks_multiply]

@[simp] theorem projection_section (p : Langlands.GeneralLinear a R × Langlands.GeneralLinear b R) :
    projection (sectionMap p) = p := projection_matrix _ _ _

def unipotent (x : Matrix (Fin a) (Fin b) R) : upper a b R := matrix 1 1 x

@[simp] theorem projection_unipotent (x : Matrix (Fin a) (Fin b) R) :
    projection (unipotent x) = 1 := projection_matrix _ _ _

theorem unipotent_add (x y : Matrix (Fin a) (Fin b) R) :
    unipotent (x + y) = unipotent x * unipotent y := by
  apply Subtype.ext
  apply Units.ext
  simp [unipotent, matrix, Matrix.fromBlocks_multiply, add_comm]

theorem unipotent_mul_section (x : Matrix (Fin a) (Fin b) R)
    (p : Langlands.GeneralLinear a R × Langlands.GeneralLinear b R) :
    (unipotent x * sectionMap p).val.val =
      Matrix.fromBlocks p.1.val (x * p.2.val) 0 p.2.val := by
  change Matrix.fromBlocks 1 x 0 1 * Matrix.fromBlocks p.1.val 0 0 p.2.val = _
  simp [Matrix.fromBlocks_multiply]

theorem conjugate_unipotent (p : Langlands.GeneralLinear a R × Langlands.GeneralLinear b R)
    (x : Matrix (Fin a) (Fin b) R) :
    sectionMap p * unipotent x * (sectionMap p)⁻¹ =
      unipotent (p.1.val * x * (p.2⁻¹).val) := by
  rw [← map_inv]
  apply Subtype.ext
  apply Units.ext
  change Matrix.fromBlocks p.1.val 0 0 p.2.val *
    Matrix.fromBlocks 1 x 0 1 *
    Matrix.fromBlocks (p.1⁻¹).val 0 0 (p.2⁻¹).val = _
  simp [unipotent, matrix, Matrix.fromBlocks_multiply, Matrix.mul_assoc]

section Topology

variable [TopologicalSpace R]

theorem continuous_projection : Continuous (projection (a := a) (b := b) (R := R)) := by
  apply Continuous.prodMk
  all_goals
    apply Units.continuous_iff.mpr
    constructor
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_submatrix _ _
    · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_submatrix _ _

theorem continuous_section : Continuous (sectionMap (a := a) (b := b) (R := R)) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · exact (Units.continuous_val.comp continuous_fst).matrix_fromBlocks
      continuous_const continuous_const (Units.continuous_val.comp continuous_snd)
  · simpa [sectionMap, matrix] using
      (Units.continuous_coe_inv.comp (continuous_fst : Continuous (Prod.fst :
        Langlands.GeneralLinear a R × Langlands.GeneralLinear b R → _))).matrix_fromBlocks
        (continuous_const (y := (0 : Matrix (Fin a) (Fin b) R))) continuous_const
        (Units.continuous_coe_inv.comp continuous_snd)

theorem continuous_unipotent [IsTopologicalRing R] :
    Continuous (unipotent (a := a) (b := b) (R := R)) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const
  · simpa [unipotent, matrix] using
      continuous_const.matrix_fromBlocks continuous_id.neg continuous_const
        (continuous_const : Continuous (fun _ : Matrix (Fin a) (Fin b) R =>
          (1 : Matrix (Fin b) (Fin b) R)))

theorem isClosed_upper [T2Space R] :
    IsClosed (upper a b R : Set (Matrix.GeneralLinearGroup (Fin a ⊕ Fin b) R)) :=
  isClosed_setOfPred_blockTriangular.preimage Units.continuous_val

end Topology
end TwoBlock

/-! The explicit coordinate permutations for the source's two embeddings. -/

/-- Consecutive `k,(r+1)` coordinates, with the arithmetic rank cast displayed. -/
def leftIndex (k r : ℕ) : Fin k ⊕ Fin (r + 1) ≃ Fin (k + r + 1) :=
  finSumFinEquiv.trans (finCongr (Nat.add_assoc k r 1).symm)

/-- First `r`, middle `k`, final `1`; the first summand is the full mirabolic block. -/
def rightIndex (k r : ℕ) : Fin (r + 1) ⊕ Fin k ≃ Fin (k + r + 1) :=
  ((finSumFinEquiv.symm.sumCongr (Equiv.refl (Fin k))).trans
    ((Equiv.sumAssoc (Fin r) (Fin 1) (Fin k)).trans
      ((Equiv.refl (Fin r)).sumCongr (Equiv.sumComm (Fin 1) (Fin k))) |>.trans
      (Equiv.sumAssoc (Fin r) (Fin k) (Fin 1)).symm)).trans
    (finSumFinEquiv.sumCongr (Equiv.refl (Fin 1)) |>.trans
      (finSumFinEquiv.trans (finCongr (show r + k + 1 = k + r + 1 by omega))))

@[simp] theorem leftIndex_last :
    leftIndex k r (Sum.inr (Fin.last r)) = Fin.last (k + r) := by
  apply Fin.ext
  simp [leftIndex]

@[simp] theorem rightIndex_last :
    rightIndex k r (Sum.inl (Fin.last r)) = Fin.last (k + r) := by
  apply Fin.ext
  simp [rightIndex]


/-- These formulas record the actual consecutive `(k,r,1)` placement. -/
@[simp] theorem leftIndex_inl_val (i : Fin k) :
    (leftIndex k r (Sum.inl i)).val = i.val := by simp [leftIndex]

@[simp] theorem leftIndex_inr_val (j : Fin (r + 1)) :
    (leftIndex k r (Sum.inr j)).val = k + j.val := by simp [leftIndex]

/-- These formulas record the actual `(r,k,1)` placement, including empty blocks. -/
@[simp] theorem rightIndex_first_val (i : Fin r) :
    (rightIndex k r (Sum.inl i.castSucc)).val = i.val := by simp [rightIndex]

@[simp] theorem rightIndex_middle_val (j : Fin k) :
    (rightIndex k r (Sum.inr j)).val = r + j.val := by simp [rightIndex]

/-- Case (II), an actual subgroup of the published total mirabolic. -/
def leftSubgroup (k r : ℕ) (R : Type u) [CommRing R] : Subgroup (mirabolic (k + r) R) :=
  (TwoBlock.upper k (r + 1) R).comap
    (((reindex (R := R) (leftIndex k r)).symm.toMonoidHom).comp (mirabolic (k + r) R).subtype)

/-- Case (III); the mirabolic coordinates are the first `r` and final coordinate. -/
def rightSubgroup (k r : ℕ) (R : Type u) [CommRing R] : Subgroup (mirabolic (k + r) R) :=
  (TwoBlock.upper (r + 1) k R).comap
    (((reindex (R := R) (rightIndex k r)).symm.toMonoidHom).comp (mirabolic (k + r) R).subtype)

theorem mem_leftSubgroup_iff_entry (g : mirabolic (k + r) R) :
    g ∈ leftSubgroup k r R ↔ ∀ i : Fin (r + 1), ∀ j : Fin k,
      g.val.val (leftIndex k r (Sum.inr i)) (leftIndex k r (Sum.inl j)) = 0 :=
  TwoBlock.mem_upper _

theorem mem_rightSubgroup_iff_entry (g : mirabolic (k + r) R) :
    g ∈ rightSubgroup k r R ↔ ∀ i : Fin k, ∀ j : Fin (r + 1),
      g.val.val (rightIndex k r (Sum.inr i)) (rightIndex k r (Sum.inl j)) = 0 :=
  TwoBlock.mem_upper _

/-- The actual two-block matrix in the case (II) coordinates. -/
def leftBlocks : leftSubgroup k r R →* TwoBlock.upper k (r + 1) R :=
  ((((reindex (R := R) (leftIndex k r)).symm.toMonoidHom).comp
    (mirabolic (k + r) R).subtype).comp (leftSubgroup k r R).subtype).codRestrict _
      fun g => g.property

/-- The actual two-block matrix in the case (III) coordinates. -/
def rightBlocks : rightSubgroup k r R →* TwoBlock.upper (r + 1) k R :=
  ((((reindex (R := R) (rightIndex k r)).symm.toMonoidHom).comp
    (mirabolic (k + r) R).subtype).comp (rightSubgroup k r R).subtype).codRestrict _
      fun g => g.property

@[simp] theorem leftBlocks_apply (g : leftSubgroup k r R) (i j : Fin k ⊕ Fin (r + 1)) :
    (leftBlocks g).val.val i j = g.val.val.val (leftIndex k r i) (leftIndex k r j) := rfl

@[simp] theorem rightBlocks_apply (g : rightSubgroup k r R) (i j : Fin (r + 1) ⊕ Fin k) :
    (rightBlocks g).val.val i j = g.val.val.val (rightIndex k r i) (rightIndex k r j) := rfl

private theorem left_diagonal_mem (g : leftSubgroup k r R) :
    (TwoBlock.projection (leftBlocks g)).2 ∈ mirabolic r R := by
  intro j
  change g.val.val.val (leftIndex k r (Sum.inr (Fin.last r)))
    (leftIndex k r (Sum.inr j)) = _
  rw [leftIndex_last, g.val.property]
  simp only [← leftIndex_last (k := k) (r := r), Equiv.apply_eq_iff_eq, Sum.inr.injEq]

private theorem right_diagonal_mem (g : rightSubgroup k r R) :
    (TwoBlock.projection (rightBlocks g)).1 ∈ mirabolic r R := by
  intro j
  change g.val.val.val (rightIndex k r (Sum.inl (Fin.last r)))
    (rightIndex k r (Sum.inl j)) = _
  rw [rightIndex_last, g.val.property]
  simp only [← rightIndex_last (k := k) (r := r), Equiv.apply_eq_iff_eq, Sum.inl.injEq]

/-- Extracted diagonal blocks, with inverse blocks extracted from the actual inverse. -/
def leftProjection : leftSubgroup k r R →* Langlands.GeneralLinear k R × mirabolic r R :=
  ((MonoidHom.fst _ _).comp (TwoBlock.projection.comp leftBlocks)).prod
    (((MonoidHom.snd _ _).comp (TwoBlock.projection.comp leftBlocks)).codRestrict
      (mirabolic r R) left_diagonal_mem)

/-- Extracted first-and-final mirabolic block and middle general-linear block. -/
def rightProjection : rightSubgroup k r R →* mirabolic r R × Langlands.GeneralLinear k R :=
  (((MonoidHom.fst _ _).comp (TwoBlock.projection.comp rightBlocks)).codRestrict
    (mirabolic r R) right_diagonal_mem).prod
    ((MonoidHom.snd _ _).comp (TwoBlock.projection.comp rightBlocks))

@[simp] theorem leftProjection_gl_apply (g : leftSubgroup k r R) (i j : Fin k) :
    (leftProjection g).1.val i j =
      g.val.val.val (leftIndex k r (Sum.inl i)) (leftIndex k r (Sum.inl j)) := rfl

@[simp] theorem leftProjection_mirabolic_apply (g : leftSubgroup k r R) (i j : Fin (r + 1)) :
    (leftProjection g).2.val.val i j =
      g.val.val.val (leftIndex k r (Sum.inr i)) (leftIndex k r (Sum.inr j)) := rfl

@[simp] theorem rightProjection_mirabolic_apply (g : rightSubgroup k r R) (i j : Fin (r + 1)) :
    (rightProjection g).1.val.val i j =
      g.val.val.val (rightIndex k r (Sum.inl i)) (rightIndex k r (Sum.inl j)) := rfl

@[simp] theorem rightProjection_gl_apply (g : rightSubgroup k r R) (i j : Fin k) :
    (rightProjection g).2.val i j =
      g.val.val.val (rightIndex k r (Sum.inr i)) (rightIndex k r (Sum.inr j)) := rfl

private theorem reindex_mem_mirabolic {a b t : ℕ}
    (e : Fin a ⊕ Fin b ≃ Fin (t + 1)) (s : Fin a ⊕ Fin b) (he : e s = Fin.last t)
    (g : Matrix.GeneralLinearGroup (Fin a ⊕ Fin b) R)
    (hg : ∀ j, g.val s j = if j = s then 1 else 0) :
    reindex e g ∈ mirabolic t R := by
  intro j
  obtain ⟨j, rfl⟩ := e.surjective j
  rw [← he]
  change g.val (e.symm (e s)) (e.symm (e j)) = _
  simpa only [Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq] using hg j

/-- Full upper rectangle, including the final column, in case (II). -/
def leftMatrix (a : Langlands.GeneralLinear k R) (p : mirabolic r R)
    (Z : Matrix (Fin k) (Fin (r + 1)) R) : leftSubgroup k r R :=
  ⟨⟨reindex (leftIndex k r) (TwoBlock.matrix a p.val Z).val,
      reindex_mem_mirabolic _ (Sum.inr (Fin.last r)) leftIndex_last _ (by
        intro j
        rcases j with j | j
        · simp [TwoBlock.matrix]
        · simpa [TwoBlock.matrix] using p.property j)⟩,
    by change (reindex (leftIndex k r)).symm
        (reindex (leftIndex k r) (TwoBlock.matrix a p.val Z).val) ∈ TwoBlock.upper k (r + 1) R
       simpa only [MulEquiv.symm_apply_apply] using (TwoBlock.matrix a p.val Z).property⟩

/-- Append a zero final row to the case (III) rectangle. -/
def extendRectangle (X : Matrix (Fin r) (Fin k) R) : Matrix (Fin (r + 1)) (Fin k) R :=
  fun i j => Fin.lastCases 0 (fun i => X i j) i

@[simp] theorem extendRectangle_first (X : Matrix (Fin r) (Fin k) R) (i : Fin r) (j : Fin k) :
    extendRectangle X i.castSucc j = X i j := by simp [extendRectangle]

@[simp] theorem extendRectangle_last (X : Matrix (Fin r) (Fin k) R) (j : Fin k) :
    extendRectangle X (Fin.last r) j = 0 := by simp [extendRectangle]

/-- The case (III) matrix: its upper-right block has zero final row. -/
def rightMatrix (p : mirabolic r R) (a : Langlands.GeneralLinear k R)
    (X : Matrix (Fin r) (Fin k) R) : rightSubgroup k r R :=
  ⟨⟨reindex (rightIndex k r) (TwoBlock.matrix p.val a (extendRectangle X)).val,
      reindex_mem_mirabolic _ (Sum.inl (Fin.last r)) rightIndex_last _ (by
        intro j
        rcases j with j | j
        · simpa [TwoBlock.matrix] using p.property j
        · simp [TwoBlock.matrix])⟩,
    by change (reindex (rightIndex k r)).symm
        (reindex (rightIndex k r) (TwoBlock.matrix p.val a (extendRectangle X)).val) ∈ TwoBlock.upper (r + 1) k R
       simpa only [MulEquiv.symm_apply_apply] using
        (TwoBlock.matrix p.val a (extendRectangle X)).property⟩

/-- Literal entries of the case (II) matrix in its stated partition. -/
theorem leftMatrix_apply (a : Langlands.GeneralLinear k R) (p : mirabolic r R)
    (Z : Matrix (Fin k) (Fin (r + 1)) R) (i j : Fin k ⊕ Fin (r + 1)) :
    (leftMatrix a p Z).val.val.val (leftIndex k r i) (leftIndex k r j) =
      Matrix.fromBlocks a.val Z 0 p.val.val i j := by
  change Matrix.fromBlocks a.val Z 0 p.val.val
    ((leftIndex k r).symm (leftIndex k r i)) ((leftIndex k r).symm (leftIndex k r j)) = _
  simp only [Equiv.symm_apply_apply]

/-- Literal entries of the case (III) matrix, including the zero final row of `X`. -/
theorem rightMatrix_apply (p : mirabolic r R) (a : Langlands.GeneralLinear k R)
    (X : Matrix (Fin r) (Fin k) R) (i j : Fin (r + 1) ⊕ Fin k) :
    (rightMatrix p a X).val.val.val (rightIndex k r i) (rightIndex k r j) =
      Matrix.fromBlocks p.val.val (extendRectangle X) 0 a.val i j := by
  change Matrix.fromBlocks p.val.val (extendRectangle X) 0 a.val
    ((rightIndex k r).symm (rightIndex k r i)) ((rightIndex k r).symm (rightIndex k r j)) = _
  simp only [Equiv.symm_apply_apply]

@[simp] theorem leftBlocks_matrix (a : Langlands.GeneralLinear k R) (p : mirabolic r R)
    (Z : Matrix (Fin k) (Fin (r + 1)) R) :
    leftBlocks (leftMatrix a p Z) = TwoBlock.matrix a p.val Z :=
  Subtype.ext ((reindex (leftIndex k r)).symm_apply_apply _)

@[simp] theorem rightBlocks_matrix (p : mirabolic r R) (a : Langlands.GeneralLinear k R)
    (X : Matrix (Fin r) (Fin k) R) :
    rightBlocks (rightMatrix p a X) = TwoBlock.matrix p.val a (extendRectangle X) :=
  Subtype.ext ((reindex (rightIndex k r)).symm_apply_apply _)

@[simp] theorem leftProjection_matrix (a : Langlands.GeneralLinear k R) (p : mirabolic r R)
    (Z : Matrix (Fin k) (Fin (r + 1)) R) : leftProjection (leftMatrix a p Z) = (a, p) := by
  apply Prod.ext
  · change (TwoBlock.projection (leftBlocks (leftMatrix a p Z))).1 = a
    rw [leftBlocks_matrix, TwoBlock.projection_matrix]
  · apply Subtype.ext
    change (TwoBlock.projection (leftBlocks (leftMatrix a p Z))).2 = p.val
    rw [leftBlocks_matrix, TwoBlock.projection_matrix]

@[simp] theorem rightProjection_matrix (p : mirabolic r R) (a : Langlands.GeneralLinear k R)
    (X : Matrix (Fin r) (Fin k) R) : rightProjection (rightMatrix p a X) = (p, a) := by
  apply Prod.ext
  · apply Subtype.ext
    change (TwoBlock.projection (rightBlocks (rightMatrix p a X))).1 = p.val
    rw [rightBlocks_matrix, TwoBlock.projection_matrix]
  · change (TwoBlock.projection (rightBlocks (rightMatrix p a X))).2 = a
    rw [rightBlocks_matrix, TwoBlock.projection_matrix]

private theorem leftBlocks_injective : Function.Injective (leftBlocks (k := k) (r := r) (R := R)) := by
  intro g h H
  apply Subtype.ext
  apply Subtype.ext
  exact (reindex (leftIndex k r)).symm.injective (congrArg Subtype.val H)

private theorem rightBlocks_injective : Function.Injective (rightBlocks (k := k) (r := r) (R := R)) := by
  intro g h H
  apply Subtype.ext
  apply Subtype.ext
  exact (reindex (rightIndex k r)).symm.injective (congrArg Subtype.val H)

/-- The split block diagonal inclusion in case (II). -/
def leftSection : (Langlands.GeneralLinear k R × mirabolic r R) →* leftSubgroup k r R where
  toFun q := leftMatrix q.1 q.2 0
  map_one' := leftBlocks_injective (by
    simp only [leftBlocks_matrix, map_one]
    exact (TwoBlock.sectionMap (a := k) (b := r + 1) (R := R)).map_one)
  map_mul' q t := leftBlocks_injective (by
    simp only [leftBlocks_matrix, map_mul]
    exact TwoBlock.sectionMap.map_mul (q.1, q.2.val) (t.1, t.2.val))

/-- The split inclusion in case (III), with mirabolic final coordinate moved to the end. -/
def rightSection : (mirabolic r R × Langlands.GeneralLinear k R) →* rightSubgroup k r R where
  toFun q := rightMatrix q.1 q.2 0
  map_one' := rightBlocks_injective (by
    simp only [rightBlocks_matrix, map_one]
    have h : extendRectangle (0 : Matrix (Fin r) (Fin k) R) = 0 := by
      ext i j; exact Fin.lastCases (by simp) (fun i => by simp) i
    rw [h]
    exact (TwoBlock.sectionMap (a := r + 1) (b := k) (R := R)).map_one)
  map_mul' q t := rightBlocks_injective (by
    simp only [rightBlocks_matrix, map_mul]
    have h : extendRectangle (0 : Matrix (Fin r) (Fin k) R) = 0 := by
      ext i j; exact Fin.lastCases (by simp) (fun i => by simp) i
    rw [h]
    exact TwoBlock.sectionMap.map_mul (q.1.val, q.2) (t.1.val, t.2))

@[simp] theorem leftProjection_section (q : Langlands.GeneralLinear k R × mirabolic r R) :
    leftProjection (leftSection q) = q := leftProjection_matrix _ _ _

@[simp] theorem rightProjection_section (q : mirabolic r R × Langlands.GeneralLinear k R) :
    rightProjection (rightSection q) = q := rightProjection_matrix _ _ _


/-- The literal upper-right block of a case (II) element. -/
def leftOffDiagonal (g : leftSubgroup k r R) : Matrix (Fin k) (Fin (r + 1)) R :=
  TwoBlock.B (leftBlocks g)

/-- The case (III) rectangle omits the final row of the reindexed upper-right block. -/
def rightOffDiagonal (g : rightSubgroup k r R) : Matrix (Fin r) (Fin k) R :=
  (TwoBlock.B (rightBlocks g)).submatrix Fin.castSucc id

private theorem right_B_last (g : rightSubgroup k r R) (j : Fin k) :
    TwoBlock.B (rightBlocks g) (Fin.last r) j = 0 := by
  change g.val.val.val (rightIndex k r (Sum.inl (Fin.last r)))
    (rightIndex k r (Sum.inr j)) = 0
  rw [rightIndex_last, g.val.property]
  simp only [← rightIndex_last (k := k) (r := r), Equiv.apply_eq_iff_eq,
    Sum.inr_ne_inl, ↓reduceIte]

private theorem extend_rightOffDiagonal (g : rightSubgroup k r R) :
    extendRectangle (rightOffDiagonal g) = TwoBlock.B (rightBlocks g) := by
  ext i j
  exact Fin.lastCases (by simp [right_B_last]) (fun i => by
    simp [rightOffDiagonal, Matrix.submatrix_apply]) i

theorem leftMatrix_parts (g : leftSubgroup k r R) :
    leftMatrix (leftProjection g).1 (leftProjection g).2 (leftOffDiagonal g) = g := by
  apply leftBlocks_injective
  rw [leftBlocks_matrix]
  exact TwoBlock.matrix_parts (leftBlocks g)

theorem rightMatrix_parts (g : rightSubgroup k r R) :
    rightMatrix (rightProjection g).1 (rightProjection g).2 (rightOffDiagonal g) = g := by
  apply rightBlocks_injective
  rw [rightBlocks_matrix, extend_rightOffDiagonal]
  exact TwoBlock.matrix_parts (rightBlocks g)

@[simp] theorem leftOffDiagonal_matrix (a : Langlands.GeneralLinear k R) (p : mirabolic r R)
    (Z : Matrix (Fin k) (Fin (r + 1)) R) : leftOffDiagonal (leftMatrix a p Z) = Z := by
  simp [leftOffDiagonal, TwoBlock.B, TwoBlock.matrix]

@[simp] theorem rightOffDiagonal_matrix (p : mirabolic r R) (a : Langlands.GeneralLinear k R)
    (X : Matrix (Fin r) (Fin k) R) : rightOffDiagonal (rightMatrix p a X) = X := by
  ext i j
  simp [rightOffDiagonal, TwoBlock.B, TwoBlock.matrix]

/-- The actual rectangular radical in case (II), as the projection kernel. -/
def leftKernel (k r : ℕ) (R : Type u) [CommRing R] : Subgroup (leftSubgroup k r R) :=
  leftProjection.ker

/-- The actual rectangular radical in case (III), as the projection kernel. -/
def rightKernel (k r : ℕ) (R : Type u) [CommRing R] : Subgroup (rightSubgroup k r R) :=
  rightProjection.ker

instance leftKernel_normal : (leftKernel k r R).Normal := MonoidHom.normal_ker _
instance rightKernel_normal : (rightKernel k r R).Normal := MonoidHom.normal_ker _

/-- Insert the full `k × (r+1)` unipotent rectangle. -/
def leftUnipotent (Z : Matrix (Fin k) (Fin (r + 1)) R) : leftSubgroup k r R := leftMatrix 1 1 Z

/-- Insert the `r × k` unipotent rectangle. -/
def rightUnipotent (X : Matrix (Fin r) (Fin k) R) : rightSubgroup k r R := rightMatrix 1 1 X

@[simp] theorem leftProjection_unipotent (Z : Matrix (Fin k) (Fin (r + 1)) R) :
    leftProjection (leftUnipotent Z) = 1 := leftProjection_matrix _ _ _

@[simp] theorem rightProjection_unipotent (X : Matrix (Fin r) (Fin k) R) :
    rightProjection (rightUnipotent X) = 1 := rightProjection_matrix _ _ _

@[simp] theorem leftOffDiagonal_unipotent (Z : Matrix (Fin k) (Fin (r + 1)) R) :
    leftOffDiagonal (leftUnipotent Z) = Z := leftOffDiagonal_matrix _ _ _

@[simp] theorem rightOffDiagonal_unipotent (X : Matrix (Fin r) (Fin k) R) :
    rightOffDiagonal (rightUnipotent X) = X := rightOffDiagonal_matrix _ _ _

private theorem extendRectangle_add (X Y : Matrix (Fin r) (Fin k) R) :
    extendRectangle (X + Y) = extendRectangle X + extendRectangle Y := by
  ext i j
  exact Fin.lastCases (by simp) (fun i => by simp) i

@[simp] theorem extendRectangle_zero : extendRectangle (0 : Matrix (Fin r) (Fin k) R) = 0 := by
  ext i j
  exact Fin.lastCases (by simp) (fun i => by simp) i

theorem leftUnipotent_add (X Y : Matrix (Fin k) (Fin (r + 1)) R) :
    leftUnipotent (X + Y) = leftUnipotent X * leftUnipotent Y := by
  apply leftBlocks_injective
  simpa only [leftUnipotent, leftBlocks_matrix, map_mul, TwoBlock.unipotent, Subgroup.coe_one] using TwoBlock.unipotent_add X Y

theorem rightUnipotent_add (X Y : Matrix (Fin r) (Fin k) R) :
    rightUnipotent (X + Y) = rightUnipotent X * rightUnipotent Y := by
  apply rightBlocks_injective
  simpa only [rightUnipotent, rightBlocks_matrix, map_mul, extendRectangle_add, TwoBlock.unipotent, Subgroup.coe_one] using
    TwoBlock.unipotent_add (extendRectangle X) (extendRectangle Y)

/-- The kernel consists exactly of these unipotent matrices. -/
theorem mem_leftKernel_iff (g : leftSubgroup k r R) :
    g ∈ leftKernel k r R ↔ g = leftUnipotent (leftOffDiagonal g) := by
  constructor
  · intro hg
    have h : leftProjection g = 1 := hg
    have hp := leftMatrix_parts g
    rw [h] at hp
    exact hp.symm
  · intro hg
    rw [leftKernel, MonoidHom.mem_ker, hg, leftProjection_unipotent]

theorem mem_rightKernel_iff (g : rightSubgroup k r R) :
    g ∈ rightKernel k r R ↔ g = rightUnipotent (rightOffDiagonal g) := by
  constructor
  · intro hg
    have h : rightProjection g = 1 := hg
    have hp := rightMatrix_parts g
    rw [h] at hp
    exact hp.symm
  · intro hg
    rw [rightKernel, MonoidHom.mem_ker, hg, rightProjection_unipotent]

/-- Radical insertion, valued in the actual kernel. -/
def leftKernelElement (Z : Matrix (Fin k) (Fin (r + 1)) R) : leftKernel k r R :=
  ⟨leftUnipotent Z, leftProjection_unipotent Z⟩

/-- Radical insertion, valued in the actual kernel. -/
def rightKernelElement (X : Matrix (Fin r) (Fin k) R) : rightKernel k r R :=
  ⟨rightUnipotent X, rightProjection_unipotent X⟩

@[simp] theorem leftKernelElement_coordinates (g : leftKernel k r R) :
    leftKernelElement (leftOffDiagonal g.val) = g :=
  Subtype.ext ((mem_leftKernel_iff g.val).mp g.property).symm

@[simp] theorem rightKernelElement_coordinates (g : rightKernel k r R) :
    rightKernelElement (rightOffDiagonal g.val) = g :=
  Subtype.ext ((mem_rightKernel_iff g.val).mp g.property).symm

/-- Addition of rectangles is multiplication in the actual kernel. -/
def leftKernelEquiv : leftKernel k r R ≃* Multiplicative (Matrix (Fin k) (Fin (r + 1)) R) where
  toFun g := Multiplicative.ofAdd (leftOffDiagonal g.val)
  invFun Z := leftKernelElement Z.toAdd
  left_inv := leftKernelElement_coordinates
  right_inv Z := congrArg Multiplicative.ofAdd (leftOffDiagonal_unipotent Z.toAdd)
  map_mul' g h := by
    change leftOffDiagonal (g.val * h.val) =
      leftOffDiagonal g.val + leftOffDiagonal h.val
    have hg : leftUnipotent (leftOffDiagonal g.val) = g.val :=
      congrArg Subtype.val (leftKernelElement_coordinates g)
    have hh : leftUnipotent (leftOffDiagonal h.val) = h.val :=
      congrArg Subtype.val (leftKernelElement_coordinates h)
    calc
      leftOffDiagonal (g.val * h.val) =
          leftOffDiagonal (leftUnipotent (leftOffDiagonal g.val) *
            leftUnipotent (leftOffDiagonal h.val)) :=
        congrArg leftOffDiagonal (congrArg₂ (· * ·) hg.symm hh.symm)
      _ = _ := by rw [← leftUnipotent_add, leftOffDiagonal_unipotent]

/-- Addition of rectangles is multiplication in the actual kernel. -/
def rightKernelEquiv : rightKernel k r R ≃* Multiplicative (Matrix (Fin r) (Fin k) R) where
  toFun g := Multiplicative.ofAdd (rightOffDiagonal g.val)
  invFun X := rightKernelElement X.toAdd
  left_inv := rightKernelElement_coordinates
  right_inv X := congrArg Multiplicative.ofAdd (rightOffDiagonal_unipotent X.toAdd)
  map_mul' g h := by
    change rightOffDiagonal (g.val * h.val) =
      rightOffDiagonal g.val + rightOffDiagonal h.val
    have hg : rightUnipotent (rightOffDiagonal g.val) = g.val :=
      congrArg Subtype.val (rightKernelElement_coordinates g)
    have hh : rightUnipotent (rightOffDiagonal h.val) = h.val :=
      congrArg Subtype.val (rightKernelElement_coordinates h)
    calc
      rightOffDiagonal (g.val * h.val) =
          rightOffDiagonal (rightUnipotent (rightOffDiagonal g.val) *
            rightUnipotent (rightOffDiagonal h.val)) :=
        congrArg rightOffDiagonal (congrArg₂ (· * ·) hg.symm hh.symm)
      _ = _ := by rw [← rightUnipotent_add, rightOffDiagonal_unipotent]


/-- Additive spelling of the same actual kernel coordinate equivalence. -/
def leftKernelAddEquiv : Additive (leftKernel k r R) ≃+ Matrix (Fin k) (Fin (r + 1)) R :=
  leftKernelEquiv.toAdditiveLeft

/-- Additive spelling of the same actual kernel coordinate equivalence. -/
def rightKernelAddEquiv : Additive (rightKernel k r R) ≃+ Matrix (Fin r) (Fin k) R :=
  rightKernelEquiv.toAdditiveLeft

/-- The radical factor `g * section(projection g)⁻¹`. -/
def leftRadicalPart (g : leftSubgroup k r R) : leftKernel k r R :=
  ⟨g * (leftSection (leftProjection g))⁻¹, by
    change leftProjection (g * (leftSection (leftProjection g))⁻¹) = 1
    rw [map_mul, map_inv, leftProjection_section, mul_inv_cancel]⟩

/-- Additive rectangle in the unique radical-then-Levi factorization. -/
def leftCoordinates (g : leftSubgroup k r R) : Matrix (Fin k) (Fin (r + 1)) R :=
  leftOffDiagonal (leftRadicalPart g).val

theorem left_factorization (g : leftSubgroup k r R) :
    g = leftUnipotent (leftCoordinates g) * leftSection (leftProjection g) := by
  have h : leftUnipotent (leftCoordinates g) =
      g * (leftSection (leftProjection g))⁻¹ :=
    congrArg Subtype.val (leftKernelElement_coordinates (leftRadicalPart g))
  rw [h, inv_mul_cancel_right]

@[simp] theorem leftRadicalPart_unipotent_section (Z : Matrix (Fin k) (Fin (r + 1)) R)
    (q : Langlands.GeneralLinear k R × mirabolic r R) :
    leftRadicalPart (leftUnipotent Z * leftSection q) = leftKernelElement Z := by
  apply Subtype.ext
  change (leftUnipotent Z * leftSection q) *
    (leftSection (leftProjection (leftUnipotent Z * leftSection q)))⁻¹ = leftUnipotent Z
  simp only [map_mul, leftProjection_unipotent, leftProjection_section, one_mul,
    mul_inv_cancel_right]

@[simp] theorem leftCoordinates_unipotent_section (Z : Matrix (Fin k) (Fin (r + 1)) R)
    (q : Langlands.GeneralLinear k R × mirabolic r R) :
    leftCoordinates (leftUnipotent Z * leftSection q) = Z := by
  rw [leftCoordinates, leftRadicalPart_unipotent_section]
  exact leftOffDiagonal_unipotent Z

/-- Both the radical coordinate and the product factor are uniquely determined. -/
theorem left_factorization_iff (g : leftSubgroup k r R) (Z : Matrix (Fin k) (Fin (r + 1)) R)
    (q : Langlands.GeneralLinear k R × mirabolic r R) :
    g = leftUnipotent Z * leftSection q ↔ Z = leftCoordinates g ∧ q = leftProjection g := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨rfl, rfl⟩
    exact left_factorization g

/-- The actual subgroup has global radical-then-Levi coordinates. -/
def leftFactorizationEquiv : leftSubgroup k r R ≃ (Matrix (Fin k) (Fin (r + 1)) R) × (Langlands.GeneralLinear k R × mirabolic r R) where
  toFun g := (leftCoordinates g, leftProjection g)
  invFun q := leftUnipotent q.1 * leftSection q.2
  left_inv g := (left_factorization g).symm
  right_inv q := by simp

/-- The radical factor `g * section(projection g)⁻¹`. -/
def rightRadicalPart (g : rightSubgroup k r R) : rightKernel k r R :=
  ⟨g * (rightSection (rightProjection g))⁻¹, by
    change rightProjection (g * (rightSection (rightProjection g))⁻¹) = 1
    rw [map_mul, map_inv, rightProjection_section, mul_inv_cancel]⟩

/-- Additive rectangle in the unique radical-then-Levi factorization. -/
def rightCoordinates (g : rightSubgroup k r R) : Matrix (Fin r) (Fin k) R :=
  rightOffDiagonal (rightRadicalPart g).val

theorem right_factorization (g : rightSubgroup k r R) :
    g = rightUnipotent (rightCoordinates g) * rightSection (rightProjection g) := by
  have h : rightUnipotent (rightCoordinates g) =
      g * (rightSection (rightProjection g))⁻¹ :=
    congrArg Subtype.val (rightKernelElement_coordinates (rightRadicalPart g))
  rw [h, inv_mul_cancel_right]

@[simp] theorem rightRadicalPart_unipotent_section (Z : Matrix (Fin r) (Fin k) R)
    (q : mirabolic r R × Langlands.GeneralLinear k R) :
    rightRadicalPart (rightUnipotent Z * rightSection q) = rightKernelElement Z := by
  apply Subtype.ext
  change (rightUnipotent Z * rightSection q) *
    (rightSection (rightProjection (rightUnipotent Z * rightSection q)))⁻¹ = rightUnipotent Z
  simp only [map_mul, rightProjection_unipotent, rightProjection_section, one_mul,
    mul_inv_cancel_right]

@[simp] theorem rightCoordinates_unipotent_section (Z : Matrix (Fin r) (Fin k) R)
    (q : mirabolic r R × Langlands.GeneralLinear k R) :
    rightCoordinates (rightUnipotent Z * rightSection q) = Z := by
  rw [rightCoordinates, rightRadicalPart_unipotent_section]
  exact rightOffDiagonal_unipotent Z

/-- Both the radical coordinate and the product factor are uniquely determined. -/
theorem right_factorization_iff (g : rightSubgroup k r R) (Z : Matrix (Fin r) (Fin k) R)
    (q : mirabolic r R × Langlands.GeneralLinear k R) :
    g = rightUnipotent Z * rightSection q ↔ Z = rightCoordinates g ∧ q = rightProjection g := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨rfl, rfl⟩
    exact right_factorization g

/-- The actual subgroup has global radical-then-Levi coordinates. -/
def rightFactorizationEquiv : rightSubgroup k r R ≃ (Matrix (Fin r) (Fin k) R) × (mirabolic r R × Langlands.GeneralLinear k R) where
  toFun g := (rightCoordinates g, rightProjection g)
  invFun q := rightUnipotent q.1 * rightSection q.2
  left_inv g := (right_factorization g).symm
  right_inv q := by simp

/-- Levi action on the full rectangle in case (II). -/
theorem left_conjugate (q : Langlands.GeneralLinear k R × mirabolic r R)
    (Z : Matrix (Fin k) (Fin (r + 1)) R) :
    leftSection q * leftUnipotent Z * (leftSection q)⁻¹ =
      leftUnipotent (q.1.val * Z * (q.2.val⁻¹).val) := by
  apply leftBlocks_injective
  simpa only [map_mul, map_inv, leftSection, MonoidHom.coe_mk, OneHom.coe_mk,
    leftBlocks_matrix, leftUnipotent, Subgroup.coe_one, TwoBlock.sectionMap,
    TwoBlock.unipotent] using TwoBlock.conjugate_unipotent (q.1, q.2.val) Z

private theorem extendRectangle_action (p : mirabolic r R) (a : Langlands.GeneralLinear k R)
    (X : Matrix (Fin r) (Fin k) R) :
    extendRectangle ((Mirabolic.projection p).val * X * a.val) =
      p.val.val * extendRectangle X * a.val := by
  have h : extendRectangle ((Mirabolic.projection p).val * X) = p.val.val * extendRectangle X := by
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · have hp (t : Fin (r + 1)) : p.val.val (Fin.last r) t =
          if t = Fin.last r then 1 else 0 := p.property t
      simp [Matrix.mul_apply, hp]
    · simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Mirabolic.projection_apply]
  rw [← h]
  ext i j
  exact Fin.lastCases (by simp [Matrix.mul_apply])
    (fun i => by simp [Matrix.mul_apply]) i

/-- The translation column of the mirabolic factor does not enter this action. -/
theorem right_conjugate (q : mirabolic r R × Langlands.GeneralLinear k R)
    (X : Matrix (Fin r) (Fin k) R) :
    rightSection q * rightUnipotent X * (rightSection q)⁻¹ =
      rightUnipotent ((Mirabolic.projection q.1).val * X * (q.2⁻¹).val) := by
  apply rightBlocks_injective
  simpa only [map_mul, map_inv, rightSection, MonoidHom.coe_mk, OneHom.coe_mk,
    rightBlocks_matrix, rightUnipotent, Subgroup.coe_one, TwoBlock.sectionMap,
    TwoBlock.unipotent, extendRectangle_zero, extendRectangle_action] using
      TwoBlock.conjugate_unipotent (q.1.val, q.2) (extendRectangle X)


/-- The split identity as equality of actual homomorphisms. -/
theorem leftProjection_comp_section :
    (leftProjection (k := k) (r := r) (R := R)).comp leftSection = MonoidHom.id _ :=
  MonoidHom.ext leftProjection_section

theorem rightProjection_comp_section :
    (rightProjection (k := k) (r := r) (R := R)).comp rightSection = MonoidHom.id _ :=
  MonoidHom.ext rightProjection_section

theorem leftProjection_surjective : Function.Surjective (leftProjection (k := k) (r := r) (R := R)) :=
  fun q => ⟨leftSection q, leftProjection_section q⟩

theorem rightProjection_surjective : Function.Surjective (rightProjection (k := k) (r := r) (R := R)) :=
  fun q => ⟨rightSection q, rightProjection_section q⟩

@[simp] theorem leftSection_val (q : Langlands.GeneralLinear k R × mirabolic r R) :
    (leftSection q).val.val = reindex (leftIndex k r) (TwoBlock.sectionMap (q.1, q.2.val)).val := rfl

@[simp] theorem rightSection_val (q : mirabolic r R × Langlands.GeneralLinear k R) :
    (rightSection q).val.val = reindex (rightIndex k r) (TwoBlock.sectionMap (q.1.val, q.2)).val := by
  change reindex (rightIndex k r) (TwoBlock.matrix q.1.val q.2 (extendRectangle 0)).val = _
  rw [extendRectangle_zero]
  rfl

section Topology

variable [TopologicalSpace R]

theorem continuous_leftBlocks : Continuous (leftBlocks (k := k) (r := r) (R := R)) :=
  ((reindexContinuous (R := R) (leftIndex k r)).symm.continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

theorem continuous_rightBlocks : Continuous (rightBlocks (k := k) (r := r) (R := R)) :=
  ((reindexContinuous (R := R) (rightIndex k r)).symm.continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

/-- Projection continuity needs only the topology inherited from matrix units. -/
theorem continuous_leftProjection : Continuous (leftProjection (k := k) (r := r) (R := R)) :=
  ((continuous_fst.comp TwoBlock.continuous_projection).comp continuous_leftBlocks).prodMk
    (((continuous_snd.comp TwoBlock.continuous_projection).comp continuous_leftBlocks).subtype_mk _)

theorem continuous_rightProjection : Continuous (rightProjection (k := k) (r := r) (R := R)) :=
  (((continuous_fst.comp TwoBlock.continuous_projection).comp continuous_rightBlocks).subtype_mk _).prodMk
    ((continuous_snd.comp TwoBlock.continuous_projection).comp continuous_rightBlocks)

theorem continuous_leftSection : Continuous (leftSection (k := k) (r := r) (R := R)) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun q => (leftSection q).val.val)
  simp_rw [leftSection_val]
  exact (reindexContinuous (R := R) (leftIndex k r)).continuous.comp
    ((continuous_subtype_val.comp TwoBlock.continuous_section).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

theorem continuous_rightSection : Continuous (rightSection (k := k) (r := r) (R := R)) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun q => (rightSection q).val.val)
  simp_rw [rightSection_val]
  exact (reindexContinuous (R := R) (rightIndex k r)).continuous.comp
    ((continuous_subtype_val.comp TwoBlock.continuous_section).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))

theorem continuous_leftOffDiagonal : Continuous (leftOffDiagonal (k := k) (r := r) (R := R)) :=
  (Units.continuous_val.comp
    (continuous_subtype_val.comp continuous_leftBlocks)).matrix_submatrix _ _

theorem continuous_rightOffDiagonal : Continuous (rightOffDiagonal (k := k) (r := r) (R := R)) :=
  ((Units.continuous_val.comp
    (continuous_subtype_val.comp continuous_rightBlocks)).matrix_submatrix _ _).matrix_submatrix _ _

theorem continuous_extendRectangle : Continuous (extendRectangle (k := k) (r := r) (R := R)) := by
  apply continuous_matrix
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [extendRectangle_last]
    exact continuous_const
  · simp only [extendRectangle_first]
    exact continuous_id.matrix_elem i j

/-- The two defining zero rectangles give closed subgroups for Hausdorff coefficients. -/
theorem leftSubgroup_isClosed [T2Space R] :
    IsClosed (leftSubgroup k r R : Set (mirabolic (k + r) R)) :=
  TwoBlock.isClosed_upper.preimage
    ((reindexContinuous (R := R) (leftIndex k r)).symm.continuous.comp continuous_subtype_val)

theorem rightSubgroup_isClosed [T2Space R] :
    IsClosed (rightSubgroup k r R : Set (mirabolic (k + r) R)) :=
  TwoBlock.isClosed_upper.preimage
    ((reindexContinuous (R := R) (rightIndex k r)).symm.continuous.comp continuous_subtype_val)

variable [IsTopologicalRing R]

theorem continuous_leftUnipotent : Continuous (leftUnipotent (k := k) (r := r) (R := R)) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (reindexContinuous (R := R) (leftIndex k r)).continuous.comp
    (continuous_subtype_val.comp TwoBlock.continuous_unipotent)

theorem continuous_rightUnipotent : Continuous (rightUnipotent (k := k) (r := r) (R := R)) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (reindexContinuous (R := R) (rightIndex k r)).continuous.comp
    ((continuous_subtype_val.comp TwoBlock.continuous_unipotent).comp continuous_extendRectangle)

theorem continuous_leftRadicalPart : Continuous (leftRadicalPart (k := k) (r := r) (R := R)) :=
  (continuous_id.mul (continuous_leftSection.comp continuous_leftProjection).inv).subtype_mk _

theorem continuous_rightRadicalPart : Continuous (rightRadicalPart (k := k) (r := r) (R := R)) :=
  (continuous_id.mul (continuous_rightSection.comp continuous_rightProjection).inv).subtype_mk _

theorem continuous_leftCoordinates : Continuous (leftCoordinates (k := k) (r := r) (R := R)) :=
  continuous_leftOffDiagonal.comp (continuous_subtype_val.comp continuous_leftRadicalPart)

theorem continuous_rightCoordinates : Continuous (rightCoordinates (k := k) (r := r) (R := R)) :=
  continuous_rightOffDiagonal.comp (continuous_subtype_val.comp continuous_rightRadicalPart)

/-- The global case (II) factorization respects the inherited topologies. -/
def leftFactorizationHomeomorph : leftSubgroup k r R ≃ₜ
    Matrix (Fin k) (Fin (r + 1)) R × (Langlands.GeneralLinear k R × mirabolic r R) where
  toEquiv := leftFactorizationEquiv
  continuous_toFun := continuous_leftCoordinates.prodMk continuous_leftProjection
  continuous_invFun :=
    (continuous_leftUnipotent.comp continuous_fst).mul (continuous_leftSection.comp continuous_snd)

/-- The global case (III) factorization respects the inherited topologies. -/
def rightFactorizationHomeomorph : rightSubgroup k r R ≃ₜ
    Matrix (Fin r) (Fin k) R × (mirabolic r R × Langlands.GeneralLinear k R) where
  toEquiv := rightFactorizationEquiv
  continuous_toFun := continuous_rightCoordinates.prodMk continuous_rightProjection
  continuous_invFun :=
    (continuous_rightUnipotent.comp continuous_fst).mul (continuous_rightSection.comp continuous_snd)

/-- The case (II) kernel has its ordinary additive rectangle topology. -/
def leftKernelHomeomorph : leftKernel k r R ≃ₜ Matrix (Fin k) (Fin (r + 1)) R where
  toEquiv := leftKernelEquiv.toEquiv.trans Multiplicative.toAdd
  continuous_toFun := continuous_leftOffDiagonal.comp continuous_subtype_val
  continuous_invFun := continuous_leftUnipotent.subtype_mk _

/-- The case (III) kernel has its ordinary additive rectangle topology. -/
def rightKernelHomeomorph : rightKernel k r R ≃ₜ Matrix (Fin r) (Fin k) R where
  toEquiv := rightKernelEquiv.toEquiv.trans Multiplicative.toAdd
  continuous_toFun := continuous_rightOffDiagonal.comp continuous_subtype_val
  continuous_invFun := continuous_rightUnipotent.subtype_mk _

end Topology

end Langlands.GeneralLinear.Mirabolic.MixedProduct
