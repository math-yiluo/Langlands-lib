import Langlands.Group.GL.RankMaps
import Langlands.Group.GL.TriangularParabolic

/-! # Actual lower-block coordinates for the display in JPSS Lemma 9.2 -/

namespace Langlands.GeneralLinear

universe u

/-- The subgroup of actual invertible lower triangular matrices, with its subtype topology. -/
def lowerTriangularSubgroup (n : ℕ) (R : Type u) [CommRing R] :
    Subgroup (Langlands.GeneralLinear n R) where
  carrier := {g | g.val.IsLowerTriangular}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' ha hb := ha.mul hb
  inv_mem' := by
    intro g hg
    let := g.invertible
    change (g⁻¹).val.IsLowerTriangular
    simpa only [Matrix.GeneralLinearGroup.coe_inv] using
      Matrix.blockTriangular_inv_of_blockTriangular hg

@[simp] theorem mem_lowerTriangularSubgroup_iff {n : ℕ} {R : Type u} [CommRing R]
    (g : Langlands.GeneralLinear n R) :
    g ∈ lowerTriangularSubgroup n R ↔ ∀ i j : Fin n, i < j → g i j = 0 := Iff.rfl

variable {R : Type u} [CommRing R] {a d c : ℕ}

private def lowerBlockUnit (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : Langlands.GeneralLinear d R) :
    Matrix.GeneralLinearGroup (Fin a ⊕ Fin d) R where
  val := Matrix.fromBlocks g.val 0 x h.val
  inv := Matrix.fromBlocks (g⁻¹).val 0 (-(h⁻¹).val * x * (g⁻¹).val) (h⁻¹).val
  val_inv := by
    simp [Matrix.fromBlocks_multiply, Matrix.mul_assoc, ← Matrix.fromBlocks_one]
  inv_val := by
    simp [Matrix.fromBlocks_multiply, Matrix.mul_assoc, ← Matrix.fromBlocks_one]

/-- The actual two-block matrix `[[g,0],[x,h]]` in standard consecutive coordinates. -/
def lowerBlockPair (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) :
    Langlands.GeneralLinear (a + d) R :=
  reindex finSumFinEquiv (lowerBlockUnit g x h.val)

/-- The matrix `[[g,0,0],[x,h,0],[0,0,I_c]]`; this is a coordinate map, not a
homomorphism from the direct product of its three parameters. -/
def lowerBlockLocalization (c : ℕ) (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) :
    Langlands.GeneralLinear (a + d + c) R :=
  rankInclusion c (lowerBlockPair g x h)

@[simp] theorem lowerBlockPair_11 (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) (i j : Fin a) :
    lowerBlockPair g x h (i.castAdd d) (j.castAdd d) = g i j := by
  change Matrix.fromBlocks g.val 0 x h.val.val
    (finSumFinEquiv.symm (i.castAdd d)) (finSumFinEquiv.symm (j.castAdd d)) = _
  simp

@[simp] theorem lowerBlockPair_12 (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R)
    (i : Fin a) (j : Fin d) :
    lowerBlockPair g x h (i.castAdd d) (j.natAdd a) = 0 := by
  change Matrix.fromBlocks g.val 0 x h.val.val
    (finSumFinEquiv.symm (i.castAdd d)) (finSumFinEquiv.symm (j.natAdd a)) = _
  simp

@[simp] theorem lowerBlockPair_21 (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R)
    (i : Fin d) (j : Fin a) :
    lowerBlockPair g x h (i.natAdd a) (j.castAdd d) = x i j := by
  change Matrix.fromBlocks g.val 0 x h.val.val
    (finSumFinEquiv.symm (i.natAdd a)) (finSumFinEquiv.symm (j.castAdd d)) = _
  simp

@[simp] theorem lowerBlockPair_22 (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) (i j : Fin d) :
    lowerBlockPair g x h (i.natAdd a) (j.natAdd a) = h.val i j := by
  change Matrix.fromBlocks g.val 0 x h.val.val
    (finSumFinEquiv.symm (i.natAdd a)) (finSumFinEquiv.symm (j.natAdd a)) = _
  simp

/-- First-block coordinate embedding into the left-associated total rank. -/
def lowerBlockFirst (d c : ℕ) (i : Fin a) : Fin (a + d + c) := (i.castAdd d).castAdd c
/-- Middle-block coordinate embedding, with offset `a`. -/
def lowerBlockMiddle (a c : ℕ) (i : Fin d) : Fin (a + d + c) := (i.natAdd a).castAdd c
/-- Final-block coordinate embedding, with offset `a+d`. -/
def lowerBlockLast (a d : ℕ) (i : Fin c) : Fin (a + d + c) := i.natAdd (a + d)

@[simp] theorem lowerBlockLocalization_11 (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R)
    (i : Fin a) (j : Fin a) :
    lowerBlockLocalization c g x h (lowerBlockFirst d c i) (lowerBlockFirst d c j) = g i j := by
  simp [lowerBlockLocalization, rankInclusion, lowerBlockFirst]

@[simp] theorem lowerBlockLocalization_12 (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R)
    (i : Fin a) (j : Fin d) :
    lowerBlockLocalization c g x h (lowerBlockFirst d c i) (lowerBlockMiddle a c j) = 0 := by
  simp [lowerBlockLocalization, rankInclusion, lowerBlockFirst, lowerBlockMiddle]

@[simp] theorem lowerBlockLocalization_13 (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R)
    (i : Fin a) (j : Fin c) :
    lowerBlockLocalization c g x h (lowerBlockFirst d c i) (lowerBlockLast a d j) = 0 := by
  simp [lowerBlockLocalization, rankInclusion, lowerBlockFirst, lowerBlockLast]

@[simp] theorem lowerBlockLocalization_21 (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R)
    (i : Fin d) (j : Fin a) :
    lowerBlockLocalization c g x h (lowerBlockMiddle a c i) (lowerBlockFirst d c j) = x i j := by
  simp [lowerBlockLocalization, rankInclusion, lowerBlockFirst, lowerBlockMiddle]

@[simp] theorem lowerBlockLocalization_22 (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R)
    (i : Fin d) (j : Fin d) :
    lowerBlockLocalization c g x h (lowerBlockMiddle a c i) (lowerBlockMiddle a c j) = h.val i j := by
  simp [lowerBlockLocalization, rankInclusion, lowerBlockMiddle]

@[simp] theorem lowerBlockLocalization_23 (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R)
    (i : Fin d) (j : Fin c) :
    lowerBlockLocalization c g x h (lowerBlockMiddle a c i) (lowerBlockLast a d j) = 0 := by
  simp [lowerBlockLocalization, rankInclusion, lowerBlockMiddle, lowerBlockLast]

@[simp] theorem lowerBlockLocalization_31 (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R)
    (i : Fin c) (j : Fin a) :
    lowerBlockLocalization c g x h (lowerBlockLast a d i) (lowerBlockFirst d c j) = 0 := by
  simp [lowerBlockLocalization, rankInclusion, lowerBlockFirst, lowerBlockLast]

@[simp] theorem lowerBlockLocalization_32 (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R)
    (i : Fin c) (j : Fin d) :
    lowerBlockLocalization c g x h (lowerBlockLast a d i) (lowerBlockMiddle a c j) = 0 := by
  simp [lowerBlockLocalization, rankInclusion, lowerBlockMiddle, lowerBlockLast]

@[simp] theorem lowerBlockLocalization_33 (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R)
    (i : Fin c) (j : Fin c) :
    lowerBlockLocalization c g x h (lowerBlockLast a d i) (lowerBlockLast a d j) = (1 : Matrix (Fin c) (Fin c) R) i j := by
  simp [lowerBlockLocalization, rankInclusion, lowerBlockLast]

/-- The inverse is obtained by inverting the two diagonal blocks and replacing
`x` by `-h⁻¹*x*g⁻¹`. -/
theorem lowerBlockPair_inv (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) :
    (lowerBlockPair g x h)⁻¹ =
      lowerBlockPair g⁻¹ (-h.val⁻¹.val * x * g⁻¹.val) h⁻¹ := by
  rw [lowerBlockPair, ← map_inv]
  apply Units.ext
  rfl

/-- Explicit inverse of the three-block chart. -/
theorem lowerBlockLocalization_inv (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) :
    (lowerBlockLocalization c g x h)⁻¹ =
      lowerBlockLocalization c g⁻¹ (-h.val⁻¹.val * x * g⁻¹.val) h⁻¹ := by
  rw [lowerBlockLocalization, ← map_inv, lowerBlockPair_inv]
  rfl

/-- The determinant is the product of the two nontrivial diagonal determinants. -/
theorem det_lowerBlockLocalization (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) :
    Matrix.det (lowerBlockLocalization c g x h).val =
      Matrix.det g.val * Matrix.det h.val.val := by
  change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (lowerBlockPair g x h).val 0 0
      (1 : Matrix (Fin c) (Fin c) R))) = _
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks g.val 0 x h.val.val)) = _
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]

/-- The three raw coordinate spaces, with their usual product topology. -/
abbrev LowerBlockParameters (a d : ℕ) (R : Type u) [CommRing R] :=
  Langlands.GeneralLinear a R × Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R

/-- Leading square matrix projection, defined on the whole ambient group. -/
def lowerBlockLeading (k : Langlands.GeneralLinear (a + d + c) R) :
    Matrix (Fin a) (Fin a) R :=
  k.val.submatrix (lowerBlockFirst d c) (lowerBlockFirst d c)

/-- Lower-left rectangular projection, defined on the whole ambient group. -/
def lowerBlockRectangle (k : Langlands.GeneralLinear (a + d + c) R) :
    Matrix (Fin d) (Fin a) R :=
  k.val.submatrix (lowerBlockMiddle a c) (lowerBlockFirst d c)

/-- Middle square matrix projection, defined on the whole ambient group. -/
def lowerBlockDiagonal (k : Langlands.GeneralLinear (a + d + c) R) :
    Matrix (Fin d) (Fin d) R :=
  k.val.submatrix (lowerBlockMiddle a c) (lowerBlockMiddle a c)

@[simp] theorem lowerBlockLeading_chart (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) :
    lowerBlockLeading (lowerBlockLocalization c g x h) = g.val := by
  ext i j
  exact lowerBlockLocalization_11 g x h i j

@[simp] theorem lowerBlockRectangle_chart (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) :
    lowerBlockRectangle (lowerBlockLocalization c g x h) = x := by
  ext i j
  exact lowerBlockLocalization_21 g x h i j

@[simp] theorem lowerBlockDiagonal_chart (g : Langlands.GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (h : lowerTriangularSubgroup d R) :
    lowerBlockDiagonal (lowerBlockLocalization c g x h) = h.val.val := by
  ext i j
  exact lowerBlockLocalization_22 g x h i j

/-- Each parameter is uniquely recoverable from the displayed matrix. -/
theorem lowerBlockLocalization_injective (c : ℕ) :
    Function.Injective (fun p : LowerBlockParameters a d R =>
      lowerBlockLocalization c p.1 p.2.1 p.2.2) := by
  rintro ⟨g,x,h⟩ ⟨g',x',h'⟩ he
  have hg := congrArg lowerBlockLeading he
  have hx := congrArg lowerBlockRectangle he
  have hh := congrArg lowerBlockDiagonal he
  simp only [lowerBlockLeading_chart] at hg
  simp only [lowerBlockRectangle_chart] at hx
  simp only [lowerBlockDiagonal_chart] at hh
  exact Prod.ext (Units.ext hg) (Prod.ext hx (Subtype.ext (Units.ext hh)))

/-- The image of the actual coordinate chart, as a subspace of the ambient GL. -/
def lowerBlockImage (a d c : ℕ) (R : Type u) [CommRing R] :
    Set (Langlands.GeneralLinear (a + d + c) R) :=
  Set.range (fun p : LowerBlockParameters a d R => lowerBlockLocalization c p.1 p.2.1 p.2.2)

/-- Recover the leading invertible matrix from a matrix in the chart image. -/
def lowerBlockRecoverG (k : lowerBlockImage a d c R) : Langlands.GeneralLinear a R where
  val := lowerBlockLeading k.val
  inv := lowerBlockLeading k.val⁻¹
  val_inv := by
    rcases k with ⟨_, ⟨⟨g,x,h⟩, rfl⟩⟩
    simp [lowerBlockLocalization_inv]
  inv_val := by
    rcases k with ⟨_, ⟨⟨g,x,h⟩, rfl⟩⟩
    simp [lowerBlockLocalization_inv]

/-- Recover the actual lower triangular middle block from the chart image. -/
def lowerBlockRecoverH (k : lowerBlockImage a d c R) : lowerTriangularSubgroup d R :=
  ⟨{ val := lowerBlockDiagonal k.val
     inv := lowerBlockDiagonal k.val⁻¹
     val_inv := by
       rcases k with ⟨_, ⟨⟨g,x,h⟩, rfl⟩⟩
       simp [lowerBlockLocalization_inv]
     inv_val := by
       rcases k with ⟨_, ⟨⟨g,x,h⟩, rfl⟩⟩
       simp [lowerBlockLocalization_inv] }, by
    rcases k with ⟨_, ⟨⟨g,x,h⟩, rfl⟩⟩
    change (lowerBlockDiagonal (lowerBlockLocalization c g x h)).IsLowerTriangular
    rw [lowerBlockDiagonal_chart]
    exact h.property⟩

/-- The genuine inverse coordinate map on the chart image. -/
def lowerBlockCoordinates (k : lowerBlockImage a d c R) : LowerBlockParameters a d R :=
  (lowerBlockRecoverG k, lowerBlockRectangle k.val, lowerBlockRecoverH k)

@[simp] theorem lowerBlockCoordinates_chart (p : LowerBlockParameters a d R) :
    lowerBlockCoordinates (a := a) (d := d) (c := c)
      ⟨lowerBlockLocalization c p.1 p.2.1 p.2.2, ⟨p,rfl⟩⟩ = p := by
  apply Prod.ext
  · apply Units.ext
    exact lowerBlockLeading_chart _ _ _
  · apply Prod.ext
    · exact lowerBlockRectangle_chart _ _ _
    · apply Subtype.ext
      apply Units.ext
      exact lowerBlockDiagonal_chart _ _ _

/-- Reassembly recovers every point of the chart image; no ambient decomposition
hypothesis is asserted. -/
theorem lowerBlockLocalization_coordinates (k : lowerBlockImage a d c R) :
    lowerBlockLocalization c (lowerBlockCoordinates k).1 (lowerBlockCoordinates k).2.1
      (lowerBlockCoordinates k).2.2 = k.val := by
  rcases k with ⟨_, ⟨p, rfl⟩⟩
  rw [lowerBlockCoordinates_chart]

section Topology

variable [TopologicalSpace R]

/-- Ambient matrix-coordinate projections are continuous without ring-topology hypotheses. -/
theorem continuous_lowerBlockLeading :
    Continuous (lowerBlockLeading (R := R) (a := a) (d := d) (c := c)) :=
  Units.continuous_val.matrix_submatrix _ _

theorem continuous_lowerBlockRectangle :
    Continuous (lowerBlockRectangle (R := R) (a := a) (d := d) (c := c)) :=
  Units.continuous_val.matrix_submatrix _ _

theorem continuous_lowerBlockDiagonal :
    Continuous (lowerBlockDiagonal (R := R) (a := a) (d := d) (c := c)) :=
  Units.continuous_val.matrix_submatrix _ _

/-- Recovery of the leading unit is continuous in the subspace topology. -/
theorem continuous_lowerBlockRecoverG :
    Continuous (lowerBlockRecoverG (R := R) (a := a) (d := d) (c := c)) := by
  apply Units.continuous_iff.mpr
  exact ⟨continuous_lowerBlockLeading.comp continuous_subtype_val,
    (Units.continuous_coe_inv.matrix_submatrix _ _).comp continuous_subtype_val⟩

/-- Recovery of the lower triangular unit is continuous in its inherited topology. -/
theorem continuous_lowerBlockRecoverH :
    Continuous (lowerBlockRecoverH (R := R) (a := a) (d := d) (c := c)) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  exact ⟨continuous_lowerBlockDiagonal.comp continuous_subtype_val,
    (Units.continuous_coe_inv.matrix_submatrix _ _).comp continuous_subtype_val⟩

/-- All three coordinate projections on the image are jointly continuous. -/
theorem continuous_lowerBlockCoordinates :
    Continuous (lowerBlockCoordinates (R := R) (a := a) (d := d) (c := c)) :=
  continuous_lowerBlockRecoverG.prodMk
    ((continuous_lowerBlockRectangle.comp continuous_subtype_val).prodMk
      continuous_lowerBlockRecoverH)

variable [IsTopologicalRing R]

private theorem continuous_lowerBlockUnit :
    Continuous (fun p : LowerBlockParameters a d R => lowerBlockUnit p.1 p.2.1 p.2.2.val) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact (Units.continuous_val.comp continuous_fst).matrix_fromBlocks continuous_const
      (continuous_fst.comp continuous_snd)
      (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  · exact (Units.continuous_coe_inv.comp continuous_fst).matrix_fromBlocks continuous_const
      (((Units.continuous_coe_inv.comp
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))).neg.matrix_mul
        (continuous_fst.comp continuous_snd)).matrix_mul
        (Units.continuous_coe_inv.comp continuous_fst))
      (Units.continuous_coe_inv.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))

/-- The chart is continuous over every topological commutative ring. Inversion in
`R` itself is not needed: the topology on matrix units controls their inverses. -/
theorem continuous_lowerBlockLocalization (c : ℕ) :
    Continuous (fun p : LowerBlockParameters a d R =>
      lowerBlockLocalization c p.1 p.2.1 p.2.2) :=
  (rankInclusionContinuous c).continuous.comp
    ((reindexContinuous finSumFinEquiv).continuous.comp continuous_lowerBlockUnit)

end Topology
end Langlands.GeneralLinear
