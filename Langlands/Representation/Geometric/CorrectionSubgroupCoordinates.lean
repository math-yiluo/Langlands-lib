import Langlands.Group.GL.BlockUnipotentCoordinates
import Langlands.Representation.Geometric.StandardIntersectionsProof

/-! Actual allowed matrix-entry coordinates on the full correction subgroup. -/

open scoped BigOperators

namespace Langlands.Geometric

open GeneralLinear

universe u
variable {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- The strict source-block and weak permuted target-block zero pattern. -/
def CorrectionAllowed (a b : Fin n) : Prop :=
  blockIndex B a < blockIndex B b ∧ blockIndex C (w a) ≤ blockIndex C (w b)

instance (a b : Fin n) : Decidable (CorrectionAllowed B C w a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The finite set of allowed actual matrix positions. -/
abbrev CorrectionEntry := {ab : Fin n × Fin n // CorrectionAllowed B C w ab.1 ab.2}

/-- The actual full intersection `U ∩ g⁻¹ Q g`, with `g` the permutation matrix. -/
abbrev correctionSubgroup (R : Type u) [CommRing R] : Subgroup (GeneralLinear n R) :=
  intersectionSource (B.unipotentSubgroup R) (C.parabolic R) (permutation n R w)

variable (R : Type u) [CommRing R]

/-- Extend allowed coordinates by zero to a matrix. -/
def correctionExtension (X : CorrectionEntry B C w → R) : Matrix (Fin n) (Fin n) R :=
  fun a b => if h : CorrectionAllowed B C w a b then X ⟨(a, b), h⟩ else 0

@[simp] theorem correctionExtension_allowed (X : CorrectionEntry B C w → R)
    (ab : CorrectionEntry B C w) :
    correctionExtension B C w R X ab.1.1 ab.1.2 = X ab := by
  simp [correctionExtension, ab.2]

theorem correctionExtension_eq_zero (X : CorrectionEntry B C w → R) (a b : Fin n)
    (h : ¬ CorrectionAllowed B C w a b) :
    correctionExtension B C w R X a b = 0 := dite_eq_right h

/-- The allowed entries, written in the published rectangular block coordinates. -/
def correctionBlocks (X : CorrectionEntry B C w → R) : B.RadicalCoordinates R :=
  fun ij a b => correctionExtension B C w R X (B.index ij.1.1 a) (B.index ij.1.2 b)

/-- The actual invertible matrix, using the published determinant-one construction. -/
def correctionMatrix (X : CorrectionEntry B C w → R) : GeneralLinear n R :=
  B.radicalMatrix R (correctionBlocks B C w R X)

/-- Its underlying matrix is exactly identity plus the zero extension. -/
theorem correctionMatrix_val (X : CorrectionEntry B C w → R) :
    (correctionMatrix B C w R X).val = 1 + correctionExtension B C w R X := by
  ext a b
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective a
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective b
  change B.radicalMatrix R _ (B.index i a) (B.index j b) =
    (1 + correctionExtension B C w R X) (B.index i a) (B.index j b)
  rw [Matrix.add_apply, Matrix.one_apply]
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [B.radicalMatrix_apply_upper R _ hij]
    rw [ite_eq_right (index_ne_of_block_ne B hij.ne a b), zero_add]
    rfl
  · rw [B.radicalMatrix_apply_same]
    have hz : ¬ CorrectionAllowed B C w (B.index i a) (B.index i b) := by
      simp [CorrectionAllowed]
    rw [correctionExtension_eq_zero B C w R X _ _ hz, add_zero]
    simp only [(B.index i).injective.eq_iff]
  · rw [B.radicalMatrix_apply_lower R _ hji]
    have hz : ¬ CorrectionAllowed B C w (B.index i a) (B.index j b) := by
      simp [CorrectionAllowed, not_lt.mpr hji.le]
    rw [correctionExtension_eq_zero B C w R X _ _ hz,
      ite_eq_right (index_ne_of_block_ne B hji.ne' a b), add_zero]

private theorem conjugate_entry (g : GeneralLinear n R) (a b : Fin n) :
    (MulAut.conj (permutation n R w) g) (w a) (w b) = g a b := by
  change (permutation n R w * g * (permutation n R w)⁻¹) (w a) (w b) = _
  rw [permutation_conjugate_entry]
  change g (w.symm (w a)) (w.symm (w b)) = _
  simp only [Equiv.symm_apply_apply]

/-- The constructed matrix belongs to the full correction subgroup. -/
theorem correctionMatrix_mem (X : CorrectionEntry B C w → R) :
    correctionMatrix B C w R X ∈ correctionSubgroup B C w R := by
  constructor
  · exact (B.mem_unipotentSubgroup_iff R _).mpr
      ⟨B.radicalMatrix_mem_parabolic R _, fun i a b => B.radicalMatrix_apply_same R _ i a b⟩
  · apply (mem_parabolic_iff_blockIndex R C _).mpr
    intro a b hba
    obtain ⟨a, rfl⟩ := w.surjective a
    obtain ⟨b, rfl⟩ := w.surjective b
    change (MulAut.conj (permutation n R w) (correctionMatrix B C w R X)) (w a) (w b) = 0
    rw [conjugate_entry]
    rw [correctionMatrix_val, Matrix.add_apply, Matrix.one_apply]
    have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ hba
    have hz : ¬ CorrectionAllowed B C w a b := fun h => not_lt_of_ge h.2 hba
    rw [ite_eq_right hab, correctionExtension_eq_zero B C w R X a b hz, add_zero]

/-- Outside the allowed positions, an intersection element has identity entries. -/
theorem correctionSubgroup_entry_not_allowed (h : correctionSubgroup B C w R)
    (a b : Fin n) (hab : ¬ CorrectionAllowed B C w a b) :
    h.val a b = if a = b then 1 else 0 := by
  have hu := (mem_unipotent_iff_blockIndex R B h.val).mp h.property.1
  rcases lt_trichotomy (blockIndex B a) (blockIndex B b) with hlt | heq | hgt
  · have hc : blockIndex C (w b) < blockIndex C (w a) :=
      lt_of_not_ge (fun hle => hab ⟨hlt, hle⟩)
    have hp := (mem_parabolic_iff_blockIndex R C _).mp h.property.2 (w a) (w b) hc
    change (MulAut.conj (permutation n R w) h.val) (w a) (w b) = 0 at hp
    rw [conjugate_entry] at hp
    rw [hp, ite_eq_right (fun he => hlt.ne (congrArg (blockIndex B) he))]
  · exact hu.2 a b heq
  · rw [(mem_parabolic_iff_blockIndex R B _).mp hu.1 a b hgt,
      ite_eq_right (fun he => hgt.ne' (congrArg (blockIndex B) he))]

/-- Actual matrix-entry coordinates, with inverse the actual matrix `1 + X`. -/
def correctionCoordinates : correctionSubgroup B C w R ≃ (CorrectionEntry B C w → R) where
  toFun h ab := h.val ab.1.1 ab.1.2
  invFun X := ⟨correctionMatrix B C w R X, correctionMatrix_mem B C w R X⟩
  left_inv h := by
    apply Subtype.ext
    apply Units.ext
    ext a b
    change (correctionMatrix B C w R _).val a b = h.val a b
    rw [correctionMatrix_val, Matrix.add_apply, Matrix.one_apply]
    by_cases hab : CorrectionAllowed B C w a b
    · rw [correctionExtension, dite_eq_left hab,
        ite_eq_right (fun he => hab.1.ne (congrArg (blockIndex B) he)), zero_add]
    · rw [correctionExtension_eq_zero B C w R _ a b hab, add_zero,
        correctionSubgroup_entry_not_allowed B C w R h a b hab]
  right_inv X := by
    funext ab
    change (correctionMatrix B C w R X).val ab.1.1 ab.1.2 = X ab
    rw [correctionMatrix_val, Matrix.add_apply, Matrix.one_apply,
      ite_eq_right (fun he => ab.2.1.ne (congrArg (blockIndex B) he)),
      correctionExtension_allowed, zero_add]

@[simp] theorem correctionCoordinates_apply (h : correctionSubgroup B C w R)
    (ab : CorrectionEntry B C w) :
    correctionCoordinates B C w R h ab = h.val ab.1.1 ab.1.2 := rfl

@[simp] theorem correctionCoordinates_symm_val (X : CorrectionEntry B C w → R) :
    ((correctionCoordinates B C w R).symm X).val = correctionMatrix B C w R X := rfl

/-- Inverse entry formula at every matrix position. -/
theorem correctionCoordinates_symm_entry (X : CorrectionEntry B C w → R) (a b : Fin n) :
    ((correctionCoordinates B C w R).symm X).val a b =
      (if a = b then 1 else 0) + correctionExtension B C w R X a b := by
  change (correctionMatrix B C w R X).val a b = _
  rw [correctionMatrix_val, Matrix.add_apply, Matrix.one_apply]

/-- Reconstruction of every element as identity plus its extended coordinates. -/
theorem correctionCoordinates_reconstruct (h : correctionSubgroup B C w R) :
    h.val.val = 1 + correctionExtension B C w R (correctionCoordinates B C w R h) := by
  have he := correctionMatrix_val B C w R (correctionCoordinates B C w R h)
  have hh := congrArg (fun z : correctionSubgroup B C w R => z.val.val)
    ((correctionCoordinates B C w R).symm_apply_apply h)
  exact hh.symm.trans he

/-- The identity has zero coordinates. -/
@[simp] theorem correctionCoordinates_one : correctionCoordinates B C w R 1 = 0 := by
  funext ab
  exact Matrix.one_apply_ne (fun he => ab.2.1.ne (congrArg (blockIndex B) he))

/-- Zero coordinates reconstruct the identity. -/
@[simp] theorem correctionCoordinates_symm_zero :
    (correctionCoordinates B C w R).symm 0 = 1 := by
  rw [Equiv.symm_apply_eq, correctionCoordinates_one]

/-- Multiplication in entry coordinates, using zero extension outside allowed pairs. -/
theorem correctionCoordinates_mul (u v : correctionSubgroup B C w R)
    (ab : CorrectionEntry B C w) :
    correctionCoordinates B C w R (u * v) ab =
      correctionCoordinates B C w R u ab + correctionCoordinates B C w R v ab +
        ∑ k : Fin n,
          correctionExtension B C w R (correctionCoordinates B C w R u) ab.1.1 k *
          correctionExtension B C w R (correctionCoordinates B C w R v) k ab.1.2 := by
  have huv : (u * v).val.val =
      (1 + correctionExtension B C w R (correctionCoordinates B C w R u)) *
      (1 + correctionExtension B C w R (correctionCoordinates B C w R v)) := by
    change u.val.val * v.val.val = _
    rw [correctionCoordinates_reconstruct B C w R u,
      correctionCoordinates_reconstruct B C w R v]
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) R => M ab.1.1 ab.1.2) huv
  rw [mul_add, add_mul, add_mul, one_mul, one_mul, mul_one] at he
  simpa only [Matrix.add_apply, Matrix.one_apply,
    ite_eq_right (fun h => ab.2.1.ne (congrArg (blockIndex B) h)),
    correctionExtension_allowed, Matrix.mul_apply, zero_add, add_assoc,
    correctionCoordinates_apply] using he

/-- Intermediate indices at which both factors in the cross term are allowed. -/
abbrev CorrectionIntermediate (ab : CorrectionEntry B C w) :=
  {k : Fin n // CorrectionAllowed B C w ab.1.1 k ∧ CorrectionAllowed B C w k ab.1.2}

/-- The positive source-block gap of an allowed entry. -/
def correctionGap (ab : CorrectionEntry B C w) : ℕ :=
  (blockIndex B ab.1.2).val - (blockIndex B ab.1.1).val

/-- Both cross-term positions have strictly smaller source-block gap. -/
theorem correctionIntermediate_gap (ab : CorrectionEntry B C w)
    (k : CorrectionIntermediate B C w ab) :
    correctionGap B C w ⟨(ab.1.1, k.val), k.2.1⟩ < correctionGap B C w ab ∧
      correctionGap B C w ⟨(k.val, ab.1.2), k.2.2⟩ < correctionGap B C w ab := by
  have ha : (blockIndex B ab.1.1).val < (blockIndex B k.val).val := k.2.1.1
  have hb : (blockIndex B k.val).val < (blockIndex B ab.1.2).val := k.2.2.1
  dsimp [correctionGap]
  omega

/-- A nonzero cross term can occur only at two allowed positions. -/
theorem correctionExtension_mul_ne_zero (X Y : CorrectionEntry B C w → R)
    (a k b : Fin n)
    (h : correctionExtension B C w R X a k * correctionExtension B C w R Y k b ≠ 0) :
    CorrectionAllowed B C w a k ∧ CorrectionAllowed B C w k b := by
  constructor
  · by_contra hk
    exact h (by rw [correctionExtension_eq_zero B C w R X a k hk, zero_mul])
  · by_contra hk
    exact h (by rw [correctionExtension_eq_zero B C w R Y k b hk, mul_zero])

/-- Every nonzero cross term has strictly smaller source-block gaps on both sides. -/
theorem correctionExtension_mul_gap (X Y : CorrectionEntry B C w → R)
    (ab : CorrectionEntry B C w) (k : Fin n)
    (h : correctionExtension B C w R X ab.1.1 k *
      correctionExtension B C w R Y k ab.1.2 ≠ 0) :
    (blockIndex B k).val - (blockIndex B ab.1.1).val < correctionGap B C w ab ∧
      (blockIndex B ab.1.2).val - (blockIndex B k).val < correctionGap B C w ab :=
  correctionIntermediate_gap B C w ab
    ⟨k, correctionExtension_mul_ne_zero B C w R X Y ab.1.1 k ab.1.2 h⟩

/-- The multiplication formula with the sum restricted to the allowed pairs. -/
theorem correctionCoordinates_mul_allowed (u v : correctionSubgroup B C w R)
    (ab : CorrectionEntry B C w) :
    correctionCoordinates B C w R (u * v) ab =
      correctionCoordinates B C w R u ab + correctionCoordinates B C w R v ab +
        ∑ k : CorrectionIntermediate B C w ab,
          correctionCoordinates B C w R u ⟨(ab.1.1, k.val), k.2.1⟩ *
          correctionCoordinates B C w R v ⟨(k.val, ab.1.2), k.2.2⟩ := by
  rw [correctionCoordinates_mul]
  congr 1
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun k => CorrectionAllowed B C w ab.1.1 k ∧ CorrectionAllowed B C w k ab.1.2)]
  have hz : ∑ k : {k : Fin n //
      ¬ (CorrectionAllowed B C w ab.1.1 k ∧ CorrectionAllowed B C w k ab.1.2)},
      correctionExtension B C w R (correctionCoordinates B C w R u) ab.1.1 k.val *
      correctionExtension B C w R (correctionCoordinates B C w R v) k.val ab.1.2 = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_contra hk
    exact k.2 (correctionExtension_mul_ne_zero B C w R _ _ _ _ _ hk)
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  simp only [correctionExtension, dite_eq_left k.2.1, dite_eq_left k.2.2,
    correctionCoordinates_apply]

/-- The transported multiplication formula directly on coordinate functions. -/
theorem correctionCoordinates_symm_mul_symm (X Y : CorrectionEntry B C w → R)
    (ab : CorrectionEntry B C w) :
    correctionCoordinates B C w R
      ((correctionCoordinates B C w R).symm X * (correctionCoordinates B C w R).symm Y) ab =
      X ab + Y ab + ∑ k : CorrectionIntermediate B C w ab,
        X ⟨(ab.1.1, k.val), k.2.1⟩ * Y ⟨(k.val, ab.1.2), k.2.2⟩ := by
  simpa only [Equiv.apply_symm_apply] using correctionCoordinates_mul_allowed B C w R
    ((correctionCoordinates B C w R).symm X) ((correctionCoordinates B C w R).symm Y) ab

section Topology

variable [TopologicalSpace R]

/-- Reading actual entries is continuous for the inherited subgroup topology. -/
theorem continuous_correctionCoordinates : Continuous (correctionCoordinates B C w R) := by
  apply continuous_pi
  intro ab
  exact (GeneralLinear.entry ab.1.1 ab.1.2).continuous.comp continuous_subtype_val

/-- Zero extension is continuous with the product matrix topology. -/
theorem continuous_correctionExtension : Continuous (correctionExtension B C w R) := by
  apply continuous_matrix
  intro a b
  by_cases hab : CorrectionAllowed B C w a b
  · simp only [correctionExtension, dite_eq_left hab]
    exact continuous_apply _
  · simp only [correctionExtension, dite_eq_right hab]
    exact continuous_const

/-- Conversion to rectangular radical coordinates is continuous. -/
theorem continuous_correctionBlocks : Continuous (correctionBlocks B C w R) := by
  apply continuous_pi
  intro ij
  apply continuous_matrix
  intro a b
  exact (continuous_correctionExtension B C w R).matrix_elem _ _

variable [IsTopologicalRing R]

/-- The actual invertible matrix is continuous, including its adjugate inverse. -/
theorem continuous_correctionMatrix : Continuous (correctionMatrix B C w R) := by
  change Continuous (fun X => ((B.radicalCoordinates R).symm
    (correctionBlocks B C w R X)).val.val)
  exact continuous_subtype_val.comp (continuous_subtype_val.comp
    ((B.continuous_radicalCoordinates_symm R).comp (continuous_correctionBlocks B C w R)))

/-- Reconstruction is continuous into the actual intersection subgroup. -/
theorem continuous_correctionCoordinates_symm :
    Continuous (correctionCoordinates B C w R).symm :=
  (continuous_correctionMatrix B C w R).subtype_mk _

/-- Allowed-entry coordinates as a homeomorphism with the inherited topology. -/
def correctionCoordinatesHomeomorph :
    correctionSubgroup B C w R ≃ₜ (CorrectionEntry B C w → R) where
  toEquiv := correctionCoordinates B C w R
  continuous_toFun := continuous_correctionCoordinates B C w R
  continuous_invFun := continuous_correctionCoordinates_symm B C w R

@[simp] theorem correctionCoordinatesHomeomorph_apply (h : correctionSubgroup B C w R) :
    correctionCoordinatesHomeomorph B C w R h = correctionCoordinates B C w R h := rfl

@[simp] theorem correctionCoordinatesHomeomorph_symm_apply (X : CorrectionEntry B C w → R) :
    (correctionCoordinatesHomeomorph B C w R).symm X =
      (correctionCoordinates B C w R).symm X := rfl

end Topology

end Langlands.Geometric
