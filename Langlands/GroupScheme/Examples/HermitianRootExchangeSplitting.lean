import Langlands.GroupScheme.Examples.HermitianRootMatrixNaturality

/-! # Splitting weighted special unitary groups over an exchange ring -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v

variable {A : Type u} {Middle : Type v}
  [CommRing A] [Fintype Middle] [DecidableEq Middle]
  {c : RingInvolution A}

/-- Conjugate transpose on invertible matrices, as an order-reversing operation. -/
def conjugateTransposeGL (c : RingInvolution A)
    (g : Matrix.GeneralLinearGroup (Index Middle) A) :
    Matrix.GeneralLinearGroup (Index Middle) A where
  val := conjugateTranspose c (g : Matrix (Index Middle) (Index Middle) A)
  inv := conjugateTranspose c (g⁻¹ : Matrix.GeneralLinearGroup (Index Middle) A)
  val_inv := by
    rw [← conjugateTranspose_mul, ← Units.val_mul, inv_mul_cancel]
    exact conjugateTranspose_one
  inv_val := by
    rw [← conjugateTranspose_mul, ← Units.val_mul, mul_inv_cancel]
    exact conjugateTranspose_one

@[simp] theorem conjugateTransposeGL_mul
    (g h : Matrix.GeneralLinearGroup (Index Middle) A) :
    conjugateTransposeGL c (g * h) =
      conjugateTransposeGL c h * conjugateTransposeGL c g :=
  Units.ext (conjugateTranspose_mul _ _)

@[simp] theorem conjugateTransposeGL_inv
    (g : Matrix.GeneralLinearGroup (Index Middle) A) :
    conjugateTransposeGL c g⁻¹ = (conjugateTransposeGL c g)⁻¹ := Units.ext rfl

@[simp] theorem conjugateTransposeGL_apply_apply
    (g : Matrix.GeneralLinearGroup (Index Middle) A) :
    conjugateTransposeGL c (conjugateTransposeGL c g) = g := by
  apply Units.ext
  ext i j
  exact c.bar_bar _

@[simp] theorem conjugateTransposeGL_toGL
    (g : Matrix.SpecialLinearGroup (Index Middle) A) :
    conjugateTransposeGL c (Matrix.SpecialLinearGroup.toGL g) =
      Matrix.SpecialLinearGroup.toGL (conjugateTransposeSL c g) := Units.ext rfl

@[simp] theorem conjugateTransposeGL_gramElement
    (H : DiagonalForm c Middle) (w : Middle → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) :
    conjugateTransposeGL c (gramElement H w hw) = gramElement H w hw := by
  apply Units.ext
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [conjugateTransposeGL, conjugateTranspose, gram, Matrix.fromBlocks,
      Matrix.diagonal_apply, eq_comm]
  split_ifs with hij
  · subst j; simp [H.bar_weight]
  · simp

/-- The weighted inverse adjoint squares to the identity for the original Hermitian form. -/
theorem unitaryTwist_involutive (H : DiagonalForm c Middle) (w : Middle → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) :
    Function.Involutive (unitaryTwist H w hw) := by
  intro g
  apply Matrix.SpecialLinearGroup.toGL_injective
  have ht (x : Matrix.SpecialLinearGroup (Index Middle) A) :
      Matrix.SpecialLinearGroup.toGL (unitaryTwist H w hw x) =
        (gramElement H w hw)⁻¹ *
          (conjugateTransposeGL c (Matrix.SpecialLinearGroup.toGL x))⁻¹ *
            gramElement H w hw := by
    rw [toGL_unitaryTwist, conjugateTransposeSL_inv, map_inv,
      conjugateTransposeGL_toGL]
  rw [ht, ht]
  simp only [conjugateTransposeGL_mul, conjugateTransposeGL_inv,
    conjugateTransposeGL_gramElement, conjugateTransposeGL_apply_apply, mul_inv_rev,
    inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

namespace Exchange

variable (A)

/-- Trivial scalar conjugation. -/
def trivialInvolution : RingInvolution A :=
  ⟨RingEquiv.refl A, fun _ => rfl⟩

/-- Scalar conjugation on the split quadratic algebra exchanges its factors. -/
def involution : RingInvolution (A × A) :=
  ⟨RingEquiv.prodComm, fun _ => rfl⟩

variable {A}

/-- A diagonal form with trivial conjugation. -/
def baseForm (h : Middle → A) : DiagonalForm (trivialInvolution A) Middle :=
  ⟨h, fun _ => rfl⟩

/-- A diagonal form with the same middle weights in both exchanged factors. -/
def form (h : Middle → A) : DiagonalForm (involution A) Middle :=
  ⟨fun i => (h i, h i), fun _ => rfl⟩

/-- Paired units witness nondegeneracy of the split form. -/
def units (w : Middle → Aˣ) : Middle → (A × A)ˣ :=
  fun i => MulEquiv.prodUnits.symm (w i, w i)

omit [Fintype Middle] [DecidableEq Middle] in
theorem units_val {h : Middle → A} {w : Middle → Aˣ}
    (hw : ∀ i, (w i : A) = h i) (i : Middle) :
    (units w i : A × A) = (form h).weight i := by
  change ((w i : A), (w i : A)) = (h i, h i)
  exact Prod.ext (hw i) (hw i)

/-- Special-linear matrices over a product ring are pairs of special-linear matrices. -/
def specialLinearProdEquiv :
    Matrix.SpecialLinearGroup (Index Middle) (A × A) ≃*
      Matrix.SpecialLinearGroup (Index Middle) A ×
        Matrix.SpecialLinearGroup (Index Middle) A where
  toFun g := (Matrix.SpecialLinearGroup.map (RingHom.fst A A) g,
    Matrix.SpecialLinearGroup.map (RingHom.snd A A) g)
  invFun g := ⟨fun (i j : Index Middle) => (g.1.val i j, g.2.val i j), by
    apply Prod.ext
    · change RingHom.fst A A (Matrix.det _) = 1
      exact (RingHom.map_det (RingHom.fst A A) _).trans g.1.2
    · change RingHom.snd A A (Matrix.det _) = 1
      exact (RingHom.map_det (RingHom.snd A A) _).trans g.2.2⟩
  left_inv g := by apply Subtype.ext; rfl
  right_inv g := by apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_mul' g h := by
    apply Prod.ext
    · exact (Matrix.SpecialLinearGroup.map (RingHom.fst A A)).map_mul g h
    · exact (Matrix.SpecialLinearGroup.map (RingHom.snd A A)).map_mul g h

theorem fst_conjugateTransposeSL
    (g : Matrix.SpecialLinearGroup (Index Middle) (A × A)) :
    Matrix.SpecialLinearGroup.map (RingHom.fst A A)
        (conjugateTransposeSL (involution A) g) =
      conjugateTransposeSL (trivialInvolution A)
        (Matrix.SpecialLinearGroup.map (RingHom.snd A A) g) := by
  apply Subtype.ext
  rfl

theorem snd_conjugateTransposeSL
    (g : Matrix.SpecialLinearGroup (Index Middle) (A × A)) :
    Matrix.SpecialLinearGroup.map (RingHom.snd A A)
        (conjugateTransposeSL (involution A) g) =
      conjugateTransposeSL (trivialInvolution A)
        (Matrix.SpecialLinearGroup.map (RingHom.fst A A) g) := by
  apply Subtype.ext
  rfl

theorem fst_unitaryTwist (h : Middle → A) (w : Middle → Aˣ)
    (hw : ∀ i, (w i : A) = h i)
    (g : Matrix.SpecialLinearGroup (Index Middle) (A × A)) :
    Matrix.SpecialLinearGroup.map (RingHom.fst A A)
        (unitaryTwist (form h) (units w) (units_val hw) g) =
      unitaryTwist (baseForm h) w hw
        (Matrix.SpecialLinearGroup.map (RingHom.snd A A) g) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_coefficientMap, toGL_unitaryTwist, map_mul, map_mul, map_inv,
    map_gramElement (H := form h) (K := baseForm h)
      (RingHom.fst A A) (fun _ => rfl) (units w) (units_val hw) w hw,
    ← toGL_coefficientMap, fst_conjugateTransposeSL, map_inv]
  exact (toGL_unitaryTwist (baseForm h) w hw _).symm

theorem snd_unitaryTwist (h : Middle → A) (w : Middle → Aˣ)
    (hw : ∀ i, (w i : A) = h i)
    (g : Matrix.SpecialLinearGroup (Index Middle) (A × A)) :
    Matrix.SpecialLinearGroup.map (RingHom.snd A A)
        (unitaryTwist (form h) (units w) (units_val hw) g) =
      unitaryTwist (baseForm h) w hw
        (Matrix.SpecialLinearGroup.map (RingHom.fst A A) g) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_coefficientMap, toGL_unitaryTwist, map_mul, map_mul, map_inv,
    map_gramElement (H := form h) (K := baseForm h)
      (RingHom.snd A A) (fun _ => rfl) (units w) (units_val hw) w hw,
    ← toGL_coefficientMap, snd_conjugateTransposeSL, map_inv]
  exact (toGL_unitaryTwist (baseForm h) w hw _).symm

/-- A fixed pair is determined by its first special-linear matrix. -/
def fixedEquiv (h : Middle → A) (w : Middle → Aˣ)
    (hw : ∀ i, (w i : A) = h i) :
    twistFixedSubgroup (form h) (units w) (units_val hw) ≃*
      Matrix.SpecialLinearGroup (Index Middle) A where
  toFun g := Matrix.SpecialLinearGroup.map (RingHom.fst A A) g.1
  invFun g := ⟨specialLinearProdEquiv.symm
    (g, unitaryTwist (baseForm h) w hw g), by
      apply specialLinearProdEquiv.injective
      apply Prod.ext
      · change Matrix.SpecialLinearGroup.map (RingHom.fst A A)
          (unitaryTwist (form h) (units w) (units_val hw) _) = _
        rw [fst_unitaryTwist]
        exact unitaryTwist_involutive (baseForm h) w hw g
      · change Matrix.SpecialLinearGroup.map (RingHom.snd A A)
          (unitaryTwist (form h) (units w) (units_val hw) _) = _
        rw [snd_unitaryTwist]
        rfl⟩
  left_inv g := by
    apply Subtype.ext
    apply specialLinearProdEquiv.injective
    apply Prod.ext
    · rfl
    · change unitaryTwist (baseForm h) w hw
        (Matrix.SpecialLinearGroup.map (RingHom.fst A A) g.1) =
          Matrix.SpecialLinearGroup.map (RingHom.snd A A) g.1
      rw [← snd_unitaryTwist]
      exact congrArg (Matrix.SpecialLinearGroup.map (RingHom.snd A A)) g.2
  right_inv g := rfl
  map_mul' g g' := (Matrix.SpecialLinearGroup.map (RingHom.fst A A)).map_mul g.1 g'.1

/-- The determinant-one isometries over the exchange ring are the full special-linear group. -/
def specialUnitaryEquiv (h : Middle → A) (w : Middle → Aˣ)
    (hw : ∀ i, (w i : A) = h i) :
    specialUnitarySubgroup (form h) ≃* Matrix.SpecialLinearGroup (Index Middle) A :=
  (fixedSpecialUnitaryEquiv (form h) (units w) (units_val hw)).symm.trans
    (fixedEquiv h w hw)

/-- The splitting is the first coefficient projection on the original isometry matrix. -/
theorem specialUnitaryEquiv_val (h : Middle → A) (w : Middle → Aˣ)
    (hw : ∀ i, (w i : A) = h i) (g : specialUnitarySubgroup (form h)) :
    (specialUnitaryEquiv h w hw g : Matrix (Index Middle) (Index Middle) A) =
      (g.1 : Matrix (Index Middle) (Index Middle) (A × A)).map (RingHom.fst A A) := rfl

/-- The inverse splitting pairs a matrix with its weighted inverse transpose. -/
theorem specialUnitaryEquiv_symm_val (h : Middle → A) (w : Middle → Aˣ)
    (hw : ∀ i, (w i : A) = h i) (g : Matrix.SpecialLinearGroup (Index Middle) A)
    (i j : Index Middle) :
    (((specialUnitaryEquiv h w hw).symm g).1 :
        Matrix (Index Middle) (Index Middle) (A × A)) i j =
      (g i j, unitaryTwist (baseForm h) w hw g i j) := rfl

end Exchange

end Langlands.GroupScheme.HermitianRoot
