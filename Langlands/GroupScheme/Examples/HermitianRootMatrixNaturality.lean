import Langlands.GroupScheme.Examples.HermitianRootMatrixFixedPoints

/-! # Coefficient changes for weighted Hermitian matrix groups -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v w

variable {A : Type u} {B : Type w} {ι : Type v}
  [CommRing A] [CommRing B] [Fintype ι] [DecidableEq ι]
  {c : RingInvolution A} {d : RingInvolution B}
  {H : DiagonalForm c ι} {K : DiagonalForm d ι}

omit [Fintype ι] in
theorem gram_map (f : A →+* B) (hH : ∀ i, f (H.weight i) = K.weight i) :
    gram K = (gram H).map f := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [gram, Matrix.fromBlocks, Matrix.diagonal_apply, apply_ite f, hH]

omit [Fintype ι] [DecidableEq ι] in
theorem conjugateTranspose_map (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (M : Matrix (Index ι) (Index ι) A) :
    conjugateTranspose d (M.map f) = (conjugateTranspose c M).map f := by
  ext i j
  exact (hf (M j i)).symm

/-- Every compatible coefficient change preserves the full form equation. -/
theorem preservesForm_map (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = K.weight i)
    {M : Matrix (Index ι) (Index ι) A} (hM : PreservesForm H M) :
    PreservesForm K (M.map f) := by
  unfold PreservesForm at *
  rw [gram_map f hH, conjugateTranspose_map f hf, ← Matrix.map_mul,
    ← Matrix.map_mul, hM]

theorem map_gramElement (f : A →+* B) (hH : ∀ i, f (H.weight i) = K.weight i)
    (w : ι → Aˣ) (hw : ∀ i, (w i : A) = H.weight i)
    (v : ι → Bˣ) (hv : ∀ i, (v i : B) = K.weight i) :
    Matrix.GeneralLinearGroup.map f (gramElement H w hw) = gramElement K v hv := by
  apply Units.ext
  exact (gram_map f hH).symm

theorem conjugateTransposeSL_map (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (g : Matrix.SpecialLinearGroup (Index ι) A) :
    conjugateTransposeSL d (Matrix.SpecialLinearGroup.map f g) =
      Matrix.SpecialLinearGroup.map f (conjugateTransposeSL c g) := by
  apply Subtype.ext
  exact conjugateTranspose_map f hf _

theorem toGL_coefficientMap (f : A →+* B)
    (g : Matrix.SpecialLinearGroup (Index ι) A) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map f g) =
      Matrix.GeneralLinearGroup.map f (Matrix.SpecialLinearGroup.toGL g) :=
  Units.ext rfl

/-- The actual inverse-adjoint twist commutes with compatible coefficient changes. -/
theorem unitaryTwist_map (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = K.weight i)
    (w : ι → Aˣ) (hw : ∀ i, (w i : A) = H.weight i)
    (v : ι → Bˣ) (hv : ∀ i, (v i : B) = K.weight i)
    (g : Matrix.SpecialLinearGroup (Index ι) A) :
    unitaryTwist K v hv (Matrix.SpecialLinearGroup.map f g) =
      Matrix.SpecialLinearGroup.map f (unitaryTwist H w hw g) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_unitaryTwist, toGL_coefficientMap, toGL_unitaryTwist,
    map_mul, map_mul, map_inv, map_gramElement f hH w hw v hv,
    ← toGL_coefficientMap, ← conjugateTransposeSL_map f hf, map_inv]

/-- Coefficient change on the actual inverse-adjoint fixed subgroups. -/
def twistFixedMap (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = K.weight i)
    (w : ι → Aˣ) (hw : ∀ i, (w i : A) = H.weight i)
    (v : ι → Bˣ) (hv : ∀ i, (v i : B) = K.weight i) :
    twistFixedSubgroup H w hw →* twistFixedSubgroup K v hv where
  toFun g := ⟨Matrix.SpecialLinearGroup.map f g.1, by
    change unitaryTwist K v hv (Matrix.SpecialLinearGroup.map f g.1) =
      Matrix.SpecialLinearGroup.map f g.1
    rw [unitaryTwist_map f hf hH w hw v hv]
    exact congrArg (Matrix.SpecialLinearGroup.map f) g.2⟩
  map_one' := Subtype.ext ((Matrix.SpecialLinearGroup.map f).map_one)
  map_mul' g h := Subtype.ext ((Matrix.SpecialLinearGroup.map f).map_mul g.1 h.1)

/-- Compatible coefficient changes on the determinant-one isometry subgroups.
This construction does not require unit middle weights. -/
def specialUnitaryMap (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = K.weight i) :
    specialUnitarySubgroup H →* specialUnitarySubgroup K where
  toFun g := ⟨Matrix.GeneralLinearGroup.map f g.1,
    preservesForm_map f hf hH g.2.1, by
      change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f g.1) = 1
      rw [Matrix.GeneralLinearGroup.map_det, g.2.2, map_one]⟩
  map_one' := Subtype.ext ((Matrix.GeneralLinearGroup.map f).map_one)
  map_mul' g h := Subtype.ext ((Matrix.GeneralLinearGroup.map f).map_mul g.1 h.1)

@[simp] theorem specialUnitaryMap_val (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = K.weight i) (g : specialUnitarySubgroup H) :
    ((specialUnitaryMap f hf hH g).1 : Matrix (Index ι) (Index ι) B) =
      (g.1 : Matrix (Index ι) (Index ι) A).map f := rfl

/-- The fixed-point comparison respects actual coefficient maps. -/
theorem fixedSpecialUnitaryEquiv_map (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = K.weight i)
    (w : ι → Aˣ) (hw : ∀ i, (w i : A) = H.weight i)
    (v : ι → Bˣ) (hv : ∀ i, (v i : B) = K.weight i)
    (g : twistFixedSubgroup H w hw) :
    fixedSpecialUnitaryEquiv K v hv (twistFixedMap f hf hH w hw v hv g) =
      specialUnitaryMap f hf hH (fixedSpecialUnitaryEquiv H w hw g) := by
  apply Subtype.ext
  exact toGL_coefficientMap f g.1

theorem involutionCompatible_symm (e : A ≃+* B)
    (he : ∀ a, e (c.bar a) = d.bar (e a)) :
    ∀ b, e.symm (d.bar b) = c.bar (e.symm b) := by
  intro b
  apply e.injective
  simp only [he, RingEquiv.apply_symm_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem weightCompatible_symm (e : A ≃+* B)
    (hH : ∀ i, e (H.weight i) = K.weight i) :
    ∀ i, e.symm (K.weight i) = H.weight i := by
  intro i
  apply e.injective
  simp only [RingEquiv.apply_symm_apply, hH]

/-- Compatible coefficient equivalences identify the actual fixed SL subgroups. -/
def twistFixedRingEquiv (e : A ≃+* B)
    (he : ∀ a, e (c.bar a) = d.bar (e a))
    (hH : ∀ i, e (H.weight i) = K.weight i)
    (w : ι → Aˣ) (hw : ∀ i, (w i : A) = H.weight i)
    (v : ι → Bˣ) (hv : ∀ i, (v i : B) = K.weight i) :
    twistFixedSubgroup H w hw ≃* twistFixedSubgroup K v hv where
  toFun := twistFixedMap e.toRingHom he hH w hw v hv
  invFun := twistFixedMap e.symm.toRingHom (involutionCompatible_symm e he)
    (weightCompatible_symm e hH) v hv w hw
  left_inv g := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact e.symm_apply_apply (g.1 i j)
  right_inv g := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact e.apply_symm_apply (g.1 i j)
  map_mul' := (twistFixedMap e.toRingHom he hH w hw v hv).map_mul

/-- Coefficient equivalence on the determinant-one isometry subgroups. -/
def specialUnitaryRingEquiv (e : A ≃+* B)
    (he : ∀ a, e (c.bar a) = d.bar (e a))
    (hH : ∀ i, e (H.weight i) = K.weight i) :
    specialUnitarySubgroup H ≃* specialUnitarySubgroup K where
  toFun := specialUnitaryMap e.toRingHom he hH
  invFun := specialUnitaryMap e.symm.toRingHom (involutionCompatible_symm e he)
    (weightCompatible_symm e hH)
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact e.symm_apply_apply (g.1 i j)
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact e.apply_symm_apply (g.1 i j)
  map_mul' := (specialUnitaryMap e.toRingHom he hH).map_mul

@[simp] theorem specialUnitaryRingEquiv_val (e : A ≃+* B)
    (he : ∀ a, e (c.bar a) = d.bar (e a))
    (hH : ∀ i, e (H.weight i) = K.weight i) (g : specialUnitarySubgroup H) :
    ((specialUnitaryRingEquiv e he hH g).1 : Matrix (Index ι) (Index ι) B) =
      (g.1 : Matrix (Index ι) (Index ι) A).map e := rfl

end Langlands.GroupScheme.HermitianRoot
