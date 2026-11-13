import Langlands.GroupScheme.Examples.HermitianMatrixBasic
import Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitting
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic

/-!
# Splitting the determinant-one isometries of a Hermitian matrix

Let `A` be a commutative ring with involution `c`, and let `p, q : A → R` be ring maps
with `q = p ∘ c̄` whose product `A → R × R` is bijective. For every nonsingular Hermitian
form `H` over `A`, the map `g ↦ p(g)` is a group isomorphism from the determinant-one
isometries of `H` onto `SL(R)`, and `p(H)⁻¹ (q(g)⁻¹)ᵀ p(H) = p(g)`.

For a separable quadratic extension `L/K` and a `K`-algebra map `φ : L → R`, the maps
`ℓ ⊗ r ↦ φ(ℓ) r` and `ℓ ⊗ r ↦ φ(c ℓ) r` on `L ⊗_K R` satisfy these hypotheses for the
conjugation `c ⊗ 1`.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.HermitianMatrix

open SU3Root

section Abstract

variable {A R : Type*} [CommRing A] [CommRing R] {Ix : Type*} [Fintype Ix] [DecidableEq Ix]
  {c : RingInvolution A}

/-- The determinant of a determinant-one isometry. -/
theorem specialUnitary_det {H : Form c Ix} (x : specialUnitarySubgroup H) :
    (x.1 : Matrix Ix Ix A).det = 1 := by
  have h := (Subgroup.mem_inf.mp x.2).2
  rw [MonoidHom.mem_ker] at h
  rw [← Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_one]

/-- A determinant-one isometry preserves the form. -/
theorem specialUnitary_preserves {H : Form c Ix} (x : specialUnitarySubgroup H) :
    Preserves H (x.1 : Matrix Ix Ix A) :=
  (Subgroup.mem_inf.mp x.2).1

omit [Fintype Ix] [DecidableEq Ix] in
/-- With `q = p ∘ c̄`, the image of an adjoint along `p` is the transpose of the image
along `q`. -/
theorem adjoint_map_left (p q : A →+* R) (hpq : ∀ a, q a = p (c.bar a))
    (x : Matrix Ix Ix A) : (adjoint c x).map p = (x.map q)ᵀ := by
  ext i j
  simp [adjoint, hpq]

omit [Fintype Ix] [DecidableEq Ix] in
/-- With `q = p ∘ c̄`, the image of an adjoint along `q` is the transpose of the image
along `p`. -/
theorem adjoint_map_right (p q : A →+* R) (hpq : ∀ a, q a = p (c.bar a))
    (x : Matrix Ix Ix A) : (adjoint c x).map q = (x.map p)ᵀ := by
  ext i j
  simp [adjoint, hpq]

/-- The image of a Hermitian Gram matrix along `q = p ∘ c̄` is the transpose of its image
along `p`. -/
theorem gram_map_right (H : Form c Ix) (p q : A →+* R) (hpq : ∀ a, q a = p (c.bar a)) :
    (H.gram : Matrix Ix Ix A).map q = ((H.gram : Matrix Ix Ix A).map p)ᵀ := by
  have h := adjoint_map_left p q hpq (H.gram : Matrix Ix Ix A)
  rw [H.hermitian] at h
  rw [h, Matrix.transpose_transpose]

/-- The images of the Gram matrix and of its inverse along `p` are mutually inverse. -/
theorem gram_inv_map_mul (H : Form c Ix) (p : A →+* R) :
    ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A).map p *
        (H.gram : Matrix Ix Ix A).map p = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _
    (map_zero p) (map_one p)]

/-- The images of the Gram matrix and of its inverse along `p` are mutually inverse. -/
theorem gram_map_mul_inv (H : Form c Ix) (p : A →+* R) :
    (H.gram : Matrix Ix Ix A).map p *
        ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A).map p = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _
    (map_zero p) (map_one p)]

/-- Mapping a determinant-one isometry entrywise along a ring map. -/
def splitSL (H : Form c Ix) (p : A →+* R) :
    specialUnitarySubgroup H →* Matrix.SpecialLinearGroup Ix R where
  toFun x := ⟨p.mapMatrix (x.1 : Matrix Ix Ix A), by
    rw [← RingHom.map_det, specialUnitary_det, map_one]⟩
  map_one' := Subtype.ext (map_one p.mapMatrix)
  map_mul' x y := Subtype.ext (map_mul p.mapMatrix (x.1 : Matrix Ix Ix A) y.1)

@[simp] theorem coe_splitSL (H : Form c Ix) (p : A →+* R) (x : specialUnitarySubgroup H) :
    ((splitSL H p x : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R) =
      (x.1 : Matrix Ix Ix A).map p := rfl

/-- The inverse transpose of an isometry in the conjugate coordinate: for
`q = p ∘ c̄` and a determinant-one isometry `x`,
`p(H)⁻¹ (q(x)⁻¹)ᵀ p(H) = p(x)`. -/
theorem splitSL_conj (H : Form c Ix) (p q : A →+* R) (hpq : ∀ a, q a = p (c.bar a))
    (x : specialUnitarySubgroup H) :
    ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A).map p *
        (((splitSL H q x)⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R)ᵀ *
          (H.gram : Matrix Ix Ix A).map p =
      ((splitSL H p x : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R) := by
  have hpres : ((splitSL H q x : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R)ᵀ *
      (H.gram : Matrix Ix Ix A).map p *
        ((splitSL H p x : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R) =
      (H.gram : Matrix Ix Ix A).map p := by
    have h := congrArg (fun m : Matrix Ix Ix A => m.map p) (specialUnitary_preserves x)
    simp only [Matrix.map_mul] at h
    rw [adjoint_map_left p q hpq] at h
    exact h
  have ht : (((splitSL H q x)⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R)ᵀ *
      ((splitSL H q x : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  calc
    _ = ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A).map p *
        (((splitSL H q x)⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R)ᵀ *
          (((splitSL H q x : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R)ᵀ *
            (H.gram : Matrix Ix Ix A).map p *
              ((splitSL H p x : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R)) := by
      rw [hpres]
    _ = ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A).map p *
        ((((splitSL H q x)⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R)ᵀ *
          ((splitSL H q x : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R)ᵀ) *
            (H.gram : Matrix Ix Ix A).map p *
              ((splitSL H p x : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [ht, Matrix.mul_one, gram_inv_map_mul, Matrix.one_mul]

omit [Fintype Ix] [DecidableEq Ix] in
/-- Matrices over `A` are determined by their images along jointly injective maps. -/
theorem matrix_eq_of_maps {p q : A →+* R} (hinj : ∀ a b : A, p a = p b → q a = q b → a = b)
    {x y : Matrix Ix Ix A} (hp : x.map p = y.map p) (hq : x.map q = y.map q) : x = y := by
  ext i j
  exact hinj _ _ (congrFun (congrFun hp i) j) (congrFun (congrFun hq i) j)

/-- For jointly injective `p` and `q = p ∘ c̄`, an isometry is determined by its image
along `p`. -/
theorem splitSL_injective (H : Form c Ix) (p q : A →+* R) (hpq : ∀ a, q a = p (c.bar a))
    (hinj : ∀ a b : A, p a = p b → q a = q b → a = b) :
    Function.Injective (splitSL H p) := by
  intro x y hxy
  have hx := splitSL_conj H p q hpq x
  have hy := splitSL_conj H p q hpq y
  rw [hxy] at hx
  have hT : (((splitSL H q x)⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R)ᵀ =
      (((splitSL H q y)⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R)ᵀ := by
    have h := hx.trans hy.symm
    calc
      _ = (H.gram : Matrix Ix Ix A).map p *
          (((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A).map p *
            (((splitSL H q x)⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R)ᵀ *
              (H.gram : Matrix Ix Ix A).map p) *
          ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A).map p := by
        simp only [Matrix.mul_assoc]
        rw [gram_map_mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, gram_map_mul_inv,
          Matrix.one_mul]
      _ = (H.gram : Matrix Ix Ix A).map p *
          (((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A).map p *
            (((splitSL H q y)⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R)ᵀ *
              (H.gram : Matrix Ix Ix A).map p) *
          ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A).map p := by
        rw [h]
      _ = _ := by
        simp only [Matrix.mul_assoc]
        rw [gram_map_mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, gram_map_mul_inv,
          Matrix.one_mul]
  have hq : splitSL H q x = splitSL H q y :=
    inv_injective (Subtype.ext (Matrix.transpose_injective hT))
  apply Subtype.ext
  apply Units.ext
  exact matrix_eq_of_maps hinj (congrArg Subtype.val hxy) (congrArg Subtype.val hq)

/-- For `q = p ∘ c̄` with `A → R × R` surjective, every determinant-one matrix over `R` is
the image of an isometry along `p`. -/
theorem splitSL_surjective (H : Form c Ix) (p q : A →+* R) (hpq : ∀ a, q a = p (c.bar a))
    (hinj : ∀ a b : A, p a = p b → q a = q b → a = b)
    (hsurj : ∀ r s : R, ∃ a, p a = r ∧ q a = s) :
    Function.Surjective (splitSL H p) := by
  intro s
  have hqp : ∀ a, q (c.bar a) = p a := fun a => by rw [hpq, c.bar_bar]
  set J := (H.gram : Matrix Ix Ix A).map p with hJ
  set Ji := ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A).map p with hJi
  have hJiJ : Ji * J = 1 := gram_inv_map_mul H p
  have hJJi : J * Ji = 1 := gram_map_mul_inv H p
  have hss : ((s⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R) *
      (s : Matrix Ix Ix R) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hdetJ : J.det * Ji.det = 1 := by rw [← Matrix.det_mul, hJJi, Matrix.det_one]
  let t : Matrix.SpecialLinearGroup Ix R :=
    ⟨(J * ((s⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R) * Ji)ᵀ, by
      rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul,
        Matrix.SpecialLinearGroup.det_coe, mul_one, hdetJ]⟩
  choose f hf using hsurj
  let x : Matrix Ix Ix A := Matrix.of fun i j => f ((s : Matrix Ix Ix R) i j) ((t : Matrix Ix Ix R) i j)
  have hxp : x.map p = (s : Matrix Ix Ix R) := by
    ext i j
    exact (hf _ _).1
  have hxq : x.map q = (t : Matrix Ix Ix R) := by
    ext i j
    exact (hf _ _).2
  have hdet : x.det = 1 := by
    apply hinj
    · rw [map_one, RingHom.map_det]
      change (x.map p).det = 1
      rw [hxp, Matrix.SpecialLinearGroup.det_coe]
    · rw [map_one, RingHom.map_det]
      change (x.map q).det = 1
      rw [hxq, Matrix.SpecialLinearGroup.det_coe]
  have hpres : Preserves H x := by
    apply matrix_eq_of_maps hinj
    · simp only [Matrix.map_mul]
      rw [adjoint_map_left p q hpq, hxq, hxp]
      change (J * ((s⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R) * Ji)ᵀᵀ * J *
        (s : Matrix Ix Ix R) = J
      rw [Matrix.transpose_transpose]
      calc
        _ = J * ((s⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R) * (Ji * J) *
            (s : Matrix Ix Ix R) := by simp only [Matrix.mul_assoc]
        _ = J * (((s⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R) *
            (s : Matrix Ix Ix R)) := by rw [hJiJ, Matrix.mul_one, Matrix.mul_assoc]
        _ = J := by rw [hss, Matrix.mul_one]
    · simp only [Matrix.map_mul]
      rw [adjoint_map_right p q hpq, hxq, hxp, gram_map_right H p q hpq]
      change (s : Matrix Ix Ix R)ᵀ * Jᵀ *
        (J * ((s⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R) * Ji)ᵀ = Jᵀ
      rw [← Matrix.transpose_mul, ← Matrix.transpose_mul]
      congr 1
      calc
        _ = J * ((s⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R) * (Ji * J) *
            (s : Matrix Ix Ix R) := by simp only [Matrix.mul_assoc]
        _ = J * (((s⁻¹ : Matrix.SpecialLinearGroup Ix R) : Matrix Ix Ix R) *
            (s : Matrix Ix Ix R)) := by rw [hJiJ, Matrix.mul_one, Matrix.mul_assoc]
        _ = J := by rw [hss, Matrix.mul_one]
  refine ⟨⟨Matrix.SpecialLinearGroup.toGL ⟨x, hdet⟩, Subgroup.mem_inf.mpr ⟨hpres, ?_⟩⟩, ?_⟩
  · rw [MonoidHom.mem_ker]
    apply Units.ext
    exact hdet
  · apply Subtype.ext
    exact hxp

/-- For `q = p ∘ c̄` with `A → R × R` bijective, the determinant-one isometries of `H` are
`SL(R)` through `p`. -/
def splitEquiv (H : Form c Ix) (p q : A →+* R) (hpq : ∀ a, q a = p (c.bar a))
    (hinj : ∀ a b : A, p a = p b → q a = q b → a = b)
    (hsurj : ∀ r s : R, ∃ a, p a = r ∧ q a = s) :
    specialUnitarySubgroup H ≃* Matrix.SpecialLinearGroup Ix R :=
  MulEquiv.ofBijective (splitSL H p)
    ⟨splitSL_injective H p q hpq hinj, splitSL_surjective H p q hpq hinj hsurj⟩

@[simp] theorem coe_splitEquiv (H : Form c Ix) (p q : A →+* R) (hpq : ∀ a, q a = p (c.bar a))
    (hinj : ∀ a b : A, p a = p b → q a = q b → a = b)
    (hsurj : ∀ r s : R, ∃ a, p a = r ∧ q a = s) (x : specialUnitarySubgroup H) :
    ((splitEquiv H p q hpq hinj hsurj x : Matrix.SpecialLinearGroup Ix R) :
      Matrix Ix Ix R) = (x.1 : Matrix Ix Ix A).map p := rfl

end Abstract

section Tensor

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {R : Type u} [CommRing R] [Algebra K R]

/-- The projection `ℓ ⊗ r ↦ φ(ℓ) r` of `L ⊗_K R` attached to a `K`-algebra map
`φ : L → R`. -/
def tensorProj (φ : L →ₐ[K] R) : L ⊗[K] R →ₐ[K] R :=
  Algebra.TensorProduct.productMap φ (AlgHom.id K R)

omit [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] in
@[simp] theorem tensorProj_tmul (φ : L →ₐ[K] R) (l : L) (r : R) :
    tensorProj K L φ (l ⊗ₜ[K] r) = φ l * r := by
  simp [tensorProj]

/-- The projection attached to `φ ∘ c` is the projection attached to `φ` after the
conjugation `c ⊗ 1`. -/
theorem tensorProj_scalarConjugation (φ : L →ₐ[K] R) (x : L ⊗[K] R) :
    tensorProj K L (φ.comp (conjugation K L).toAlgHom) x =
      tensorProj K L φ (QuasiSplitUnitary.scalarConjugation R (conjugation K L) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul l r => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The two projections attached to `φ` and `φ ∘ c` identify `L ⊗_K R` with `R × R`. -/
theorem tensorProj_bijective (φ : L →ₐ[K] R) :
    Function.Bijective (fun x : L ⊗[K] R =>
      (tensorProj K L φ x, tensorProj K L (φ.comp (conjugation K L).toAlgHom) x)) := by
  let _ : Algebra L R := φ.toRingHom.toAlgebra
  have : IsScalarTower K L R := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  have hc : conjugation K L ≠ AlgEquiv.refl := conjugation_ne_one K L
  have h : (fun x : L ⊗[K] R =>
      (tensorProj K L φ x, tensorProj K L (φ.comp (conjugation K L).toAlgHom) x)) =
      QuasiSplitUnitary.tensorSplit R (conjugation K L) hc := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul l r =>
      rw [QuasiSplitUnitary.tensorSplit_tmul, tensorProj_tmul, tensorProj_tmul]
      apply Prod.ext <;> simp [mul_comm, RingHom.algebraMap_toAlgebra]
    | add x y hx hy =>
      simp only [map_add]
      rw [← hx, ← hy, Prod.mk_add_mk]
  rw [h]
  exact (QuasiSplitUnitary.tensorSplit R (conjugation K L) hc).bijective

/-- The projections attached to `φ` and `φ ∘ c` are jointly injective. -/
theorem tensorProj_injective₂ (φ : L →ₐ[K] R) (x y : L ⊗[K] R)
    (h₁ : tensorProj K L φ x = tensorProj K L φ y)
    (h₂ : tensorProj K L (φ.comp (conjugation K L).toAlgHom) x =
      tensorProj K L (φ.comp (conjugation K L).toAlgHom) y) : x = y :=
  (tensorProj_bijective K L φ).1 (Prod.ext h₁ h₂)

/-- The projections attached to `φ` and `φ ∘ c` are jointly surjective. -/
theorem tensorProj_surjective₂ (φ : L →ₐ[K] R) (r s : R) :
    ∃ x : L ⊗[K] R, tensorProj K L φ x = r ∧
      tensorProj K L (φ.comp (conjugation K L).toAlgHom) x = s := by
  obtain ⟨x, hx⟩ := (tensorProj_bijective K L φ).2 (r, s)
  exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩

end Tensor

end Langlands.GroupScheme.HermitianMatrix
