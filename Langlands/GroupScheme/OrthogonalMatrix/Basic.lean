import Langlands.GroupScheme.GeneralLinear
import Langlands.GroupScheme.Multiplicative
import Langlands.AbelianScheme.KernelBaseChange

/-! # The split orthogonal group scheme from explicit matrix coordinates

For a finite index type `l` and a commutative ring `R`, this module constructs the affine
group scheme `O_{2l}` over `Spec R` of the split quadratic form
`q(x) = ∑ a, x (inl a) * x (inr a)` on row vectors indexed by `l ⊕ l`. Its Gram matrix is
`Q = [[0, 1], [0, 0]]` and its polar matrix is `J = Q + Qᵀ = [[0, 1], [1, 0]]`. The points
with values in a commutative `R`-algebra `S` are the matrices `g ∈ M_{l ⊕ l}(S)` with
`g Q gᵀ - Q = U - Uᵀ` for some `U`, i.e. `g Q gᵀ ≡ Q` modulo alternating matrices. In every
characteristic this is equivalent to `g J gᵀ = J` together with the vanishing of the diagonal
entries `∑ a, g i (inl a) * g i (inr a)` of `g Q gᵀ`. The coordinate ring is the polynomial
ring in the matrix entries modulo these equations; no inverse variables are needed, because
such a matrix is invertible with inverse `J gᵀ J`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.OrthogonalMatrix

section Alternating

variable {n : Type*} [Fintype n] {A : Type*} [CommRing A]

/-- A square matrix is alternating when it has the form `U - Uᵀ`. -/
def IsAlt (M : Matrix n n A) : Prop :=
  ∃ U : Matrix n n A, M = U - Uᵀ

omit [Fintype n] in
theorem isAlt_zero : IsAlt (0 : Matrix n n A) :=
  ⟨0, by simp⟩

omit [Fintype n] in
theorem IsAlt.add {M N : Matrix n n A} (hM : IsAlt M) (hN : IsAlt N) : IsAlt (M + N) := by
  obtain ⟨U, rfl⟩ := hM
  obtain ⟨V, rfl⟩ := hN
  exact ⟨U + V, by rw [Matrix.transpose_add]; abel⟩

omit [Fintype n] in
theorem IsAlt.neg {M : Matrix n n A} (hM : IsAlt M) : IsAlt (-M) := by
  obtain ⟨U, rfl⟩ := hM
  exact ⟨Uᵀ, by rw [Matrix.transpose_transpose, neg_sub]⟩

omit [Fintype n] in
theorem IsAlt.sub {M N : Matrix n n A} (hM : IsAlt M) (hN : IsAlt N) : IsAlt (M - N) := by
  rw [sub_eq_add_neg]
  exact hM.add hN.neg

omit [Fintype n] in
theorem isAlt_sub_transpose (U : Matrix n n A) : IsAlt (U - Uᵀ) :=
  ⟨U, rfl⟩

/-- Congruence preserves alternating matrices. -/
theorem IsAlt.conj {M : Matrix n n A} (hM : IsAlt M) {m : Type*} [Fintype m]
    (g : Matrix m n A) : IsAlt (g * M * gᵀ) := by
  obtain ⟨U, rfl⟩ := hM
  refine ⟨g * U * gᵀ, ?_⟩
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

omit [Fintype n] in
theorem IsAlt.map {M : Matrix n n A} (hM : IsAlt M) {B : Type*} [CommRing B] (f : A →+* B) :
    IsAlt (M.map f) := by
  obtain ⟨U, rfl⟩ := hM
  exact ⟨U.map f, by rw [Matrix.map_sub _ (map_sub f), Matrix.transpose_map]⟩

/-- The strictly upper triangular part of a square matrix, for the order of the indices given by
an enumeration. -/
def strictUpper (M : Matrix n n A) : Matrix n n A :=
  Matrix.of fun i j => if Fintype.equivFin n i < Fintype.equivFin n j then M i j else 0

theorem strictUpper_map (M : Matrix n n A) {B : Type*} [CommRing B] (f : A →+* B) :
    strictUpper (M.map f) = (strictUpper M).map f := by
  ext i j
  simp only [strictUpper, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp

/-- A matrix with `M + Mᵀ = 0` and zero diagonal is its strictly upper triangular part minus the
transpose of it. -/
theorem strictUpper_sub_transpose (M : Matrix n n A) (hM : M + Mᵀ = 0) (hd : ∀ i, M i i = 0) :
    strictUpper M - (strictUpper M)ᵀ = M := by
  ext i j
  have hji : M j i = -M i j := by
    have := congrFun (congrFun hM i) j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply] at this
    linear_combination this
  simp only [strictUpper, Matrix.sub_apply, Matrix.transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy (Fintype.equivFin n i) (Fintype.equivFin n j) with h | h | h
  · simp [h, lt_asymm h]
  · have hij : i = j := (Fintype.equivFin n).injective h
    subst hij
    simp [hd]
  · simp [h, lt_asymm h, hji]

/-- **Alternating matrices.** A matrix is `U - Uᵀ` for some `U` exactly when `M + Mᵀ = 0` and
its diagonal vanishes. -/
theorem isAlt_iff (M : Matrix n n A) : IsAlt M ↔ M + Mᵀ = 0 ∧ ∀ i, M i i = 0 := by
  constructor
  · rintro ⟨U, rfl⟩
    refine ⟨by rw [Matrix.transpose_sub, Matrix.transpose_transpose]; abel, fun i => ?_⟩
    simp
  · rintro ⟨h, hd⟩
    exact ⟨strictUpper M, (strictUpper_sub_transpose M h hd).symm⟩

end Alternating

section Forms

variable (l : Type) [Fintype l] [DecidableEq l] (A : Type*) [CommRing A]

/-- The Gram matrix `Q = [[0, 1], [0, 0]]` of the split quadratic form
`q(x) = ∑ a, x (inl a) * x (inr a)`. -/
def formMatrix : Matrix (l ⊕ l) (l ⊕ l) A :=
  Matrix.fromBlocks 0 1 0 0

/-- The polar matrix `J = Q + Qᵀ = [[0, 1], [1, 0]]` of the split quadratic form. -/
def polarMatrix : Matrix (l ⊕ l) (l ⊕ l) A :=
  Matrix.fromBlocks 0 1 1 0

variable {l A}

omit [Fintype l] in
theorem formMatrix_add_transpose :
    formMatrix l A + (formMatrix l A)ᵀ = polarMatrix l A := by
  simp [formMatrix, polarMatrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_add]

omit [Fintype l] in
@[simp] theorem polarMatrix_transpose : (polarMatrix l A)ᵀ = polarMatrix l A := by
  simp [polarMatrix, Matrix.fromBlocks_transpose]

@[simp] theorem polarMatrix_mul_self : polarMatrix l A * polarMatrix l A = 1 := by
  simp [polarMatrix, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

omit [Fintype l] in
theorem formMatrix_map {B : Type*} [CommRing B] (f : A →+* B) :
    (formMatrix l A).map f = formMatrix l B := by
  simp [formMatrix, Matrix.fromBlocks_map]

omit [Fintype l] in
theorem polarMatrix_map {B : Type*} [CommRing B] (f : A →+* B) :
    (polarMatrix l A).map f = polarMatrix l B := by
  simp [polarMatrix, Matrix.fromBlocks_map]

omit [Fintype l] in
theorem formMatrix_apply (i j : l ⊕ l) :
    formMatrix l A i j = match i, j with
      | Sum.inl a, Sum.inr b => if a = b then 1 else 0
      | _, _ => 0 := by
  rcases i with a | a <;> rcases j with b | b <;>
    simp [formMatrix, Matrix.one_apply]

/-- The defect `g Q gᵀ - Q` of a matrix. -/
def defect (g : Matrix (l ⊕ l) (l ⊕ l) A) : Matrix (l ⊕ l) (l ⊕ l) A :=
  g * formMatrix l A * gᵀ - formMatrix l A

theorem defect_map (g : Matrix (l ⊕ l) (l ⊕ l) A) {B : Type*} [CommRing B] (f : A →+* B) :
    (defect g).map f = defect (g.map f) := by
  rw [defect, defect, Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    formMatrix_map]

/-- The defect of a product. -/
theorem defect_mul (g h : Matrix (l ⊕ l) (l ⊕ l) A) :
    defect (g * h) = g * defect h * gᵀ + defect g := by
  simp only [defect, Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

theorem defect_add_transpose (g : Matrix (l ⊕ l) (l ⊕ l) A) :
    defect g + (defect g)ᵀ = g * polarMatrix l A * gᵀ - polarMatrix l A := by
  rw [← formMatrix_add_transpose, defect, Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_assoc]
  abel

theorem defect_apply_self (g : Matrix (l ⊕ l) (l ⊕ l) A) (i : l ⊕ l) :
    defect g i i = ∑ a, g i (Sum.inl a) * g i (Sum.inr a) := by
  simp only [defect, formMatrix, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply,
    mul_zero, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rcases i with a | a <;> simp

end Forms

section Matrices

variable (l : Type) [Fintype l] [DecidableEq l] (A : Type*) [CommRing A]

/-- The orthogonal matrices of the split quadratic form: `g Q gᵀ - Q` is alternating. -/
def orthogonalGroup : Submonoid (Matrix (l ⊕ l) (l ⊕ l) A) where
  carrier := {g | IsAlt (defect g)}
  one_mem' := by
    change IsAlt (defect 1)
    rw [defect, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one, sub_self]
    exact isAlt_zero
  mul_mem' := by
    intro g h hg hh
    change IsAlt (defect (g * h))
    rw [defect_mul]
    exact (IsAlt.conj hh g).add hg

variable {l A}

theorem mem_orthogonalGroup_iff (g : Matrix (l ⊕ l) (l ⊕ l) A) :
    g ∈ orthogonalGroup l A ↔ IsAlt (defect g) :=
  Iff.rfl

/-- **Membership in coordinates.** A matrix is orthogonal exactly when `g J gᵀ = J` and every
row `x` of `g` has `q(x) = ∑ a, x (inl a) * x (inr a) = 0`. -/
theorem mem_orthogonalGroup_iff' (g : Matrix (l ⊕ l) (l ⊕ l) A) :
    g ∈ orthogonalGroup l A ↔
      g * polarMatrix l A * gᵀ = polarMatrix l A ∧
        ∀ i, ∑ a, g i (Sum.inl a) * g i (Sum.inr a) = 0 := by
  rw [mem_orthogonalGroup_iff, isAlt_iff, defect_add_transpose, sub_eq_zero]
  simp only [defect_apply_self]

theorem polar_mul_self (g : orthogonalGroup l A) :
    (g : Matrix (l ⊕ l) (l ⊕ l) A) * polarMatrix l A * (g : Matrix (l ⊕ l) (l ⊕ l) A)ᵀ =
      polarMatrix l A :=
  ((mem_orthogonalGroup_iff' _).1 g.2).1

/-- The inverse `J gᵀ J` of an orthogonal matrix. -/
def invMatrix (g : Matrix (l ⊕ l) (l ⊕ l) A) : Matrix (l ⊕ l) (l ⊕ l) A :=
  polarMatrix l A * gᵀ * polarMatrix l A

theorem mul_invMatrix {g : Matrix (l ⊕ l) (l ⊕ l) A} (hg : g ∈ orthogonalGroup l A) :
    g * invMatrix g = 1 := by
  have h := ((mem_orthogonalGroup_iff' g).1 hg).1
  rw [invMatrix, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, polarMatrix_mul_self]

theorem invMatrix_mul {g : Matrix (l ⊕ l) (l ⊕ l) A} (hg : g ∈ orthogonalGroup l A) :
    invMatrix g * g = 1 :=
  mul_eq_one_comm.mp (mul_invMatrix hg)

theorem invMatrix_mem {g : Matrix (l ⊕ l) (l ⊕ l) A} (hg : g ∈ orthogonalGroup l A) :
    invMatrix g ∈ orthogonalGroup l A := by
  rw [mem_orthogonalGroup_iff]
  have h := defect_mul (invMatrix g) g
  rw [invMatrix_mul hg, defect, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one,
    sub_self] at h
  have h' : defect (invMatrix g) = -(invMatrix g * defect g * (invMatrix g)ᵀ) := by
    rw [eq_neg_iff_add_eq_zero, add_comm, ← h]
  rw [h']
  exact (hg.conj _).neg

instance : Inv (orthogonalGroup l A) where
  inv g := ⟨invMatrix g, invMatrix_mem g.2⟩

@[simp] theorem coe_inv (g : orthogonalGroup l A) :
    ((g⁻¹ : orthogonalGroup l A) : Matrix (l ⊕ l) (l ⊕ l) A) = invMatrix g :=
  rfl

instance : Group (orthogonalGroup l A) where
  inv_mul_cancel g := Subtype.ext (invMatrix_mul g.2)

variable (l) in
/-- Entrywise application of a ring homomorphism, as a homomorphism of orthogonal groups. -/
def map {B : Type*} [CommRing B] (f : A →+* B) : orthogonalGroup l A →* orthogonalGroup l B where
  toFun g := ⟨(g : Matrix (l ⊕ l) (l ⊕ l) A).map f, by
    rw [mem_orthogonalGroup_iff, ← defect_map]
    exact g.2.map f⟩
  map_one' := by
    apply Subtype.ext
    exact Matrix.map_one f (map_zero f) (map_one f)
  map_mul' g h := by
    apply Subtype.ext
    exact Matrix.map_mul

@[simp] theorem coe_map {B : Type*} [CommRing B] (f : A →+* B) (g : orthogonalGroup l A) :
    ((map l f g : orthogonalGroup l B) : Matrix (l ⊕ l) (l ⊕ l) B) =
      (g : Matrix (l ⊕ l) (l ⊕ l) A).map f :=
  rfl

/-- An orthogonal matrix as an invertible matrix. -/
def toGL : orthogonalGroup l A →* GL (l ⊕ l) A where
  toFun g :=
    { val := g
      inv := ((g⁻¹ : orthogonalGroup l A) : Matrix (l ⊕ l) (l ⊕ l) A)
      val_inv := mul_invMatrix g.2
      inv_val := invMatrix_mul g.2 }
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

@[simp] theorem coe_toGL (g : orthogonalGroup l A) :
    ((toGL g : GL (l ⊕ l) A) : Matrix (l ⊕ l) (l ⊕ l) A) = g :=
  rfl

theorem ext {g h : orthogonalGroup l A}
    (H : ∀ i j, (g : Matrix (l ⊕ l) (l ⊕ l) A) i j = (h : Matrix (l ⊕ l) (l ⊕ l) A) i j) :
    g = h :=
  Subtype.ext (Matrix.ext H)

end Matrices

section Algebra

variable (l : Type) [Fintype l] [DecidableEq l] (R : Type u) [CommRing R]

/-- The matrix of independent polynomial entry variables. -/
def genericMatrix : Matrix (l ⊕ l) (l ⊕ l) (MvPolynomial ((l ⊕ l) × (l ⊕ l)) R) :=
  Matrix.of fun i j => X (i, j)

/-- The entries of `g J gᵀ - J` and the diagonal entries of `g Q gᵀ - Q`, for the generic
matrix `g`. -/
def relations : Set (MvPolynomial ((l ⊕ l) × (l ⊕ l)) R) :=
  Set.range (fun p : (l ⊕ l) × (l ⊕ l) =>
      (defect (genericMatrix l R) + (defect (genericMatrix l R))ᵀ) p.1 p.2) ∪
    Set.range (fun i : l ⊕ l => defect (genericMatrix l R) i i)

/-- The ideal imposing orthogonality. -/
def ideal : Ideal (MvPolynomial ((l ⊕ l) × (l ⊕ l)) R) :=
  Ideal.span (relations l R)

/-- The coordinate ring of the split orthogonal group. -/
abbrev CoordinateRing : Type u := MvPolynomial ((l ⊕ l) × (l ⊕ l)) R ⧸ ideal l R

/-- The quotient map to the orthogonal coordinate ring. -/
abbrev quotient : MvPolynomial ((l ⊕ l) × (l ⊕ l)) R →ₐ[R] CoordinateRing l R :=
  Ideal.Quotient.mkₐ R (ideal l R)

variable {l R}

/-- A ring map sends the generic defect to the defect of the image matrix. -/
theorem map_defect_genericMatrix {S : Type*} [CommRing S]
    (f : MvPolynomial ((l ⊕ l) × (l ⊕ l)) R →+* S) :
    (defect (genericMatrix l R)).map f = defect ((genericMatrix l R).map f) :=
  defect_map _ f

/-- An entry specialization kills the defining ideal exactly when its matrix is orthogonal. -/
theorem ideal_le_ker {S : Type u} [CommRing S] [Algebra R S]
    (f : MvPolynomial ((l ⊕ l) × (l ⊕ l)) R →ₐ[R] S)
    (h : (genericMatrix l R).map f ∈ orthogonalGroup l S) :
    ideal l R ≤ RingHom.ker f := by
  rw [mem_orthogonalGroup_iff, isAlt_iff] at h
  refine Ideal.span_le.mpr ?_
  rintro _ (⟨⟨i, j⟩, rfl⟩ | ⟨i, rfl⟩)
  · simp only [SetLike.mem_coe, RingHom.mem_ker]
    have := congrFun (congrFun h.1 i) j
    have e : (defect (genericMatrix l R)).map f = defect ((genericMatrix l R).map f) :=
      defect_map _ f.toRingHom
    rw [← e, ← Matrix.transpose_map, ← Matrix.map_add _ (map_add f)] at this
    exact this
  · simp only [SetLike.mem_coe, RingHom.mem_ker]
    have := h.2 i
    have e : (defect (genericMatrix l R)).map f = defect ((genericMatrix l R).map f) :=
      defect_map _ f.toRingHom
    rw [← e] at this
    exact this

variable (l R)

/-- The matrix of quotient entry coordinates is orthogonal. -/
theorem quotient_mem :
    (genericMatrix l R).map (quotient l R) ∈ orthogonalGroup l (CoordinateRing l R) := by
  have hmem : ∀ p ∈ relations l R, quotient l R p = 0 := fun p hp => by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span hp
  have e : (defect (genericMatrix l R)).map (quotient l R) =
      defect ((genericMatrix l R).map (quotient l R)) :=
    defect_map _ (quotient l R).toRingHom
  rw [mem_orthogonalGroup_iff, isAlt_iff, ← e]
  refine ⟨?_, fun i => hmem _ (Or.inr ⟨i, rfl⟩)⟩
  rw [← Matrix.transpose_map, ← Matrix.map_add _ (map_add _)]
  ext i j
  exact hmem _ (Or.inl ⟨(i, j), rfl⟩)

/-- The universal orthogonal matrix. -/
def universal : orthogonalGroup l (CoordinateRing l R) :=
  ⟨(genericMatrix l R).map (quotient l R), quotient_mem l R⟩

@[simp] theorem universal_apply (i j : l ⊕ l) :
    (universal l R : Matrix (l ⊕ l) (l ⊕ l) (CoordinateRing l R)) i j =
      quotient l R (X (i, j)) := rfl

variable {l R} {S T : Type u} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- Specialization of the universal orthogonal matrix along an algebra map. -/
def point (f : CoordinateRing l R →ₐ[R] S) : orthogonalGroup l S :=
  map l f.toRingHom (universal l R)

@[simp] theorem point_apply (f : CoordinateRing l R →ₐ[R] S) (i j : l ⊕ l) :
    (point f : Matrix (l ⊕ l) (l ⊕ l) S) i j = f (quotient l R (X (i, j))) := rfl

/-- Specialization is natural in the target algebra. -/
theorem point_comp (f : CoordinateRing l R →ₐ[R] S) (g : S →ₐ[R] T) :
    point (g.comp f) = map l g.toRingHom (point f) := rfl

@[simp] theorem point_id : point (AlgHom.id R (CoordinateRing l R)) = universal l R := rfl

/-- The values of the entry variables at an orthogonal matrix. -/
def values (g : orthogonalGroup l S) : (l ⊕ l) × (l ⊕ l) → S :=
  fun ij => (g : Matrix (l ⊕ l) (l ⊕ l) S) ij.1 ij.2

theorem map_aeval_genericMatrix (g : orthogonalGroup l S) :
    (genericMatrix l R).map (aeval (R := R) (values g)) = (g : Matrix (l ⊕ l) (l ⊕ l) S) := by
  ext i j
  simp [genericMatrix, values]

/-- The algebra map classifying an orthogonal matrix. -/
def classify (g : orthogonalGroup l S) : CoordinateRing l R →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aeval (values g)) fun _ ha =>
    RingHom.mem_ker.mp <| ideal_le_ker _
      (by rw [map_aeval_genericMatrix]; exact g.2) ha

theorem classify_comp_quotient (g : orthogonalGroup l S) :
    (classify (R := R) g).comp (quotient l R) = aeval (values g) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[simp] theorem classify_quotient (g : orthogonalGroup l S)
    (f : MvPolynomial ((l ⊕ l) × (l ⊕ l)) R) :
    classify g (quotient l R f) = aeval (values g) f :=
  AlgHom.congr_fun (classify_comp_quotient g) f

@[simp] theorem classify_entry (g : orthogonalGroup l S) (i j : l ⊕ l) :
    classify (R := R) g (quotient l R (X (i, j))) = (g : Matrix (l ⊕ l) (l ⊕ l) S) i j := by
  rw [classify_quotient, aeval_X]
  rfl

/-- Algebra maps out of the coordinate ring are exactly orthogonal matrices. -/
def homEquiv : (CoordinateRing l R →ₐ[R] S) ≃ orthogonalGroup l S where
  toFun := point
  invFun := classify
  left_inv f := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    rw [AlgHom.comp_apply, AlgHom.comp_apply, classify_entry]
    rfl
  right_inv g := ext fun i j => classify_entry g i j

@[simp] theorem classify_point (f : CoordinateRing l R →ₐ[R] S) : classify (point f) = f :=
  homEquiv.left_inv f

@[simp] theorem point_classify (g : orthogonalGroup l S) :
    point (classify (R := R) g) = g := homEquiv.right_inv g

/-- Classifying a coefficient-changed matrix is composing its classifying map. -/
theorem classify_map (g : orthogonalGroup l S) (f : S →ₐ[R] T) :
    classify (map l f.toRingHom g) = f.comp (classify (R := R) g) := by
  apply homEquiv.injective
  change point _ = point _
  rw [point_comp, point_classify, point_classify]

end Algebra

section Scheme

variable (l : Type) [Fintype l] [DecidableEq l] (R : CommRingCat.{u})

/-- The functor of orthogonal matrices, with entrywise coefficient change. -/
def functor : CommAlgCat.{u} R ⥤ GrpCat.{u} where
  obj S := GrpCat.of (orthogonalGroup l S)
  map f := GrpCat.ofHom (map l f.hom.toRingHom)
  map_id S := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    exact ext fun i j => rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact ext fun i j => rfl

@[simp] theorem functor_obj (S : CommAlgCat.{u} R) :
    (functor l R).obj S = GrpCat.of (orthogonalGroup l S) := rfl

theorem functor_map_apply {S T : CommAlgCat.{u} R} (f : S ⟶ T) (g : orthogonalGroup l S) :
    (functor l R).map f g = map l f.hom.toRingHom g := rfl

/-- The orthogonal coordinate ring as a base algebra. -/
abbrev coordinateAlgebra : CommAlgCat.{u} R := CommAlgCat.of R (CoordinateRing l R)

/-- The explicit coordinate ring corepresents the orthogonal functor. -/
def corepresentableBy :
    (functor l R ⋙ forget GrpCat).CorepresentableBy (coordinateAlgebra l R) where
  homEquiv :=
    { toFun := fun f => point f.hom
      invFun := fun g => CommAlgCat.ofHom (classify g)
      left_inv := fun f => CommAlgCat.hom_ext (classify_point f.hom)
      right_inv := fun g => point_classify g }
  homEquiv_comp g f := point_comp f.hom g.hom

/-- The split orthogonal group scheme `O_{2l}` over `Spec R`. -/
abbrev groupScheme : GroupScheme (Spec R) :=
  Corepresented.groupScheme (functor l R) (corepresentableBy l R)

@[simp] theorem groupScheme_X :
    (groupScheme l R).X = (algSpec R).obj (op (coordinateAlgebra l R)) := rfl

theorem groupScheme_left :
    (groupScheme l R).X.left = Spec (CommRingCat.of (CoordinateRing l R)) := rfl

theorem groupScheme_hom :
    (groupScheme l R).X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing l R))) := rfl

instance isAffine_groupScheme : IsAffine (groupScheme l R).X.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (CoordinateRing l R))))

instance isAffineHom_groupScheme : IsAffineHom (groupScheme l R).X.hom :=
  isAffineHom_of_isAffine _

/-- Scheme points over every relative test scheme are orthogonal matrices over its global
sections. -/
def pointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme l R).X) ≃* orthogonalGroup l Γ(T.left, ⊤) :=
  Corepresented.pointsEquiv (functor l R) (corepresentableBy l R) T

variable {l R}

/-- Restriction of scheme points applies the pullback on global sections entrywise. -/
theorem pointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme l R).X) :
    pointsEquiv l R T' (a ≫ x) = map l a.left.appTop.hom (pointsEquiv l R T x) :=
  Corepresented.pointsEquiv_naturality _ _ a x

/-- An orthogonal scheme point is determined by its matrix entries. -/
theorem points_ext {T : Over (Spec R)} {x y : T ⟶ (groupScheme l R).X}
    (h : ∀ i j, (pointsEquiv l R T x : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) i j =
      (pointsEquiv l R T y : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) i j) : x = y :=
  (pointsEquiv l R T).injective (ext h)

/-- Inclusion of orthogonal matrices into invertible matrices is a natural map. -/
def toGeneralLinear : functor l R ⟶ GeneralLinear.functor (l ⊕ l) R where
  app S := GrpCat.ofHom toGL
  naturality S T f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Units.ext
    rfl

variable (l R) in
/-- The homomorphism from the orthogonal group scheme into the general linear one. -/
def inclusion : groupScheme l R ⟶ GeneralLinear.groupScheme (l ⊕ l) R :=
  Corepresented.groupSchemeMap (corepresentableBy l R) (GeneralLinear.corepresentableBy (l ⊕ l) R)
    toGeneralLinear

/-- The inclusion on every test scheme is the usual inclusion of orthogonal matrices. -/
theorem pointsEquiv_inclusion (T : Over (Spec R)) (x : T ⟶ (groupScheme l R).X) :
    GeneralLinear.pointsEquiv (l ⊕ l) R T (x ≫ (inclusion l R).hom.hom) =
      toGL (pointsEquiv l R T x) :=
  Corepresented.groupSchemeMap_points _ _ _ x

end Scheme

section BaseChange

variable (l : Type) [Fintype l] [DecidableEq l]
variable {R R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R)

/-- On every test scheme, the pullback model and the model over the new base have the same
orthogonal matrices of global sections. -/
def baseChangeModelPointsEquiv (T : Over (Spec R')) :
    (T ⟶ ((GroupScheme.baseChange b).obj (groupScheme l R)).X) ≃*
      (T ⟶ (groupScheme l R').X) :=
  ((baseChangePointsEquiv b (groupScheme l R) T).trans
    (pointsEquiv l R ((Over.map b).obj T))).trans (pointsEquiv l R' T).symm

theorem baseChangeModelPointsEquiv_naturality {T T' : Over (Spec R')}
    (a : T' ⟶ T) (x : T ⟶ ((GroupScheme.baseChange b).obj (groupScheme l R)).X) :
    baseChangeModelPointsEquiv l b T' (a ≫ x) =
      a ≫ baseChangeModelPointsEquiv l b T x := by
  apply (pointsEquiv l R' T').injective
  simp only [baseChangeModelPointsEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality,
    pointsEquiv_naturality]
  rfl

/-- The split orthogonal group commutes with arbitrary change of the affine base. -/
def baseChangeModelIso :
    (GroupScheme.baseChange b).obj (groupScheme l R) ≅ groupScheme l R' :=
  isoOfPoints (baseChangeModelPointsEquiv l b)
    (baseChangeModelPointsEquiv_naturality l b)

/-- The model comparison preserves all entries on every relative test scheme. -/
theorem pointsEquiv_baseChangeModelIso_hom (T : Over (Spec R'))
    (x : T ⟶ ((GroupScheme.baseChange b).obj (groupScheme l R)).X) :
    pointsEquiv l R' T (x ≫ (baseChangeModelIso l b).hom.hom.hom) =
      pointsEquiv l R ((Over.map b).obj T) (baseChangePointsEquiv b _ T x) := by
  rw [baseChangeModelIso, comp_isoOfPoints_hom]
  exact (pointsEquiv l R' T).apply_symm_apply _

end BaseChange

end Langlands.GroupScheme.OrthogonalMatrix
