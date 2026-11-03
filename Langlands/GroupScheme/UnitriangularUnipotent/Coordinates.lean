import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Langlands.GroupScheme.AffineLinearEmbedding.Coordinate
import Langlands.GroupScheme.UnitriangularUnipotent.WeightCore

/-! # Polynomial coordinates on the upper unitriangular group scheme -/

noncomputable section

universe u

open CategoryTheory MvPolynomial

namespace Langlands.GroupScheme.UnitriangularUnipotent

open _root_.Langlands.GroupScheme.GeneralLinear

section UpperTri

variable {N : ℕ} {S T : Type*} [CommRing S] [CommRing T]

theorem upperTri_apply_of_not_lt (v : Pos N → S) {i j : Fin N} (h : ¬ i < j) :
    upperTri v i j = (1 : Matrix (Fin N) (Fin N) S) i j := by
  simp [upperTri, h]

theorem isUpperTriangular_upperTri (v : Pos N → S) : (upperTri v).IsUpperTriangular := by
  intro i j hji
  have h : j < i := hji
  exact upperTri_apply_of_lt v h

theorem det_upperTri (v : Pos N → S) : (upperTri v).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (isUpperTriangular_upperTri v)]
  exact Finset.prod_eq_one fun i _ => by
    rw [upperTri_apply_of_not_lt v (lt_irrefl i), Matrix.one_apply_eq]

/-- The upper unitriangular matrix with prescribed entries, as an invertible matrix. -/
def upperTriGL (v : Pos N → S) : GL (Fin N) S :=
  ((Matrix.isUnit_iff_isUnit_det (upperTri v)).2 (by rw [det_upperTri]; exact isUnit_one)).unit

@[simp] theorem upperTriGL_val (v : Pos N → S) :
    (upperTriGL v : Matrix (Fin N) (Fin N) S) = upperTri v :=
  rfl

theorem map_upperTri (ψ : S →+* T) (v : Pos N → S) (i j : Fin N) :
    ψ (upperTri v i j) = upperTri (fun q => ψ (v q)) i j := by
  by_cases h : i < j
  · rw [upperTri_apply_of_lt' _ h, upperTri_apply_of_lt' _ h]
  · rw [upperTri_apply_of_not_lt _ h, upperTri_apply_of_not_lt _ h, Matrix.one_apply,
      Matrix.one_apply]
    split_ifs <;> simp

end UpperTri

variable (k : Type u) [Field k] (N : ℕ)

/-- The weights `e i = -i` defining the upper unitriangular group as a block unipotent group. -/
abbrev weights : Fin N → ℤ := fun i => -(i.val : ℤ)

/-- The ideal of the coordinate ring of `GL_N` cutting out the upper unitriangular group. -/
abbrev cutIdeal : Ideal (CoordinateRing (Fin N) (CommRingCat.of k)) :=
  entryIdeal (Fin N) (CommRingCat.of k) (fun i j => weights N i ≤ weights N j)
    (fun i j => (1 : Matrix (Fin N) (Fin N) (CommRingCat.of k)) i j)

/-- The corepresentation of the upper unitriangular group functor by the quotient of the
coordinate ring of `GL_N`. -/
abbrev corep :=
  Corepresented.cutCorepresentableBy
    (isCutOutBy_blockUnipotent (n := Fin N) (R := CommRingCat.of k) (weights N))

/-- The coordinate ring of the upper unitriangular group scheme. -/
abbrev Coord : Type u := CoordinateRing (Fin N) (CommRingCat.of k) ⧸ cutIdeal k N

variable {k N}

/-- The image of the matrix entry `x_ij` in the coordinate ring of the unitriangular group. -/
def u (i j : Fin N) : Coord k N :=
  Ideal.Quotient.mk (cutIdeal k N) (quotient (Fin N) (CommRingCat.of k) (X (Coordinate.entry i j)))

theorem weights_le_iff (i j : Fin N) : weights N i ≤ weights N j ↔ j ≤ i := by
  simp only [weights, neg_le_neg_iff, Nat.cast_le, Fin.val_fin_le]

/-- On and below the diagonal the entry functions are those of the identity matrix. -/
theorem u_of_not_lt {i j : Fin N} (h : ¬ i < j) :
    u i j = (1 : Matrix (Fin N) (Fin N) (Coord k N)) i j := by
  have hmem : quotient (Fin N) (CommRingCat.of k) (X (Coordinate.entry i j)) -
      algebraMap (CommRingCat.of k) (CoordinateRing (Fin N) (CommRingCat.of k))
        ((1 : Matrix (Fin N) (Fin N) (CommRingCat.of k)) i j) ∈ cutIdeal k N :=
    Ideal.subset_span ⟨i, j, (weights_le_iff i j).2 (not_lt.1 h), rfl⟩
  rw [u, Ideal.Quotient.eq.2 hmem]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- The upper unitriangular matrix of the entry functions above the diagonal has all entry
functions as entries. -/
theorem upperTri_u (i j : Fin N) :
    upperTri (fun q : Pos N => u (k := k) q.1.1 q.1.2) i j = u i j := by
  by_cases h : i < j
  · rw [upperTri_apply_of_lt' _ h]
  · rw [upperTri_apply_of_not_lt _ h, u_of_not_lt h]

/-- Algebra maps out of the coordinate ring of the unitriangular group are determined by their
values on the entry functions. -/
theorem hom_ext {S : Type u} [CommRing S] [Algebra k S] {f g : Coord k N →ₐ[k] S}
    (h : ∀ i j, f (u i j) = g (u i j)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply (homEquiv (n := Fin N) (R := CommRingCat.of k) (S := S)).injective
  apply Units.ext
  ext i j
  exact h i j

variable (k N)

/-- The algebra map sending the variable at `(i, j)`, `i < j`, to the entry function `x_ij`. -/
def theta : MvPolynomial (Pos N) k →ₐ[k] Coord k N :=
  aeval (R := k) (S₁ := Coord k N) fun p : Pos N => u p.1.1 p.1.2

/-- The algebra map classifying the upper unitriangular matrix of variables. -/
def chi : Coord k N →ₐ[k] MvPolynomial (Pos N) k :=
  Ideal.Quotient.liftₐ (cutIdeal k N)
    (classify (R := CommRingCat.of k) (upperTriGL (X : Pos N → MvPolynomial (Pos N) k)))
    ((classify_eq_zero_iff _ _ _).2 fun i j hij => by
      rw [upperTriGL_val, upperTri_apply_of_not_lt _ (not_lt.2 ((weights_le_iff i j).1 hij))]
      by_cases h : i = j <;> simp [Matrix.one_apply, h])

variable {k N}

@[simp] theorem theta_X (p : Pos N) : theta k N (X p) = u p.1.1 p.1.2 :=
  aeval_X _ _

theorem chi_u (i j : Fin N) :
    chi k N (u i j) = upperTri (X : Pos N → MvPolynomial (Pos N) k) i j := by
  change classify (R := CommRingCat.of k) (upperTriGL (X : Pos N → MvPolynomial (Pos N) k))
    (quotient (Fin N) (CommRingCat.of k) (X (Coordinate.entry i j))) = _
  rw [classify_entry, upperTriGL_val]

theorem theta_upperTri (i j : Fin N) :
    theta k N (upperTri (X : Pos N → MvPolynomial (Pos N) k) i j) = u i j := by
  by_cases h : i < j
  · rw [upperTri_apply_of_lt' _ h, theta_X]
  · rw [upperTri_apply_of_not_lt _ h, u_of_not_lt h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem chi_comp_theta : (chi k N).comp (theta k N) = AlgHom.id k (MvPolynomial (Pos N) k) := by
  apply MvPolynomial.algHom_ext
  intro p
  rw [AlgHom.comp_apply, theta_X, chi_u, upperTri_apply_of_lt' _ p.2, AlgHom.id_apply]

theorem theta_comp_chi : (theta k N).comp (chi k N) = AlgHom.id k (Coord k N) :=
  hom_ext (S := Coord k N) fun i j => by rw [AlgHom.comp_apply, chi_u, theta_upperTri, AlgHom.id_apply]

@[simp] theorem chi_theta (f : MvPolynomial (Pos N) k) : chi k N (theta k N f) = f :=
  AlgHom.congr_fun chi_comp_theta f

@[simp] theorem theta_chi (b : Coord k N) : theta k N (chi k N b) = b :=
  AlgHom.congr_fun theta_comp_chi b

/-- The point classified by an algebra map out of the coordinate ring is the matrix of the
images of the entry functions. -/
theorem pt_apply {A : CommAlgCat.{u} (CommRingCat.of k)} (f : Coord k N →ₐ[k] A) (i j : Fin N) :
    ((show GL (Fin N) A from (AffineLinearEmbedding.pt (corep k N) f).1) :
      Matrix (Fin N) (Fin N) A) i j =
      f (u i j) :=
  rfl

end Langlands.GroupScheme.UnitriangularUnipotent
