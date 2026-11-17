import Langlands.GroupScheme.SpecialLinearContragredient
import Langlands.GroupScheme.CenterMovingAutomorphisms
import Langlands.GroupScheme.MuAffinePresentationProof

/-! # Scalar roots of unity and the full centre of special linear groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear

section Matrices

variable (n : ℕ) {A B : Type u} [CommRing A] [CommRing B]

/-- A scalar root of unity gives a determinant-one scalar matrix. -/
def scalarRootMatrix (ζ : rootsOfUnity n A) : Matrix.SpecialLinearGroup (Fin n) A :=
  ⟨Matrix.scalar (Fin n) (ζ.val : A), by
    simpa using congrArg (fun x : Aˣ => (x : A)) ((mem_rootsOfUnity n _).mp ζ.property)⟩

@[simp]
theorem scalarRootMatrix_coe (ζ : rootsOfUnity n A) :
    (scalarRootMatrix n ζ : Matrix (Fin n) (Fin n) A) =
      Matrix.scalar (Fin n) (ζ.val : A) := rfl

/-- Scalar-root matrices depend multiplicatively on the root of unity. -/
def scalarRootMatrixHom : rootsOfUnity n A →* Matrix.SpecialLinearGroup (Fin n) A where
  toFun := scalarRootMatrix n
  map_one' := by
    apply Subtype.ext
    simp [scalarRootMatrix]
  map_mul' ζ ξ := by
    apply Subtype.ext
    change Matrix.scalar (Fin n) ((ζ.val : A) * (ξ.val : A)) =
      Matrix.scalar (Fin n) (ζ.val : A) * Matrix.scalar (Fin n) (ξ.val : A)
    exact map_mul (Matrix.scalar (Fin n)) _ _

/-- Coefficient maps preserve scalar-root matrices. -/
theorem scalarRootMatrix_map (f : A →+* B) (ζ : rootsOfUnity n A) :
    Matrix.SpecialLinearGroup.map f (scalarRootMatrix n ζ) =
      scalarRootMatrix n (restrictRootsOfUnity f n ζ) := by
  apply Subtype.ext
  ext i j
  change f (Matrix.scalar (Fin n) (ζ.val : A) i j) =
    Matrix.scalar (Fin n) (f (ζ.val : A)) i j
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- The contragredient inverts a scalar-root matrix. -/
theorem matrixContragredient_scalarRootMatrix (ζ : rootsOfUnity n A) :
    matrixContragredient (Fin n) A (scalarRootMatrix n ζ) =
      scalarRootMatrix n ζ⁻¹ := by
  rw [matrixContragredient_apply]
  change Matrix.SpecialLinearGroup.transpose (((scalarRootMatrixHom n) ζ)⁻¹) =
    scalarRootMatrix n ζ⁻¹
  rw [← map_inv]
  apply Subtype.ext
  change (Matrix.scalar (Fin n) ((ζ⁻¹).val : A)).transpose =
    Matrix.scalar (Fin n) ((ζ⁻¹).val : A)
  exact Matrix.diagonal_transpose _

/-- For positive degree the scalar-root matrix determines its root of unity. -/
theorem scalarRootMatrix_injective (hn : 0 < n) :
    Function.Injective (scalarRootMatrix n (A := A)) := by
  intro ζ ξ h
  apply Subtype.ext
  apply Units.ext
  have hm := congrArg (fun g : Matrix.SpecialLinearGroup (Fin n) A =>
    (g : Matrix (Fin n) (Fin n) A) ⟨0, hn⟩ ⟨0, hn⟩) h
  simpa [scalarRootMatrix] using hm

end Matrices

section Schemes

variable (n : ℕ) (R : CommRingCat.{u})

/-- Scalar roots on each test scheme give actual special-linear points. -/
def scalarRootPoints (T : Over (Spec R)) :
    (T ⟶ (mu (Spec R) n).X) →* (T ⟶ (groupScheme (Fin n) R).X) :=
  ((pointsEquiv (Fin n) R T).symm.toMonoidHom.comp (scalarRootMatrixHom n)).comp
    (mu.pointsEquiv (Spec R) n T).toMonoidHom

theorem pointsEquiv_scalarRootPoints (T : Over (Spec R))
    (x : T ⟶ (mu (Spec R) n).X) :
    pointsEquiv (Fin n) R T (scalarRootPoints n R T x) =
      scalarRootMatrix n (mu.pointsEquiv (Spec R) n T x) :=
  (pointsEquiv (Fin n) R T).apply_symm_apply _

theorem scalarRootPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (mu (Spec R) n).X) :
    scalarRootPoints n R T' (a ≫ x) = a ≫ scalarRootPoints n R T x := by
  apply (pointsEquiv (Fin n) R T').injective
  rw [pointsEquiv_scalarRootPoints, pointsEquiv_naturality,
    pointsEquiv_scalarRootPoints, mu.pointsEquiv_naturality, scalarRootMatrix_map]

/-- The actual scalar embedding of the roots-of-unity kernel into `SL_n`. -/
def scalarRootsOfUnityHom : (mu (Spec R) n).toGrp ⟶ groupScheme (Fin n) R :=
  homOfPoints (scalarRootPoints n R) (scalarRootPoints_naturality n R)

@[simp]
theorem comp_scalarRootsOfUnityHom (T : Over (Spec R))
    (x : T ⟶ (mu (Spec R) n).X) :
    x ≫ (scalarRootsOfUnityHom n R).hom.hom = scalarRootPoints n R T x :=
  comp_homOfPoints _ _ T x

/-- Scalar-root points are in the full scheme-theoretic centre. -/
theorem isCentral_scalarRootsOfUnityHom : IsCentral (scalarRootsOfUnityHom n R) := by
  intro T x U a y
  rw [← Category.assoc, comp_scalarRootsOfUnityHom]
  change _ * y = y * _
  apply (pointsEquiv (Fin n) R U).injective
  change pointsEquiv (Fin n) R U
      ((scalarRootPoints n R U (a ≫ x)) * y) =
    pointsEquiv (Fin n) R U (y * scalarRootPoints n R U (a ≫ x))
  rw [map_mul, map_mul, pointsEquiv_scalarRootPoints]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, scalarRootMatrix_coe]
  exact (Matrix.scalar_commute _ (Commute.all _) _).eq

/-- The scalar embedding is injective on points of every test scheme when
the degree is positive. -/
theorem scalarRootPoints_injective (hn : 0 < n) (T : Over (Spec R)) :
    Function.Injective (scalarRootPoints n R T) := by
  intro x y h
  apply (mu.pointsEquiv (Spec R) n T).injective
  apply scalarRootMatrix_injective n hn
  have hm := congrArg (pointsEquiv (Fin n) R T) h
  change pointsEquiv (Fin n) R T (scalarRootPoints n R T x) =
    pointsEquiv (Fin n) R T (scalarRootPoints n R T y) at hm
  rwa [pointsEquiv_scalarRootPoints, pointsEquiv_scalarRootPoints] at hm

/-- The contragredient inverts the image of every scalar root on every test. -/
theorem scalarRootPoints_comp_contragredientIso (T : Over (Spec R))
    (x : T ⟶ (mu (Spec R) n).X) :
    scalarRootPoints n R T x ≫ (contragredientIso (Fin n) R).hom.hom.hom =
      scalarRootPoints n R T x⁻¹ := by
  apply (pointsEquiv (Fin n) R T).injective
  rw [pointsEquiv_contragredientIso', pointsEquiv_scalarRootPoints,
    matrixContragredient_scalarRootMatrix, pointsEquiv_scalarRootPoints, map_inv]

/-- The universal `n`-th root on the quotient by `X^n - 1` is not killed by
`X^2 - 1` when `n > 2`, over any nontrivial commutative base ring. -/
theorem universalRoot_sq_ne_one [Nontrivial R] (hn : 2 < n) :
    AdjoinRoot.root (MuAffinePresentation.equation R n) ^ 2 ≠ 1 := by
  have hnonzero :
      AdjoinRoot.mk (MuAffinePresentation.equation R n)
        ((Polynomial.X : Polynomial R) ^ 2 - 1) ≠ 0 := by
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt
      (Polynomial.monic_X_pow_sub_one (by omega))
    · simpa using
        (Polynomial.X_pow_sub_C_ne_zero (R := R) (n := 2) (by decide) (1 : R))
    · simpa only [MuAffinePresentation.equation, ← Polynomial.C_1,
        Polynomial.natDegree_X_pow_sub_C] using hn
  intro h
  apply hnonzero
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] using h

/-- Inversion moves the universal root of unity, without passing to reduced
or field-valued points. -/
theorem universalCoordinate_inv_ne [Nontrivial R] (hn : 2 < n) :
    (MuAffinePresentation.coordinate R n (by omega))⁻¹ ≠
      MuAffinePresentation.coordinate R n (by omega) := by
  intro h
  have hm := inv_mul_cancel (MuAffinePresentation.coordinate R n (by omega))
  rw [h] at hm
  have hv := congrArg (fun z : rootsOfUnity n
    (AdjoinRoot (MuAffinePresentation.equation R n)) =>
      (z.val : AdjoinRoot (MuAffinePresentation.equation R n))) hm
  apply universalRoot_sq_ne_one n R hn
  change AdjoinRoot.root (MuAffinePresentation.equation R n) *
    AdjoinRoot.root (MuAffinePresentation.equation R n) = 1 at hv
  simpa only [pow_two] using hv

/-- In degree greater than two, the actual contragredient moves the full
scheme-theoretic centre over every nontrivial commutative affine base. -/
theorem not_automorphismFixesCenter_contragredientIso [Nontrivial R] (hn : 2 < n) :
    ¬ AutomorphismFixesCenter (contragredientIso (Fin n) R) := by
  let f := Spec.map (CommRingCat.ofHom
    (algebraMap R (AdjoinRoot (MuAffinePresentation.equation R n))))
  let T : Over (Spec R) := Over.mk f
  let x : T ⟶ (mu (Spec R) n).X :=
    (mu.affinePointsEquiv n f).symm (MuAffinePresentation.coordinate R n (by omega))
  have hz : scalarRootPoints n R T x ∈
      (center (groupScheme (Fin n) R)).carrier T := by
    rw [← comp_scalarRootsOfUnityHom]
    exact isCentral_scalarRootsOfUnityHom n R T x
  intro hfix
  have he := hfix T (scalarRootPoints n R T x) hz
  rw [scalarRootPoints_comp_contragredientIso] at he
  have hx := scalarRootPoints_injective n R (by omega) T he
  have hu := congrArg (mu.affinePointsEquiv n f) hx
  change mu.affinePointsEquiv n f x⁻¹ = mu.affinePointsEquiv n f x at hu
  rw [map_inv] at hu
  change ((mu.affinePointsEquiv n f)
      ((mu.affinePointsEquiv n f).symm
        (MuAffinePresentation.coordinate R n (by omega))))⁻¹ =
    (mu.affinePointsEquiv n f)
      ((mu.affinePointsEquiv n f).symm
        (MuAffinePresentation.coordinate R n (by omega))) at hu
  rw [MulEquiv.apply_symm_apply] at hu
  exact universalCoordinate_inv_ne n R hn hu

/-- A split special-linear group of degree greater than two has an actual
centre-moving automorphism over any nontrivial commutative affine base. -/
theorem hasCenterMovingAutomorphism [Nontrivial R] (hn : 2 < n) :
    HasCenterMovingAutomorphism (groupScheme (Fin n) R) :=
  ⟨contragredientIso (Fin n) R,
    not_automorphismFixesCenter_contragredientIso n R hn⟩

end Schemes

end Langlands.GroupScheme.SpecialLinear
