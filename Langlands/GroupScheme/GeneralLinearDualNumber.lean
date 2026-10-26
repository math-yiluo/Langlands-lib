import Langlands.GroupScheme.GeneralLinear
import Mathlib.Algebra.DualNumber

/-! # Dual-number coordinates at the identity of the general linear group scheme -/

noncomputable section

universe u v w

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear.DualNumber

open TrivSqZeroExt

section Matrices

variable {n : Type v}
variable {S : Type u} [CommRing S]

/-- The matrix `εX`, formed in Mathlib's actual dual-number ring. -/
def epsilonMatrix (X : Matrix n n S) : Matrix n n (DualNumber S) :=
  X.map TrivSqZeroExt.inr

@[simp] theorem epsilonMatrix_apply (X : Matrix n n S) (i j : n) :
    epsilonMatrix X i j = TrivSqZeroExt.inr (X i j) := rfl

@[simp] theorem epsilonMatrix_zero : epsilonMatrix (0 : Matrix n n S) = 0 := by
  apply Matrix.ext
  intro i j
  simp only [epsilonMatrix_apply, Matrix.zero_apply, TrivSqZeroExt.inr_zero]

@[simp] theorem epsilonMatrix_add (X Y : Matrix n n S) :
    epsilonMatrix (X + Y) = epsilonMatrix X + epsilonMatrix Y := by
  apply Matrix.ext
  intro i j
  simp only [epsilonMatrix_apply, Matrix.add_apply, TrivSqZeroExt.inr_add]

@[simp] theorem epsilonMatrix_neg (X : Matrix n n S) :
    epsilonMatrix (-X) = -epsilonMatrix X := by
  apply Matrix.ext
  intro i j
  simp only [epsilonMatrix_apply, Matrix.neg_apply, TrivSqZeroExt.inr_neg]

variable [Fintype n]

/-- Every product of two matrices with only epsilon coefficients vanishes. -/
@[simp] theorem epsilonMatrix_mul (X Y : Matrix n n S) :
    epsilonMatrix X * epsilonMatrix Y = 0 := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, epsilonMatrix_apply, inr_mul_inr, Finset.sum_const_zero,
    Matrix.zero_apply]

variable [DecidableEq n]

/-- The square-zero calculation that turns matrix addition into multiplication. -/
theorem one_add_epsilonMatrix_mul (X Y : Matrix n n S) :
    (1 + epsilonMatrix X) * (1 + epsilonMatrix Y) = 1 + epsilonMatrix (X + Y) := by
  simp only [mul_add, add_mul, one_mul, mul_one, epsilonMatrix_mul, add_zero,
    epsilonMatrix_add]
  abel

/-- `I + εX` is a unit, with the explicitly constructed inverse `I - εX`. -/
def matrixUnit (X : Matrix n n S) : GL n (DualNumber S) where
  val := 1 + epsilonMatrix X
  inv := 1 - epsilonMatrix X
  val_inv := by
    simp only [mul_sub, add_mul, one_mul, mul_one, epsilonMatrix_mul]
    abel
  inv_val := by
    simp only [sub_mul, mul_add, one_mul, mul_one, epsilonMatrix_mul]
    abel

@[simp] theorem matrixUnit_val (X : Matrix n n S) :
    (matrixUnit X : Matrix n n (DualNumber S)) = 1 + epsilonMatrix X := rfl

@[simp] theorem matrixUnit_inv_val (X : Matrix n n S) :
    (((matrixUnit X)⁻¹ : GL n (DualNumber S)) : Matrix n n (DualNumber S)) = 1 - epsilonMatrix X := rfl

@[simp] theorem matrixUnit_zero : matrixUnit (0 : Matrix n n S) = 1 := by
  apply Units.ext
  simp

/-- Addition of coefficient matrices is the actual multiplication of dual-number units. -/
theorem matrixUnit_add (X Y : Matrix n n S) :
    matrixUnit (X + Y) = matrixUnit X * matrixUnit Y :=
  Units.ext (one_add_epsilonMatrix_mul X Y).symm

variable (n S)

/-- Reduction of an invertible matrix modulo epsilon. -/
def matrixReduction : GL n (DualNumber S) →* GL n S :=
  Matrix.GeneralLinearGroup.map (TrivSqZeroExt.fstHom S S S).toRingHom

/-- The actual group kernel of reduction to the identity. -/
abbrev MatrixKernel := (matrixReduction n S).ker

variable {n S}

@[simp] theorem matrixReduction_matrixUnit (X : Matrix n n S) :
    matrixReduction n S (matrixUnit X) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  change TrivSqZeroExt.fst ((1 : Matrix n n (DualNumber S)) i j +
    TrivSqZeroExt.inr (X i j)) = (1 : Matrix n n S) i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- The epsilon coefficients of a dual-number matrix. -/
def coefficients (g : GL n (DualNumber S)) : Matrix n n S :=
  Matrix.of fun i j => TrivSqZeroExt.snd (g i j)

@[simp] theorem coefficients_matrixUnit (X : Matrix n n S) :
    coefficients (matrixUnit X) = X := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;> simp [coefficients, Matrix.one_apply, h]

/-- The constant coefficients of a kernel element are exactly those of the identity. -/
theorem fst_of_mem_kernel (g : MatrixKernel n S) (i j : n) :
    TrivSqZeroExt.fst (g.val i j) = (1 : Matrix n n S) i j := by
  exact congrArg (fun h : GL n S => h i j) g.property

/-- Every kernel element is recovered from its actual epsilon coefficients. -/
theorem matrixUnit_coefficients (g : MatrixKernel n S) :
    matrixUnit (coefficients g.val) = g.val := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply TrivSqZeroExt.ext
  · simp only [matrixUnit_val, Matrix.add_apply, epsilonMatrix_apply, fst_add, fst_inr,
      add_zero]
    by_cases h : i = j <;> simpa [Matrix.one_apply, h] using (fst_of_mem_kernel g i j).symm
  · by_cases h : i = j <;> simp [coefficients, h]

/-- Matrices and the identity kernel of actual dual-number general linear matrices. -/
def matrixKernelEquiv : Matrix n n S ≃ MatrixKernel n S where
  toFun X := ⟨matrixUnit X, matrixReduction_matrixUnit X⟩
  invFun g := coefficients g.val
  left_inv := coefficients_matrixUnit
  right_inv g := Subtype.ext (matrixUnit_coefficients g)

/-- The correspondence is an isomorphism from the additive matrix group. -/
def matrixKernelMulEquiv : Multiplicative (Matrix n n S) ≃* MatrixKernel n S where
  toEquiv := Multiplicative.toAdd.trans matrixKernelEquiv
  map_mul' X Y := Subtype.ext (matrixUnit_add X.toAdd Y.toAdd)

end Matrices

section RingMaps

variable {S : Type u} [CommRing S]
variable {T : Type w} [CommRing T]

/-- Coefficient change on the actual dual-number ring, on both coefficients. -/
def coefficientMap (f : S →+* T) : DualNumber S →+* DualNumber T where
  toFun z := (f z.fst, f z.snd)
  map_one' := TrivSqZeroExt.ext (map_one f) (map_zero f)
  map_zero' := TrivSqZeroExt.ext (map_zero f) (map_zero f)
  map_add' x y := TrivSqZeroExt.ext (map_add f _ _) (map_add f _ _)
  map_mul' x y := TrivSqZeroExt.ext (map_mul f _ _) (by
    change f (x.fst * y.snd + x.snd * y.fst) =
      f x.fst * f y.snd + f x.snd * f y.fst
    simp only [map_add, map_mul])

@[simp] theorem coefficientMap_fst (f : S →+* T) (z : DualNumber S) :
    (coefficientMap f z).fst = f z.fst := rfl

@[simp] theorem coefficientMap_snd (f : S →+* T) (z : DualNumber S) :
    (coefficientMap f z).snd = f z.snd := rfl

@[simp] theorem coefficientMap_inr (f : S →+* T) (s : S) :
    coefficientMap f (TrivSqZeroExt.inr s) = TrivSqZeroExt.inr (f s) :=
  TrivSqZeroExt.ext (map_zero f) rfl

@[simp] theorem coefficientMap_eps (f : S →+* T) :
    coefficientMap f (DualNumber.eps : DualNumber S) = DualNumber.eps := by
  simp only [DualNumber.eps, coefficientMap_inr, map_one]

/-- The actual algebra endomorphism `ε ↦ rε`, fixing the constant coefficient. -/
def epsilonScale (r : S) : DualNumber S →ₐ[S] DualNumber S :=
  TrivSqZeroExt.map (r • (LinearMap.id : S →ₗ[S] S))

@[simp] theorem epsilonScale_fst (r : S) (z : DualNumber S) :
    (epsilonScale r z).fst = z.fst := by
  simp only [epsilonScale, TrivSqZeroExt.fst_map]

@[simp] theorem epsilonScale_snd (r : S) (z : DualNumber S) :
    (epsilonScale r z).snd = r * z.snd := by
  simp only [epsilonScale, TrivSqZeroExt.snd_map, LinearMap.smul_apply,
    LinearMap.id_apply, smul_eq_mul]

@[simp] theorem epsilonScale_eps (r : S) :
    epsilonScale r (DualNumber.eps : DualNumber S) = r • DualNumber.eps := by
  apply TrivSqZeroExt.ext <;> simp

end RingMaps

section MatrixMaps

variable {n : Type v} [Fintype n] [DecidableEq n]
variable {S : Type u} [CommRing S] {T : Type w} [CommRing T]

/-- Coefficient change commutes with the explicitly constructed unit. -/
theorem matrixUnit_map (f : S →+* T) (X : Matrix n n S) :
    Matrix.GeneralLinearGroup.map (coefficientMap f) (matrixUnit X) =
      matrixUnit (X.map f) := by
  apply Units.ext
  change (coefficientMap f).mapMatrix (1 + epsilonMatrix X) =
    1 + epsilonMatrix (X.map f)
  rw [map_add, map_one]
  congr 1
  apply Matrix.ext
  intro i j
  exact coefficientMap_inr f (X i j)

/-- Scaling epsilon is scalar multiplication on the coefficient matrix. -/
theorem matrixUnit_scale (r : S) (X : Matrix n n S) :
    Matrix.GeneralLinearGroup.map (epsilonScale r).toRingHom (matrixUnit X) =
      matrixUnit (r • X) := by
  apply Units.ext
  change (epsilonScale r).mapMatrix (1 + epsilonMatrix X) =
    1 + epsilonMatrix (r • X)
  rw [map_add, map_one]
  congr 1
  apply Matrix.ext
  intro i j
  apply TrivSqZeroExt.ext <;> simp [Matrix.smul_apply, smul_eq_mul, mul_comm]

/-- Coefficient change preserves the identity kernel. -/
def matrixKernelMap (f : S →+* T) : MatrixKernel n S →* MatrixKernel n T where
  toFun g := ⟨Matrix.GeneralLinearGroup.map (coefficientMap f) g.val, by
    change matrixReduction n T _ = 1
    have h : matrixReduction n T
        (Matrix.GeneralLinearGroup.map (coefficientMap f) g.val) =
        Matrix.GeneralLinearGroup.map f (matrixReduction n S g.val) := rfl
    rw [h, g.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

/-- Epsilon scaling preserves the identity kernel, including for a nonunit scalar. -/
def matrixKernelScale (r : S) : MatrixKernel n S →* MatrixKernel n S where
  toFun g := ⟨Matrix.GeneralLinearGroup.map (epsilonScale r).toRingHom g.val, by
    change matrixReduction n S _ = 1
    have h : matrixReduction n S
        (Matrix.GeneralLinearGroup.map (epsilonScale r).toRingHom g.val) =
        matrixReduction n S g.val := by
      apply Units.ext
      apply Matrix.ext
      intro i j
      exact epsilonScale_fst r (g.val i j)
    exact h.trans g.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

/-- Naturality of the bundled kernel coordinates. -/
theorem matrixKernelEquiv_naturality (f : S →+* T) (X : Matrix n n S) :
    matrixKernelMap f (matrixKernelEquiv X) = matrixKernelEquiv (X.map f) :=
  Subtype.ext (matrixUnit_map f X)

/-- Scalar compatibility of the bundled kernel coordinates. -/
theorem matrixKernelEquiv_scale (r : S) (X : Matrix n n S) :
    matrixKernelScale r (matrixKernelEquiv X) = matrixKernelEquiv (r • X) :=
  Subtype.ext (matrixUnit_scale r X)

end MatrixMaps

section SchemePoints

variable {n : Type} [Fintype n] [DecidableEq n]
variable {R : CommRingCat.{u}}
variable {S T : Type u} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- Coefficient change as a morphism of dual-number algebras over the fixed base. -/
def coefficientAlgMap (f : S →ₐ[R] T) : DualNumber S →ₐ[R] DualNumber T where
  __ := coefficientMap f.toRingHom
  commutes' r := TrivSqZeroExt.ext (f.commutes r) (map_zero f)

/-- Epsilon scaling as a morphism over the fixed base. -/
def epsilonScaleAlg (r : S) : DualNumber S →ₐ[R] DualNumber S :=
  (epsilonScale r).restrictScalars R

/-- Actual affine points of the published general linear group scheme. -/
abbrev AffinePoints (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u})
    (S : Type u) [CommRing S] [Algebra R S] :=
  ((algSpec R).obj (op (CommAlgCat.of R S)) ⟶ (groupScheme n R).X)

/-- Coefficient maps act on actual points by precomposing with their spectrum maps. -/
def affineMap (f : S →ₐ[R] T) : AffinePoints n R S →* AffinePoints n R T :=
  ((groupScheme n R).points.map ((algSpec R).map (CommAlgCat.ofHom f).op).op).hom

@[simp] theorem affineMap_apply (f : S →ₐ[R] T) (x : AffinePoints n R S) :
    affineMap f x = (algSpec R).map (CommAlgCat.ofHom f).op ≫ x := rfl

/-- The published affine-point comparison carries actual restriction to entrywise change. -/
theorem affineMap_matrix (f : S →ₐ[R] T) (x : AffinePoints n R S) :
    affinePointsEquiv n R (CommAlgCat.of R T) (affineMap f x) =
      Matrix.GeneralLinearGroup.map f.toRingHom
        (affinePointsEquiv n R (CommAlgCat.of R S) x) :=
  affinePointsEquiv_naturality (CommAlgCat.ofHom f) x

/-- The actual dual-number scheme point whose matrix is `I + εX`. -/
def pointUnit (X : Matrix n n S) : AffinePoints n R (DualNumber S) :=
  (affinePointsEquiv n R (CommAlgCat.of R (DualNumber S))).symm (matrixUnit X)

@[simp] theorem pointUnit_matrix (X : Matrix n n S) :
    affinePointsEquiv n R (CommAlgCat.of R (DualNumber S)) (pointUnit X) = matrixUnit X :=
  MulEquiv.apply_symm_apply _ _

/-- Reduction of actual scheme points, by the spectrum of the dual-number projection. -/
def pointReduction : AffinePoints n R (DualNumber S) →* AffinePoints n R S :=
  affineMap (TrivSqZeroExt.fstHom R S S)

/-- The identity kernel inside the actual scheme-point group. -/
abbrev PointKernel (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u})
    (S : Type u) [CommRing S] [Algebra R S] :=
  (pointReduction (n := n) (R := R) (S := S)).ker

/-- Actual scheme reduction becomes matrix reduction under `affinePointsEquiv`. -/
theorem pointReduction_matrix (x : AffinePoints n R (DualNumber S)) :
    affinePointsEquiv n R (CommAlgCat.of R S) (pointReduction x) =
      matrixReduction n S (affinePointsEquiv n R (CommAlgCat.of R (DualNumber S)) x) :=
  affineMap_matrix (TrivSqZeroExt.fstHom R S S) x

@[simp] theorem pointReduction_pointUnit (X : Matrix n n S) :
    pointReduction (pointUnit X : AffinePoints n R (DualNumber S)) = 1 := by
  apply (affinePointsEquiv n R (CommAlgCat.of R S)).injective
  rw [pointReduction_matrix, pointUnit_matrix, matrixReduction_matrixUnit, map_one]

/-- The published comparison restricts to the actual identity kernels. -/
def pointKernelComparison : PointKernel n R S ≃* MatrixKernel n S where
  toFun x := ⟨affinePointsEquiv n R (CommAlgCat.of R (DualNumber S)) x.val, by
    change matrixReduction n S _ = 1
    rw [← pointReduction_matrix, x.property, map_one]⟩
  invFun g := ⟨(affinePointsEquiv n R (CommAlgCat.of R (DualNumber S))).symm g.val, by
    apply (affinePointsEquiv n R (CommAlgCat.of R S)).injective
    rw [pointReduction_matrix, MulEquiv.apply_symm_apply, g.property, map_one]⟩
  left_inv x := Subtype.ext (MulEquiv.symm_apply_apply _ x.val)
  right_inv g := Subtype.ext (MulEquiv.apply_symm_apply _ g.val)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

/-- Matrices are canonically the identity kernel in actual dual-number scheme points. -/
def pointKernelEquiv : Matrix n n S ≃ PointKernel n R S :=
  matrixKernelEquiv.trans pointKernelComparison.symm.toEquiv

/-- The same correspondence as an isomorphism from the additive matrix group. -/
def pointKernelMulEquiv : Multiplicative (Matrix n n S) ≃* PointKernel n R S :=
  matrixKernelMulEquiv.trans pointKernelComparison.symm

@[simp] theorem pointKernelEquiv_val (X : Matrix n n S) :
    (pointKernelEquiv (R := R) X).val = pointUnit X := rfl

/-- The inverse correspondence takes epsilon coefficients in published affine coordinates. -/
@[simp] theorem pointKernelEquiv_symm (x : PointKernel n R S) :
    pointKernelEquiv.symm x =
      coefficients (affinePointsEquiv n R (CommAlgCat.of R (DualNumber S)) x.val) := rfl

/-- The actual group-scheme law is addition of coefficient matrices at the identity. -/
theorem pointUnit_add (X Y : Matrix n n S) :
    pointUnit (R := R) (X + Y) = pointUnit X * pointUnit Y := by
  apply (affinePointsEquiv n R (CommAlgCat.of R (DualNumber S))).injective
  rw [map_mul, pointUnit_matrix, pointUnit_matrix, pointUnit_matrix, matrixUnit_add]

/-- The bundled scheme-point coordinates carry addition to the actual kernel product. -/
theorem pointKernelEquiv_add (X Y : Matrix n n S) :
    pointKernelEquiv (R := R) (X + Y) = pointKernelEquiv X * pointKernelEquiv Y :=
  Subtype.ext (pointUnit_add X Y)

/-- Naturality uses actual precomposition with the coefficient-change spectrum map. -/
theorem pointUnit_naturality (f : S →ₐ[R] T) (X : Matrix n n S) :
    affineMap (coefficientAlgMap f) (pointUnit X) = pointUnit (X.map f) := by
  apply (affinePointsEquiv n R (CommAlgCat.of R (DualNumber T))).injective
  rw [affineMap_matrix, pointUnit_matrix, pointUnit_matrix]
  exact matrixUnit_map f.toRingHom X

/-- The scalar operation comes from the actual test-algebra map `ε ↦ rε`. -/
theorem pointUnit_scale (r : S) (X : Matrix n n S) :
    affineMap (epsilonScaleAlg (R := R) r) (pointUnit X) = pointUnit (r • X) := by
  apply (affinePointsEquiv n R (CommAlgCat.of R (DualNumber S))).injective
  rw [affineMap_matrix, pointUnit_matrix, pointUnit_matrix]
  exact matrixUnit_scale r X

/-- Coefficient change on actual scheme points restricts to their identity kernels. -/
def pointKernelMap (f : S →ₐ[R] T) : PointKernel n R S →* PointKernel n R T where
  toFun x := ⟨affineMap (coefficientAlgMap f) x.val, by
    obtain ⟨X, rfl⟩ := (pointKernelEquiv (n := n) (R := R) (S := S)).surjective x
    change pointReduction _ = 1
    rw [pointKernelEquiv_val, pointUnit_naturality, pointReduction_pointUnit]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

/-- Epsilon scaling restricts to actual scheme-point identity kernels. -/
def pointKernelScale (r : S) : PointKernel n R S →* PointKernel n R S where
  toFun x := ⟨affineMap (epsilonScaleAlg (R := R) r) x.val, by
    obtain ⟨X, rfl⟩ := (pointKernelEquiv (n := n) (R := R) (S := S)).surjective x
    change pointReduction _ = 1
    rw [pointKernelEquiv_val, pointUnit_scale, pointReduction_pointUnit]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

/-- The bundled scheme-point equivalence is natural in the coefficient algebra. -/
theorem pointKernelEquiv_naturality (f : S →ₐ[R] T) (X : Matrix n n S) :
    pointKernelMap f (pointKernelEquiv X) = pointKernelEquiv (X.map f) :=
  Subtype.ext (pointUnit_naturality f X)

/-- The bundled scheme-point equivalence respects the actual epsilon-scaling map. -/
theorem pointKernelEquiv_scale (r : S) (X : Matrix n n S) :
    pointKernelScale (R := R) r (pointKernelEquiv X) = pointKernelEquiv (r • X) :=
  Subtype.ext (pointUnit_scale r X)

/-- Recovery of coefficients is natural for every element of the actual kernel. -/
theorem pointKernelEquiv_symm_naturality (f : S →ₐ[R] T) (x : PointKernel n R S) :
    pointKernelEquiv.symm (pointKernelMap f x) = (pointKernelEquiv.symm x).map f := by
  obtain ⟨X, rfl⟩ := (pointKernelEquiv (n := n) (R := R) (S := S)).surjective x
  rw [pointKernelEquiv_naturality, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Coefficient recovery respects epsilon scaling for every element of the actual kernel. -/
theorem pointKernelEquiv_symm_scale (r : S) (x : PointKernel n R S) :
    pointKernelEquiv.symm (pointKernelScale r x) = r • pointKernelEquiv.symm x := by
  obtain ⟨X, rfl⟩ := (pointKernelEquiv (n := n) (R := R) (S := S)).surjective x
  rw [pointKernelEquiv_scale, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end SchemePoints

end Langlands.GroupScheme.GeneralLinear.DualNumber
