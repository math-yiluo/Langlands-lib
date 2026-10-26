import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.GeneralLinearDualNumber

/-! # Linear dual-number differentials of general linear scheme representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

open GeneralLinear GeneralLinear.DualNumber

variable {R : CommRingCat.{u}}
variable {n m k : Type} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
variable {S T : Type u} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- An actual scheme representation sends the dual-number identity kernel to itself. -/
def dualNumberKernelMap (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] : PointKernel n R S →* PointKernel m R S where
  toFun x := ⟨x.val ≫ ρ.hom.hom, by
    change (algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R S S)).op ≫
      (x.val ≫ ρ.hom.hom) = 1
    rw [← Category.assoc]
    change ((pointsMap ρ).app (op ((algSpec R).obj (op (CommAlgCat.of R S))))).hom
      (pointReduction x.val) = 1
    rw [x.property]
    exact map_one
      ((pointsMap ρ).app (op ((algSpec R).obj (op (CommAlgCat.of R S))))).hom⟩
  map_one' := Subtype.ext (map_one
    ((pointsMap ρ).app (op ((algSpec R).obj (op (CommAlgCat.of R (DualNumber S)))))).hom)
  map_mul' x y := Subtype.ext (map_mul
    ((pointsMap ρ).app (op ((algSpec R).obj (op (CommAlgCat.of R (DualNumber S)))))).hom
    x.val y.val)

@[simp] theorem dualNumberKernelMap_val
    (ρ : MatrixRepresentation (groupScheme n R) m) (x : PointKernel n R S) :
    (ρ.dualNumberKernelMap S x).val = x.val ≫ ρ.hom.hom := rfl

/-- Kernel maps commute with change of the coefficient algebra. -/
theorem dualNumberKernelMap_naturality
    (ρ : MatrixRepresentation (groupScheme n R) m) (f : S →ₐ[R] T)
    (x : PointKernel n R S) :
    ρ.dualNumberKernelMap T (pointKernelMap f x) =
      pointKernelMap f (ρ.dualNumberKernelMap S x) := by
  apply Subtype.ext
  exact Category.assoc _ _ _

/-- Naturality for the actual endomorphism `ε ↦ rε`, including nonunit scalars. -/
theorem dualNumberKernelMap_scale (ρ : MatrixRepresentation (groupScheme n R) m)
    (r : S) (x : PointKernel n R S) :
    ρ.dualNumberKernelMap S (pointKernelScale r x) =
      pointKernelScale r (ρ.dualNumberKernelMap S x) := by
  apply Subtype.ext
  exact Category.assoc _ _ _

/-- The linear differential obtained from actual dual-number points.
No bracket or analytic tangent-space comparison is part of this definition. -/
def differential (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] : Matrix n n S →ₗ[S] Matrix m m S where
  toFun X := pointKernelEquiv.symm (ρ.dualNumberKernelMap S (pointKernelEquiv X))
  map_add' X Y := by
    rw [pointKernelEquiv_add, map_mul]
    exact congrArg Multiplicative.toAdd
      ((pointKernelMulEquiv (n := m) (R := R) (S := S)).symm.map_mul _ _)
  map_smul' r X := by
    change pointKernelEquiv.symm
      (ρ.dualNumberKernelMap S (pointKernelEquiv (r • X))) = _
    rw [← pointKernelEquiv_scale, dualNumberKernelMap_scale,
      pointKernelEquiv_symm_scale]
    rfl

@[simp] theorem differential_apply (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) :
    ρ.differential S X =
      pointKernelEquiv.symm (ρ.dualNumberKernelMap S (pointKernelEquiv X)) := rfl

/-- The differential reconstructs exactly the image point in the actual identity kernel. -/
theorem differential_kernel (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) :
    pointKernelEquiv (ρ.differential S X) =
      ρ.dualNumberKernelMap S (pointKernelEquiv X) :=
  Equiv.apply_symm_apply _ _

/-- The defining first-order equation is an equality of actual scheme points. -/
theorem differential_pointUnit (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) :
    pointUnit (ρ.differential S X) = pointUnit X ≫ ρ.hom.hom :=
  congrArg Subtype.val (ρ.differential_kernel X)

/-- On actual affine points, `ρ(I + εX) = I + ε dρ(X)`. -/
theorem differential_affineMatrix (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) :
    ρ.affineMatrix (CommAlgCat.of R (DualNumber S)) (pointUnit X) =
      matrixUnit (ρ.differential S X) := by
  rw [affineMatrix_apply, ← differential_pointUnit, pointUnit_matrix]

/-- Entrywise epsilon coefficients compute the differential. -/
theorem differential_coefficients (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) :
    ρ.differential S X =
      coefficients (ρ.affineMatrix (CommAlgCat.of R (DualNumber S)) (pointUnit X)) := by
  rw [differential_affineMatrix, coefficients_matrixUnit]

/-- The first-order equation characterizes the differential without choosing a tangent map. -/
theorem differential_eq_iff (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) (Y : Matrix m m S) :
    ρ.differential S X = Y ↔
      ρ.affineMatrix (CommAlgCat.of R (DualNumber S)) (pointUnit X) = matrixUnit Y := by
  rw [differential_affineMatrix]
  constructor
  · exact congrArg matrixUnit
  · intro h
    simpa only [coefficients_matrixUnit] using congrArg coefficients h

/-- Any linear map satisfying the actual first-order equation is the constructed differential. -/
theorem differential_unique (ρ : MatrixRepresentation (groupScheme n R) m)
    (D : Matrix n n S →ₗ[S] Matrix m m S)
    (hD : ∀ X, ρ.affineMatrix (CommAlgCat.of R (DualNumber S)) (pointUnit X) =
      matrixUnit (D X)) :
    D = ρ.differential S := by
  apply LinearMap.ext
  intro X
  exact ((ρ.differential_eq_iff X (D X)).mpr (hD X)).symm

/-- Differentiation commutes with arbitrary maps of test algebras over the base. -/
theorem differential_naturality (ρ : MatrixRepresentation (groupScheme n R) m)
    (f : S →ₐ[R] T) (X : Matrix n n S) :
    ρ.differential T (X.map f) = (ρ.differential S X).map f := by
  simp only [differential_apply]
  rw [← pointKernelEquiv_naturality, dualNumberKernelMap_naturality,
    pointKernelEquiv_symm_naturality]

/-- Identity representations have the identity differential. -/
@[simp] theorem differential_standard (X : Matrix n n S) :
    (standard n R).differential S X = X := by
  apply (pointKernelEquiv (n := n) (R := R) (S := S)).injective
  rw [differential_kernel]
  apply Subtype.ext
  change pointUnit X ≫ 𝟙 _ = pointUnit X
  exact Category.comp_id _

/-- Trivial representations have zero differential. -/
@[simp] theorem differential_trivial (X : Matrix n n S) :
    (trivial (groupScheme n R) m).differential S X = 0 := by
  rw [differential_coefficients, trivial_affineMatrix]
  have h : (1 : GL m (DualNumber S)) = matrixUnit (0 : Matrix m m S) :=
    matrixUnit_zero.symm
  rw [h, coefficients_matrixUnit]

/-- The chain rule is induced by composition of the actual scheme-point maps. -/
theorem differential_comp (ρ : MatrixRepresentation (groupScheme n R) m)
    (σ : MatrixRepresentation (groupScheme m R) k) (X : Matrix n n S) :
    differential (ρ ≫ σ) S X = σ.differential S (ρ.differential S X) := by
  apply (pointKernelEquiv (n := k) (R := R) (S := S)).injective
  rw [differential_kernel, differential_kernel, differential_kernel]
  apply Subtype.ext
  change pointUnit X ≫ (ρ.hom.hom ≫ σ.hom.hom) =
    (pointUnit X ≫ ρ.hom.hom) ≫ σ.hom.hom
  exact (Category.assoc _ _ _).symm

/-- The chain rule as an equality of bundled linear maps. -/
theorem differential_comp_linearMap (ρ : MatrixRepresentation (groupScheme n R) m)
    (σ : MatrixRepresentation (groupScheme m R) k) :
    differential (ρ ≫ σ) S = (σ.differential S).comp (ρ.differential S) := by
  ext X i j
  exact congrArg (fun A : Matrix k k S => A i j) (differential_comp ρ σ X)

/-- The corresponding linear family of endomorphisms of the coordinate module. -/
def differentialAction (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] : Matrix n n S →ₗ[S] Module.End S (m → S) :=
  (Matrix.toLin' : Matrix m m S ≃ₗ[S] Module.End S (m → S)).toLinearMap.comp
    (ρ.differential S)

@[simp] theorem differentialAction_apply (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) (v : m → S) :
    ρ.differentialAction S X v = ρ.differential S X *ᵥ v := rfl

/-- Entrywise coefficient change intertwines the linear endomorphism families. -/
theorem differentialAction_naturality (ρ : MatrixRepresentation (groupScheme n R) m)
    (f : S →ₐ[R] T) (X : Matrix n n S) (v : m → S) :
    ρ.differentialAction T (X.map f) (fun i => f (v i)) =
      fun i => f (ρ.differentialAction S X v i) := by
  rw [differentialAction_apply, differential_naturality, differentialAction_apply]
  funext i
  exact (f.toRingHom.map_mulVec _ _ i).symm

end Langlands.GroupScheme.MatrixRepresentation
