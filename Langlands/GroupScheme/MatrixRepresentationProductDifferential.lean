import Langlands.GroupScheme.MatrixRepresentationDifferential
import Langlands.GroupScheme.GeneralLinearProductDualNumber

/-! # Linear differentials of representations of finite products of general linear schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

open GeneralLinear GeneralLinearProductDualNumber

variable {I : Type u} [Finite I]
variable {n : I → Type} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
variable {R : CommRingCat.{u}}
variable {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
variable {S T : Type u} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- Postcomposition by an actual representation maps the product identity kernel
to the identity kernel of the target general linear scheme. -/
def productDualNumberKernelMap (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] : PointKernel n R S →* DualNumber.PointKernel m R S where
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

@[simp] theorem productDualNumberKernelMap_val
    (ρ : MatrixRepresentation (groupScheme n R) m) (x : PointKernel n R S) :
    (ρ.productDualNumberKernelMap S x).val = x.val ≫ ρ.hom.hom := rfl

/-- Kernel postcomposition commutes with arbitrary coefficient change. -/
theorem productDualNumberKernelMap_naturality
    (ρ : MatrixRepresentation (groupScheme n R) m) (f : S →ₐ[R] T)
    (x : PointKernel n R S) :
    ρ.productDualNumberKernelMap T (pointKernelMap f x) =
      DualNumber.pointKernelMap f (ρ.productDualNumberKernelMap S x) := by
  apply Subtype.ext
  exact Category.assoc _ _ _

/-- Kernel postcomposition commutes with `ε ↦ rε`, for every scalar. -/
theorem productDualNumberKernelMap_scale
    (ρ : MatrixRepresentation (groupScheme n R) m) (r : S) (x : PointKernel n R S) :
    ρ.productDualNumberKernelMap S (pointKernelScale r x) =
      DualNumber.pointKernelScale r (ρ.productDualNumberKernelMap S x) := by
  apply Subtype.ext
  exact Category.assoc _ _ _

/-- The linear differential of an actual representation of a finite product scheme. -/
def productDifferential (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] :
    (∀ i, Matrix (n i) (n i) S) →ₗ[S] Matrix m m S where
  toFun X := DualNumber.pointKernelEquiv.symm
    (ρ.productDualNumberKernelMap S (pointKernelEquiv X))
  map_add' X Y := by
    rw [pointKernelEquiv_add, map_mul]
    exact congrArg Multiplicative.toAdd
      ((DualNumber.pointKernelMulEquiv (n := m) (R := R) (S := S)).symm.map_mul _ _)
  map_smul' r X := by
    change DualNumber.pointKernelEquiv.symm
      (ρ.productDualNumberKernelMap S (pointKernelEquiv (r • X))) = _
    rw [← pointKernelEquiv_scale, productDualNumberKernelMap_scale,
      DualNumber.pointKernelEquiv_symm_scale]
    rfl

@[simp] theorem productDifferential_apply (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : ∀ i, Matrix (n i) (n i) S) :
    ρ.productDifferential S X =
      DualNumber.pointKernelEquiv.symm
        (ρ.productDualNumberKernelMap S (pointKernelEquiv X)) := rfl

/-- The recovered matrix gives exactly the actual image kernel point. -/
theorem productDifferential_kernel (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : ∀ i, Matrix (n i) (n i) S) :
    DualNumber.pointKernelEquiv (ρ.productDifferential S X) =
      ρ.productDualNumberKernelMap S (pointKernelEquiv X) :=
  Equiv.apply_symm_apply _ _

/-- The first-order identity holds as an equality of actual scheme points. -/
theorem productDifferential_pointUnit (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : ∀ i, Matrix (n i) (n i) S) :
    DualNumber.pointUnit (ρ.productDifferential S X) = pointUnit X ≫ ρ.hom.hom :=
  congrArg Subtype.val (ρ.productDifferential_kernel X)

/-- In affine coordinates, `ρ((I + εX_i)_i) = I + ε dρ(X)`. -/
theorem productDifferential_affineMatrix (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : ∀ i, Matrix (n i) (n i) S) :
    ρ.affineMatrix (CommAlgCat.of R (DualNumber S)) (pointUnit X) =
      DualNumber.matrixUnit (ρ.productDifferential S X) := by
  rw [affineMatrix_apply, ← productDifferential_pointUnit, DualNumber.pointUnit_matrix]

/-- Epsilon coefficients of the actual image recover the product differential. -/
theorem productDifferential_coefficients (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : ∀ i, Matrix (n i) (n i) S) :
    ρ.productDifferential S X =
      DualNumber.coefficients
        (ρ.affineMatrix (CommAlgCat.of R (DualNumber S)) (pointUnit X)) := by
  rw [productDifferential_affineMatrix, DualNumber.coefficients_matrixUnit]

/-- The actual first-order equation characterizes each value of the differential. -/
theorem productDifferential_eq_iff (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : ∀ i, Matrix (n i) (n i) S) (Y : Matrix m m S) :
    ρ.productDifferential S X = Y ↔
      ρ.affineMatrix (CommAlgCat.of R (DualNumber S)) (pointUnit X) =
        DualNumber.matrixUnit Y := by
  rw [productDifferential_affineMatrix]
  constructor
  · exact congrArg DualNumber.matrixUnit
  · intro h
    simpa only [DualNumber.coefficients_matrixUnit] using congrArg DualNumber.coefficients h

/-- A linear map satisfying the actual first-order formula is the constructed map. -/
theorem productDifferential_unique (ρ : MatrixRepresentation (groupScheme n R) m)
    (D : (∀ i, Matrix (n i) (n i) S) →ₗ[S] Matrix m m S)
    (hD : ∀ X, ρ.affineMatrix (CommAlgCat.of R (DualNumber S)) (pointUnit X) =
      DualNumber.matrixUnit (D X)) :
    D = ρ.productDifferential S := by
  apply LinearMap.ext
  intro X
  exact ((ρ.productDifferential_eq_iff X (D X)).mpr (hD X)).symm

/-- Differentiation is natural under arbitrary maps of test algebras over the base. -/
theorem productDifferential_naturality (ρ : MatrixRepresentation (groupScheme n R) m)
    (f : S →ₐ[R] T) (X : ∀ i, Matrix (n i) (n i) S) :
    ρ.productDifferential T (fun i => (X i).map f) =
      (ρ.productDifferential S X).map f := by
  simp only [productDifferential_apply]
  rw [← pointKernelEquiv_naturality, productDualNumberKernelMap_naturality,
    DualNumber.pointKernelEquiv_symm_naturality]

/-- The actual categorical projection differentiates to coordinate evaluation. -/
@[simp] theorem productDifferential_proj (i : I) (X : ∀ i, Matrix (n i) (n i) S) :
    productDifferential
      (CategoryTheory.Limits.Pi.π (fun i => GeneralLinear.groupScheme (n i) R) i) S X = X i := by
  apply (DualNumber.pointKernelEquiv (n := n i) (R := R) (S := S)).injective
  rw [productDifferential_kernel]
  apply Subtype.ext
  change pointUnit X ≫ proj n R i = DualNumber.pointUnit (X i)
  exact pointUnit_proj X i

/-- The trivial representation has zero product differential. -/
@[simp] theorem productDifferential_trivial (X : ∀ i, Matrix (n i) (n i) S) :
    (trivial (groupScheme n R) m).productDifferential S X = 0 := by
  rw [productDifferential_coefficients, trivial_affineMatrix]
  have h : (1 : GL m (DualNumber S)) = DualNumber.matrixUnit (0 : Matrix m m S) :=
    DualNumber.matrixUnit_zero.symm
  rw [h, DualNumber.coefficients_matrixUnit]

/-- The chain rule follows from composition of the actual scheme-point maps. -/
theorem productDifferential_comp (ρ : MatrixRepresentation (groupScheme n R) m)
    (σ : MatrixRepresentation (GeneralLinear.groupScheme m R) k)
    (X : ∀ i, Matrix (n i) (n i) S) :
    productDifferential (ρ ≫ σ) S X = σ.differential S (ρ.productDifferential S X) := by
  apply (DualNumber.pointKernelEquiv (n := k) (R := R) (S := S)).injective
  rw [productDifferential_kernel, differential_kernel, productDifferential_kernel]
  apply Subtype.ext
  change pointUnit X ≫ (ρ.hom.hom ≫ σ.hom.hom) =
    (pointUnit X ≫ ρ.hom.hom) ≫ σ.hom.hom
  exact (Category.assoc _ _ _).symm

/-- The chain rule as equality of the constructed linear maps. -/
theorem productDifferential_comp_linearMap (ρ : MatrixRepresentation (groupScheme n R) m)
    (σ : MatrixRepresentation (GeneralLinear.groupScheme m R) k) :
    productDifferential (ρ ≫ σ) S =
      (σ.differential S).comp (ρ.productDifferential S) := by
  ext X i j
  exact congrArg (fun A : Matrix k k S => A i j) (productDifferential_comp ρ σ X)

/-- The corresponding linear family of coordinate endomorphisms. -/
def productDifferentialAction (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] :
    (∀ i, Matrix (n i) (n i) S) →ₗ[S] Module.End S (m → S) :=
  (Matrix.toLin' : Matrix m m S ≃ₗ[S] Module.End S (m → S)).toLinearMap.comp
    (ρ.productDifferential S)

@[simp] theorem productDifferentialAction_apply
    (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : ∀ i, Matrix (n i) (n i) S) (v : m → S) :
    ρ.productDifferentialAction S X v = ρ.productDifferential S X *ᵥ v := rfl

/-- Entrywise coefficient change intertwines the full coordinate endomorphism families. -/
theorem productDifferentialAction_naturality
    (ρ : MatrixRepresentation (groupScheme n R) m)
    (f : S →ₐ[R] T) (X : ∀ i, Matrix (n i) (n i) S) (v : m → S) :
    ρ.productDifferentialAction T (fun i => (X i).map f) (fun a => f (v a)) =
      fun a => f (ρ.productDifferentialAction S X v a) := by
  rw [productDifferentialAction_apply, productDifferential_naturality,
    productDifferentialAction_apply]
  funext a
  exact (f.toRingHom.map_mulVec _ _ a).symm

end Langlands.GroupScheme.MatrixRepresentation
