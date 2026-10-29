import Langlands.GroupScheme.Products
import Langlands.GroupScheme.GeneralLinearDualNumber

/-! # Dual-number identity kernels of finite products of general linear group schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinearProductDualNumber

open GeneralLinear

variable {I : Type u} [Finite I]

section Points

variable (n : I → Type) [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
variable (R : CommRingCat.{u})

/-- The actual categorical finite product of the general linear group schemes `GL_{n i}`. -/
abbrev groupScheme : GroupScheme (Spec R) :=
  GroupScheme.pi fun i => GeneralLinear.groupScheme (n i) R

/-- The underlying scheme map of the categorical projection onto the `i`th factor. -/
abbrev proj (i : I) : (groupScheme n R).X ⟶ (GeneralLinear.groupScheme (n i) R).X :=
  (Pi.π (fun i => GeneralLinear.groupScheme (n i) R) i).hom.hom

/-- Actual points of the product over the affine test scheme of an `R`-algebra `S`. -/
abbrev AffinePoints (S : Type u) [CommRing S] [Algebra R S] :=
  (algSpec R).obj (op (CommAlgCat.of R S)) ⟶ (groupScheme n R).X

variable {n R}
variable {S T U : Type u} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
  [CommRing U] [Algebra R U]

/-- Coefficient maps act on actual product points by precomposing with their spectrum maps. -/
def affineMap (f : S →ₐ[R] T) : AffinePoints n R S →* AffinePoints n R T :=
  ((groupScheme n R).points.map ((algSpec R).map (CommAlgCat.ofHom f).op).op).hom

@[simp] theorem affineMap_apply (f : S →ₐ[R] T) (x : AffinePoints n R S) :
    affineMap f x = (algSpec R).map (CommAlgCat.ofHom f).op ≫ x := rfl

/-- Precomposition with spectrum maps is functorial in the coefficient algebra. -/
theorem affineMap_comp (f : S →ₐ[R] T) (g : T →ₐ[R] U) (x : AffinePoints n R S) :
    affineMap g (affineMap f x) = affineMap (g.comp f) x := by
  rw [affineMap_apply, affineMap_apply, affineMap_apply, ← Category.assoc, ← Functor.map_comp]
  rfl

@[simp] theorem affineMap_id (x : AffinePoints n R S) :
    affineMap (AlgHom.id R S) x = x := by
  rw [affineMap_apply]
  change (algSpec R).map (𝟙 (op (CommAlgCat.of R S))) ≫ x = x
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

variable (S) in
/-- The published finite-product point equivalence on the affine test scheme of `S`. -/
def affinePointsPiEquiv : AffinePoints n R S ≃* ∀ i, DualNumber.AffinePoints (n i) R S :=
  piPointsEquiv (fun i => GeneralLinear.groupScheme (n i) R) _

@[simp] theorem affinePointsPiEquiv_apply (x : AffinePoints n R S) (i : I) :
    affinePointsPiEquiv S x i = x ≫ proj n R i := rfl

@[simp] theorem affinePointsPiEquiv_symm_proj (x : ∀ i, DualNumber.AffinePoints (n i) R S)
    (i : I) : (affinePointsPiEquiv S).symm x ≫ proj n R i = x i :=
  piPointsEquiv_symm_π _ _ x i

/-- Product coordinates turn coefficient change into coefficient change of every factor. -/
theorem affinePointsPiEquiv_affineMap (f : S →ₐ[R] T) (x : AffinePoints n R S) (i : I) :
    affinePointsPiEquiv T (affineMap f x) i =
      DualNumber.affineMap f (affinePointsPiEquiv S x i) :=
  congrFun (piPointsEquiv_naturality (fun i => GeneralLinear.groupScheme (n i) R)
    ((algSpec R).map (CommAlgCat.ofHom f).op) x) i

/-- Reduction modulo epsilon of actual product points, by the spectrum of the projection. -/
def pointReduction : AffinePoints n R (DualNumber S) →* AffinePoints n R S :=
  affineMap (TrivSqZeroExt.fstHom R S S)

theorem pointReduction_apply (x : AffinePoints n R (DualNumber S)) :
    pointReduction x = (algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R S S)).op ≫ x :=
  rfl

variable (n R S) in
/-- The identity kernel inside the actual product-scheme point group. -/
abbrev PointKernel := (pointReduction (n := n) (R := R) (S := S)).ker

/-- Product reduction is the published single-factor reduction in every factor. -/
theorem affinePointsPiEquiv_pointReduction (x : AffinePoints n R (DualNumber S)) (i : I) :
    affinePointsPiEquiv S (pointReduction x) i =
      DualNumber.pointReduction (affinePointsPiEquiv (DualNumber S) x i) :=
  affinePointsPiEquiv_affineMap _ x i

/-- A product point lies in the kernel exactly when every factor lies in its kernel. -/
theorem mem_pointKernel_iff (x : AffinePoints n R (DualNumber S)) :
    x ∈ PointKernel n R S ↔
      ∀ i, affinePointsPiEquiv (DualNumber S) x i ∈ DualNumber.PointKernel (n i) R S := by
  rw [MonoidHom.mem_ker, ← (affinePointsPiEquiv (n := n) (R := R) S).injective.eq_iff,
    map_one, funext_iff]
  simp only [affinePointsPiEquiv_pointReduction, Pi.one_apply, MonoidHom.mem_ker]

/-- `piPointsEquiv` identifies the actual product kernel with the family of factor kernels. -/
def pointKernelPiEquiv : PointKernel n R S ≃* ∀ i, DualNumber.PointKernel (n i) R S where
  toFun x i := ⟨affinePointsPiEquiv (DualNumber S) x.val i,
    (mem_pointKernel_iff x.val).mp x.property i⟩
  invFun y := ⟨(affinePointsPiEquiv (DualNumber S)).symm fun i => (y i).val, by
    rw [mem_pointKernel_iff]
    intro i
    rw [MulEquiv.apply_symm_apply]
    exact (y i).property⟩
  left_inv x := Subtype.ext ((affinePointsPiEquiv (DualNumber S)).symm_apply_apply x.val)
  right_inv y := by
    funext i
    apply Subtype.ext
    exact congrFun ((affinePointsPiEquiv (DualNumber S)).apply_symm_apply fun i => (y i).val) i
  map_mul' x y := by
    funext i
    apply Subtype.ext
    exact congrFun (map_mul (affinePointsPiEquiv (DualNumber S)) x.val y.val) i

@[simp] theorem pointKernelPiEquiv_apply_val (x : PointKernel n R S) (i : I) :
    (pointKernelPiEquiv x i).val = x.val ≫ proj n R i := rfl

@[simp] theorem pointKernelPiEquiv_symm_apply_val
    (y : ∀ i, DualNumber.PointKernel (n i) R S) :
    (pointKernelPiEquiv.symm y).val =
      (affinePointsPiEquiv (DualNumber S)).symm fun i => (y i).val := rfl

end Points

section Coordinates

variable {n : I → Type} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
variable {R : CommRingCat.{u}}
variable {S T U : Type u} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
  [CommRing U] [Algebra R U]

/-- The actual product point whose `i`th factor is the published point `I + εX_i`. -/
def pointUnit (X : ∀ i, Matrix (n i) (n i) S) : AffinePoints n R (DualNumber S) :=
  (affinePointsPiEquiv (DualNumber S)).symm fun i => DualNumber.pointUnit (X i)

/-- The `i`th scheme projection of the product point is the actual factor point. -/
@[simp] theorem pointUnit_proj (X : ∀ i, Matrix (n i) (n i) S) (i : I) :
    pointUnit (R := R) X ≫ proj n R i = DualNumber.pointUnit (X i) :=
  affinePointsPiEquiv_symm_proj _ i

/-- In published affine coordinates, the `i`th factor of the point is `I + εX_i`. -/
theorem pointUnit_matrix (X : ∀ i, Matrix (n i) (n i) S) (i : I) :
    affinePointsEquiv (n i) R (CommAlgCat.of R (DualNumber S)) (pointUnit X ≫ proj n R i) =
      DualNumber.matrixUnit (X i) := by
  rw [pointUnit_proj, DualNumber.pointUnit_matrix]

/-- Families of matrices are the actual identity kernel of the finite product. -/
def pointKernelEquiv : (∀ i, Matrix (n i) (n i) S) ≃ PointKernel n R S :=
  (Equiv.piCongrRight fun i => DualNumber.pointKernelEquiv (n := n i) (R := R) (S := S)).trans
    pointKernelPiEquiv.symm.toEquiv

@[simp] theorem pointKernelEquiv_val (X : ∀ i, Matrix (n i) (n i) S) :
    (pointKernelEquiv (R := R) X).val = pointUnit X := rfl

/-- The `i`th scheme projection of the kernel point at `X` is the actual `pointUnit (X i)`. -/
theorem pointKernelEquiv_proj (X : ∀ i, Matrix (n i) (n i) S) (i : I) :
    (pointKernelEquiv (R := R) X).val ≫ proj n R i = DualNumber.pointUnit (X i) :=
  pointUnit_proj X i

/-- Under the kernel comparison, the point at `X` is the family of published kernel points. -/
@[simp] theorem pointKernelPiEquiv_pointKernelEquiv (X : ∀ i, Matrix (n i) (n i) S) (i : I) :
    pointKernelPiEquiv (pointKernelEquiv (R := R) X) i = DualNumber.pointKernelEquiv (X i) :=
  Subtype.ext (pointUnit_proj X i)

/-- Every component is recovered by the published single-factor inverse. -/
theorem pointKernelEquiv_symm_apply (x : PointKernel n R S) (i : I) :
    pointKernelEquiv.symm x i = DualNumber.pointKernelEquiv.symm (pointKernelPiEquiv x i) :=
  rfl

/-- Every component is the matrix of epsilon coefficients of the corresponding factor. -/
theorem pointKernelEquiv_symm_coefficients (x : PointKernel n R S) (i : I) :
    pointKernelEquiv.symm x i =
      DualNumber.coefficients
        (affinePointsEquiv (n i) R (CommAlgCat.of R (DualNumber S)) (x.val ≫ proj n R i)) :=
  rfl

/-- Addition of matrix families is the actual group law of the product scheme. -/
theorem pointKernelEquiv_add (X Y : ∀ i, Matrix (n i) (n i) S) :
    pointKernelEquiv (R := R) (X + Y) = pointKernelEquiv X * pointKernelEquiv Y := by
  apply pointKernelPiEquiv.injective
  rw [map_mul]
  funext i
  rw [Pi.mul_apply, pointKernelPiEquiv_pointKernelEquiv, pointKernelPiEquiv_pointKernelEquiv,
    pointKernelPiEquiv_pointKernelEquiv]
  exact DualNumber.pointKernelEquiv_add (X i) (Y i)

/-- The additive group of matrix families is isomorphic to the actual product kernel. -/
def pointKernelMulEquiv : Multiplicative (∀ i, Matrix (n i) (n i) S) ≃* PointKernel n R S where
  toEquiv := Multiplicative.toAdd.trans pointKernelEquiv
  map_mul' X Y := pointKernelEquiv_add X.toAdd Y.toAdd

@[simp] theorem pointKernelMulEquiv_apply (X : Multiplicative (∀ i, Matrix (n i) (n i) S)) :
    pointKernelMulEquiv (R := R) X = pointKernelEquiv X.toAdd := rfl

@[simp] theorem pointKernelMulEquiv_symm_apply (x : PointKernel n R S) :
    pointKernelMulEquiv.symm x = Multiplicative.ofAdd (pointKernelEquiv.symm x) := rfl

@[simp] theorem pointKernelEquiv_zero :
    pointKernelEquiv (R := R) (0 : ∀ i, Matrix (n i) (n i) S) = 1 :=
  map_one (pointKernelMulEquiv (n := n) (R := R) (S := S))

/-- Negation of matrix families is inversion in the actual product kernel. -/
theorem pointKernelEquiv_neg (X : ∀ i, Matrix (n i) (n i) S) :
    pointKernelEquiv (R := R) (-X) = (pointKernelEquiv X)⁻¹ :=
  map_inv (pointKernelMulEquiv (n := n) (R := R) (S := S)) (Multiplicative.ofAdd X)

/-- Coefficient recovery turns the actual group law into addition. -/
theorem pointKernelEquiv_symm_mul (x y : PointKernel n R S) :
    pointKernelEquiv.symm (x * y) = pointKernelEquiv.symm x + pointKernelEquiv.symm y := by
  obtain ⟨X, rfl⟩ := (pointKernelEquiv (n := n) (R := R) (S := S)).surjective x
  obtain ⟨Y, rfl⟩ := (pointKernelEquiv (n := n) (R := R) (S := S)).surjective y
  rw [← pointKernelEquiv_add, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

@[simp] theorem pointKernelEquiv_symm_one :
    pointKernelEquiv.symm (1 : PointKernel n R S) = 0 := by
  rw [← pointKernelEquiv_zero, Equiv.symm_apply_apply]

theorem pointKernelEquiv_symm_inv (x : PointKernel n R S) :
    pointKernelEquiv.symm x⁻¹ = -pointKernelEquiv.symm x := by
  obtain ⟨X, rfl⟩ := (pointKernelEquiv (n := n) (R := R) (S := S)).surjective x
  rw [← pointKernelEquiv_neg, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The actual product law is addition of coefficient families at the identity. -/
theorem pointUnit_add (X Y : ∀ i, Matrix (n i) (n i) S) :
    pointUnit (R := R) (X + Y) = pointUnit X * pointUnit Y :=
  congrArg Subtype.val (pointKernelEquiv_add X Y)

@[simp] theorem pointReduction_pointUnit (X : ∀ i, Matrix (n i) (n i) S) :
    pointReduction (pointUnit (R := R) X) = 1 :=
  (pointKernelEquiv (R := R) X).property

/-- Reduction commutes with coefficient change of the dual-number test algebra. -/
theorem pointReduction_affineMap (f : S →ₐ[R] T) (x : AffinePoints n R (DualNumber S)) :
    pointReduction (affineMap (DualNumber.coefficientAlgMap f) x) =
      affineMap f (pointReduction x) := by
  have h : (TrivSqZeroExt.fstHom R T T).comp (DualNumber.coefficientAlgMap f) =
      f.comp (TrivSqZeroExt.fstHom R S S) :=
    AlgHom.ext fun _ => rfl
  simp only [pointReduction, affineMap_comp, h]

/-- Reduction is unchanged by the actual test-algebra endomorphism `ε ↦ rε`. -/
theorem pointReduction_affineMap_scale (r : S) (x : AffinePoints n R (DualNumber S)) :
    pointReduction (affineMap (DualNumber.epsilonScaleAlg (R := R) r) x) =
      pointReduction x := by
  have h : (TrivSqZeroExt.fstHom R S S).comp (DualNumber.epsilonScaleAlg (R := R) r) =
      TrivSqZeroExt.fstHom R S S :=
    AlgHom.ext fun z => DualNumber.epsilonScale_fst r z
  simp only [pointReduction, affineMap_comp, h]

/-- Coefficient change on actual product points restricts to their identity kernels. -/
def pointKernelMap (f : S →ₐ[R] T) : PointKernel n R S →* PointKernel n R T where
  toFun x := ⟨affineMap (DualNumber.coefficientAlgMap f) x.val, by
    rw [MonoidHom.mem_ker, pointReduction_affineMap, MonoidHom.mem_ker.mp x.property,
      map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

@[simp] theorem pointKernelMap_val (f : S →ₐ[R] T) (x : PointKernel n R S) :
    (pointKernelMap f x).val = affineMap (DualNumber.coefficientAlgMap f) x.val := rfl

/-- Epsilon scaling restricts to the actual product kernel, including for nonunit scalars. -/
def pointKernelScale (r : S) : PointKernel n R S →* PointKernel n R S where
  toFun x := ⟨affineMap (DualNumber.epsilonScaleAlg (R := R) r) x.val, by
    rw [MonoidHom.mem_ker, pointReduction_affineMap_scale]
    exact x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

@[simp] theorem pointKernelScale_val (r : S) (x : PointKernel n R S) :
    (pointKernelScale r x).val = affineMap (DualNumber.epsilonScaleAlg (R := R) r) x.val := rfl

/-- Coefficient change is the published single-factor coefficient change in every factor. -/
theorem pointKernelPiEquiv_pointKernelMap (f : S →ₐ[R] T) (x : PointKernel n R S) (i : I) :
    pointKernelPiEquiv (pointKernelMap f x) i =
      DualNumber.pointKernelMap f (pointKernelPiEquiv x i) :=
  Subtype.ext (affinePointsPiEquiv_affineMap _ x.val i)

/-- Epsilon scaling is the published single-factor epsilon scaling in every factor. -/
theorem pointKernelPiEquiv_pointKernelScale (r : S) (x : PointKernel n R S) (i : I) :
    pointKernelPiEquiv (pointKernelScale r x) i =
      DualNumber.pointKernelScale r (pointKernelPiEquiv x i) :=
  Subtype.ext (affinePointsPiEquiv_affineMap _ x.val i)

/-- Coefficient change on kernels is functorial in the coefficient algebra. -/
theorem pointKernelMap_comp (f : S →ₐ[R] T) (g : T →ₐ[R] U) (x : PointKernel n R S) :
    pointKernelMap g (pointKernelMap f x) = pointKernelMap (g.comp f) x := by
  apply Subtype.ext
  have h : (DualNumber.coefficientAlgMap g).comp (DualNumber.coefficientAlgMap f) =
      DualNumber.coefficientAlgMap (R := R) (g.comp f) :=
    AlgHom.ext fun _ => rfl
  rw [pointKernelMap_val, pointKernelMap_val, pointKernelMap_val, affineMap_comp, h]

@[simp] theorem pointKernelMap_id (x : PointKernel n R S) :
    pointKernelMap (AlgHom.id R S) x = x := by
  apply Subtype.ext
  have h : DualNumber.coefficientAlgMap (R := R) (AlgHom.id R S) = AlgHom.id R (DualNumber S) :=
    AlgHom.ext fun _ => rfl
  rw [pointKernelMap_val, h, affineMap_id]

/-- The product kernel coordinates are natural: coefficient change is `Matrix.map f`
in every component. -/
theorem pointKernelEquiv_naturality (f : S →ₐ[R] T) (X : ∀ i, Matrix (n i) (n i) S) :
    pointKernelMap f (pointKernelEquiv X) = pointKernelEquiv fun i => (X i).map f := by
  apply pointKernelPiEquiv.injective
  funext i
  rw [pointKernelPiEquiv_pointKernelMap, pointKernelPiEquiv_pointKernelEquiv,
    pointKernelPiEquiv_pointKernelEquiv]
  exact DualNumber.pointKernelEquiv_naturality f (X i)

/-- Epsilon scaling by `r` is multiplication of every component by `r`. -/
theorem pointKernelEquiv_scale (r : S) (X : ∀ i, Matrix (n i) (n i) S) :
    pointKernelScale (R := R) r (pointKernelEquiv X) = pointKernelEquiv (r • X) := by
  apply pointKernelPiEquiv.injective
  funext i
  rw [pointKernelPiEquiv_pointKernelScale, pointKernelPiEquiv_pointKernelEquiv,
    pointKernelPiEquiv_pointKernelEquiv]
  exact DualNumber.pointKernelEquiv_scale r (X i)

/-- Coefficient recovery is natural for every element of the actual product kernel. -/
theorem pointKernelEquiv_symm_naturality (f : S →ₐ[R] T) (x : PointKernel n R S) :
    pointKernelEquiv.symm (pointKernelMap f x) = fun i => (pointKernelEquiv.symm x i).map f := by
  obtain ⟨X, rfl⟩ := (pointKernelEquiv (n := n) (R := R) (S := S)).surjective x
  rw [pointKernelEquiv_naturality, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Coefficient recovery respects epsilon scaling for every element of the actual kernel. -/
theorem pointKernelEquiv_symm_scale (r : S) (x : PointKernel n R S) :
    pointKernelEquiv.symm (pointKernelScale r x) = r • pointKernelEquiv.symm x := by
  obtain ⟨X, rfl⟩ := (pointKernelEquiv (n := n) (R := R) (S := S)).surjective x
  rw [pointKernelEquiv_scale, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- On actual product points, coefficient change sends `pointUnit X` to the point of the
componentwise mapped family. -/
theorem pointUnit_naturality (f : S →ₐ[R] T) (X : ∀ i, Matrix (n i) (n i) S) :
    affineMap (DualNumber.coefficientAlgMap f) (pointUnit X) =
      pointUnit (R := R) fun i => (X i).map f :=
  congrArg Subtype.val (pointKernelEquiv_naturality f X)

/-- On actual product points, epsilon scaling sends `pointUnit X` to `pointUnit (r • X)`. -/
theorem pointUnit_scale (r : S) (X : ∀ i, Matrix (n i) (n i) S) :
    affineMap (DualNumber.epsilonScaleAlg (R := R) r) (pointUnit X) =
      pointUnit (R := R) (r • X) :=
  congrArg Subtype.val (pointKernelEquiv_scale r X)

end Coordinates

end Langlands.GroupScheme.GeneralLinearProductDualNumber
