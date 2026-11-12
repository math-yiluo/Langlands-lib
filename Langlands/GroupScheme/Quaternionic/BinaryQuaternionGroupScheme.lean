import Langlands.GroupScheme.Quaternionic.BinaryQuaternionAction
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.CentralSimpleNormOne
import Langlands.GroupScheme.SpecialLinear
import Langlands.GroupScheme.Products
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Rational.LeviFactorization
import Mathlib.RingTheory.MatrixAlgebra

/-! # The actual binary quaternionic product morphism -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.Quaternionic.BinaryScheme

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)

/-- The actual product SL₂ × SL₁(D). -/
def groupScheme : GroupScheme (Spec (CommRingCat.of K)) :=
  SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K) ⊗ CentralSimpleUnits.normOne K D

/-- The actual coefficient algebra of a relative test scheme. -/
abbrev coefficients (T : Over (Spec (CommRingCat.of K))) :=
  ((algΓ (CommRingCat.of K)).obj T).unop

/-- Scalar extension commutes with binary matrices over every commutative coefficient ring. -/
def tensorMatrixEquiv (R : Type u) [CommRing R] [Algebra K R] :
    R ⊗[K] Matrix (Fin 2) (Fin 2) D ≃ₐ[K] Matrix (Fin 2) (Fin 2) (R ⊗[K] D) :=
  ((Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[K] R)
      (matrixEquivTensor (Fin 2) K D)).trans
    (Algebra.TensorProduct.assoc K K K R D (Matrix (Fin 2) (Fin 2) K)).symm).trans
      (matrixEquivTensor (Fin 2) K (R ⊗[K] D)).symm

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
@[simp] theorem tensorMatrixEquiv_tmul (R : Type u) [CommRing R] [Algebra K R]
    (r : R) (M : Matrix (Fin 2) (Fin 2) D) :
    tensorMatrixEquiv R (r ⊗ₜ[K] M) = fun i j => r ⊗ₜ[K] M i j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorMatrixEquiv, matrixEquivTensor_apply, TensorProduct.tmul_add,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.single]

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
/-- The matrix comparison commutes with every coefficient-algebra map. -/
theorem tensorMatrixEquiv_naturality {R S : Type u} [CommRing R] [Algebra K R]
    [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (x : R ⊗[K] Matrix (Fin 2) (Fin 2) D) :
    tensorMatrixEquiv S (Algebra.TensorProduct.map f (AlgHom.id K _) x) =
      (tensorMatrixEquiv R x).map (Algebra.TensorProduct.map f (AlgHom.id K D)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [_root_.map_add, hx, hy]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, _root_.map_add]
  | tmul r M => ext i j; simp

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
/-- The actual tensor matrix comparison intertwines the two adjoint constructions. -/
theorem tensorMatrixEquiv_adjoint (R : Type u) [CommRing R] [Algebra K R]
    (x : R ⊗[K] Matrix (Fin 2) (Fin 2) D) :
    tensorMatrixEquiv R ((σ.matrix (Fin 2)).baseChange R x) =
      (σ.baseChange R).matrix (Fin 2) (tensorMatrixEquiv R x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [_root_.map_add, hx, hy]
  | tmul r M => ext i j; simp

/-- Test points of the actual product are its concrete two factors. -/
def pointsEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (groupScheme (K := K) (D := D)).X) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (coefficients T) ×
        Langlands.CentralSimple.reducedNormOne K D (coefficients T) :=
  (productPointsEquiv _ _ T).trans
    ((SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of K) T).prodCongr
      (CentralSimpleUnits.normOnePointsEquiv K D T))

/-- Test points of the actual algebra-unit group as binary tensor matrices. -/
def matrixPointsEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (FiniteAlgebraUnits.groupScheme
      (Module.finBasis K (Matrix (Fin 2) (Fin 2) D))).X) ≃*
        (Matrix (Fin 2) (Fin 2) (coefficients T ⊗[K] D))ˣ :=
  (FiniteAlgebraUnits.pointsEquiv _ T).trans
    (Units.mapEquiv (tensorMatrixEquiv (coefficients T)).toMulEquiv)

/-- The actual product point determines the concrete tensor matrix. -/
def pointMatrix (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (groupScheme (K := K) (D := D)).X) →*
      (Matrix (Fin 2) (Fin 2) (coefficients T ⊗[K] D))ˣ :=
  (BinaryAction.normOneAction σ hdim hsym (coefficients T)).comp (pointsEquiv T).toMonoidHom

omit [Algebra.IsCentral K D] in
private theorem tensorAlternatingUnit_naturality {R S : Type u} [CommRing R] [Algebra K R]
    [CommRing S] [Algebra K S] (f : R →ₐ[K] S) :
    Units.map (Algebra.TensorProduct.map f (AlgHom.id K D)).toMonoidHom
      (BinaryAction.tensorAlternatingUnit σ hdim hsym R) =
        BinaryAction.tensorAlternatingUnit σ hdim hsym S := by
  apply Units.ext
  simp

/-- The tensor matrix of a product point respects every relative test restriction. -/
theorem pointMatrix_naturality {T T' : Over (Spec (CommRingCat.of K))}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme (K := K) (D := D)).X) :
    (pointMatrix σ hdim hsym T' (a ≫ x) : Matrix (Fin 2) (Fin 2) (coefficients T' ⊗[K] D)) =
      (pointMatrix σ hdim hsym T x : Matrix (Fin 2) (Fin 2) (coefficients T ⊗[K] D)).map
        (Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map a).unop.hom
          (AlgHom.id K D)) := by
  let f := ((algΓ (CommRingCat.of K)).map a).unop.hom
  change (BinaryAction.action (BinaryAction.tensorAlternatingUnit σ hdim hsym (coefficients T'))
      ((pointsEquiv T' (a ≫ x)).1, (pointsEquiv T' (a ≫ x)).2.val) :
        Matrix (Fin 2) (Fin 2) (coefficients T' ⊗[K] D)) = _
  have h1 : (pointsEquiv T' (a ≫ x)).1 =
      Matrix.SpecialLinearGroup.map f.toRingHom (pointsEquiv T x).1 := by
    change SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of K) T'
      ((a ≫ x) ≫ fst _ _) = _
    rw [Category.assoc, SpecialLinear.pointsEquiv_naturality]
    rfl
  have h2 : (pointsEquiv T' (a ≫ x)).2.val =
      Units.map (Algebra.TensorProduct.map f (AlgHom.id K D)).toMonoidHom
        (pointsEquiv T x).2.val := by
    change FiniteAlgebraUnits.pointsEquiv (Module.finBasis K D) T'
      (((a ≫ x) ≫ snd _ _) ≫ (CentralSimpleUnits.normOneι K D).hom.hom) = _
    rw [Category.assoc, Category.assoc, FiniteAlgebraUnits.pointsEquiv_naturality]
    rfl
  rw [h1, h2, ← tensorAlternatingUnit_naturality σ hdim hsym f]
  exact BinaryAction.action_naturality f.toRingHom
    (Algebra.TensorProduct.map f (AlgHom.id K D)).toRingHom
    (fun r => by change f r ⊗ₜ[K] (1 : D) = _; rfl)
    _ _ _

/-- The homomorphism on all test points induced by the concrete action. -/
def unitPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (groupScheme (K := K) (D := D)).X) →*
      (T ⟶ (FiniteAlgebraUnits.groupScheme
        (Module.finBasis K (Matrix (Fin 2) (Fin 2) D))).X) :=
  (matrixPointsEquiv T).symm.toMonoidHom.comp (pointMatrix σ hdim hsym T)

/-- This family is natural on the actual schemes, not only on affine tests. -/
theorem unitPoints_naturality {T T' : Over (Spec (CommRingCat.of K))}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme (K := K) (D := D)).X) :
    unitPoints σ hdim hsym T' (a ≫ x) = a ≫ unitPoints σ hdim hsym T x := by
  apply (matrixPointsEquiv T').injective
  change matrixPointsEquiv T' ((matrixPointsEquiv T').symm _) = _
  rw [MulEquiv.apply_symm_apply]
  apply Units.ext
  have h := pointMatrix_naturality σ hdim hsym a x
  change (pointMatrix σ hdim hsym T' (a ≫ x) :
    Matrix (Fin 2) (Fin 2) (coefficients T' ⊗[K] D)) = _
  change _ = tensorMatrixEquiv (coefficients T')
    (FiniteAlgebraUnits.pointsEquiv _ T' (a ≫ unitPoints σ hdim hsym T x) :
      coefficients T' ⊗[K] Matrix (Fin 2) (Fin 2) D)
  rw [FiniteAlgebraUnits.pointsEquiv_naturality]
  change _ = tensorMatrixEquiv (coefficients T')
    (Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map a).unop.hom
      (AlgHom.id K (Matrix (Fin 2) (Fin 2) D))
        (FiniteAlgebraUnits.pointsEquiv _ T (unitPoints σ hdim hsym T x) :
          coefficients T ⊗[K] Matrix (Fin 2) (Fin 2) D))
  rw [tensorMatrixEquiv_naturality]
  have hu := congrArg (fun z : (Matrix (Fin 2) (Fin 2) (coefficients T ⊗[K] D))ˣ =>
      (z : Matrix (Fin 2) (Fin 2) (coefficients T ⊗[K] D)))
    ((matrixPointsEquiv T).apply_symm_apply (pointMatrix σ hdim hsym T x))
  change tensorMatrixEquiv (coefficients T)
    (FiniteAlgebraUnits.pointsEquiv _ T (unitPoints σ hdim hsym T x) :
      coefficients T ⊗[K] Matrix (Fin 2) (Fin 2) D) = _ at hu
  rw [hu]
  exact h

/-- The actual homomorphism of group schemes defined by the binary quaternion action. -/
def unitHom : groupScheme (K := K) (D := D) ⟶
    FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix (Fin 2) (Fin 2) D)) :=
  homOfPoints (unitPoints σ hdim hsym) (unitPoints_naturality σ hdim hsym)

/-- On every relative test, the actual morphism recovers the prescribed tensor matrix. -/
@[simp] theorem unitHom_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (groupScheme (K := K) (D := D)).X) :
    matrixPointsEquiv T (x ≫ (unitHom σ hdim hsym).hom.hom) = pointMatrix σ hdim hsym T x := by
  rw [unitHom, comp_homOfPoints]
  exact (matrixPointsEquiv T).apply_symm_apply _

/-- The full kernel equation of the actual group-scheme morphism on every test scheme. -/
theorem unitHom_kernel (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (groupScheme (K := K) (D := D)).X) :
    x ≫ (unitHom σ hdim hsym).hom.hom = 1 ↔ ∃ r : coefficients T, r * r = 1 ∧
      ((pointsEquiv T x).1 : Matrix (Fin 2) (Fin 2) (coefficients T)) = Matrix.scalar (Fin 2) r ∧
      ((pointsEquiv T x).2.val : coefficients T ⊗[K] D) =
        algebraMap (coefficients T) (coefficients T ⊗[K] D) r := by
  rw [← (matrixPointsEquiv T).injective.eq_iff, unitHom_points, _root_.map_one]
  exact BinaryAction.normOneAction_kernel σ hdim hsym (coefficients T) _ _

/-- The full kernel of the actual product morphism is central, including its non-smooth part. -/
theorem unitHom_kernel_isCentral : IsCentral (kernelι (unitHom σ hdim hsym)) := by
  apply (isCentral_kernelι_iff _).mpr
  intro T x hx T' a y
  have hx' : (a ≫ x) ≫ (unitHom σ hdim hsym).hom.hom = 1 := by
    rw [Category.assoc, hx, MonObj.comp_one]
  obtain ⟨r, _, hg, hb⟩ := (unitHom_kernel σ hdim hsym T' (a ≫ x)).mp hx'
  change (a ≫ x) * y = y * (a ≫ x)
  apply (pointsEquiv T').injective
  rw [_root_.map_mul, _root_.map_mul]
  apply Prod.ext
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (((pointsEquiv T' (a ≫ x)).1 : Matrix (Fin 2) (Fin 2) (coefficients T')) *
      ((pointsEquiv T' y).1 : Matrix (Fin 2) (Fin 2) (coefficients T'))) i j =
        (((pointsEquiv T' y).1 : Matrix (Fin 2) (Fin 2) (coefficients T')) *
          ((pointsEquiv T' (a ≫ x)).1 : Matrix (Fin 2) (Fin 2) (coefficients T'))) i j
    rw [hg]
    simp [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  · apply Subtype.ext
    apply Units.ext
    change ((pointsEquiv T' (a ≫ x)).2.val : coefficients T' ⊗[K] D) *
        ((pointsEquiv T' y).2.val : coefficients T' ⊗[K] D) =
      ((pointsEquiv T' y).2.val : coefficients T' ⊗[K] D) *
        ((pointsEquiv T' (a ≫ x)).2.val : coefficients T' ⊗[K] D)
    rw [hb]
    exact Algebra.commutes r _

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
private theorem tensorMatrix_mem_alternating_iff
    (R : Type u) [CommRing R] [Algebra K R]
    (x : R ⊗[K] Matrix (Fin 2) (Fin 2) D) :
    x ∈ ((σ.matrix (Fin 2)).baseChange R).alternatingSubspace ↔
      tensorMatrixEquiv R x ∈ ((σ.baseChange R).matrix (Fin 2)).alternatingSubspace := by
  constructor
  · intro h
    obtain ⟨w, rfl⟩ := ((σ.matrix (Fin 2)).baseChange R).mem_alternatingSubspace.mp h
    apply ((σ.baseChange R).matrix (Fin 2)).mem_alternatingSubspace.mpr
    exact ⟨tensorMatrixEquiv R w, by rw [_root_.map_sub, tensorMatrixEquiv_adjoint]⟩
  · intro h
    obtain ⟨w, hw⟩ := ((σ.baseChange R).matrix (Fin 2)).mem_alternatingSubspace.mp h
    apply ((σ.matrix (Fin 2)).baseChange R).mem_alternatingSubspace.mpr
    refine ⟨(tensorMatrixEquiv R).symm w, (tensorMatrixEquiv R).injective ?_⟩
    rw [_root_.map_sub, tensorMatrixEquiv_adjoint, AlgEquiv.apply_symm_apply]
    exact hw

/-- The actual hyperbolic quadratic class in the published matrix quotient. -/
def hyperbolicForm : σ.QuadraticForms (Fin 2) :=
  Submodule.Quotient.mk (BinaryAction.hyperbolicMatrix : Matrix (Fin 2) (Fin 2) D)

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
private theorem tensorMatrix_hyperbolic (R : Type u) [CommRing R] [Algebra K R] :
    tensorMatrixEquiv R (1 ⊗ₜ[K] (BinaryAction.hyperbolicMatrix : Matrix (Fin 2) (Fin 2) D)) =
      (BinaryAction.hyperbolicMatrix : Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [BinaryAction.hyperbolicMatrix, Algebra.TensorProduct.one_def]

variable [Infinite K]

/-- The actual product morphism has image in the actual hyperbolic isometry group. -/
theorem unitHom_range_le_isometry :
    SubgroupFunctor.range (unitHom σ hdim hsym) ≤
      SubgroupFunctor.range (σ.isometryGroupι (hyperbolicForm σ)) := by
  intro T z hz
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  rw [σ.mem_range_isometryGroupι_iff (hyperbolicForm σ)
    BinaryAction.hyperbolicMatrix rfl]
  change IsometryCut.defect (σ.matrix (Fin 2)) BinaryAction.hyperbolicMatrix _ ∈
    (σ.matrix (Fin 2)).alternatingSubspace.baseChange (coefficients T)
  rw [IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    tensorMatrix_mem_alternating_iff]
  have hu := congrArg
    (fun z : (Matrix (Fin 2) (Fin 2) (coefficients T ⊗[K] D))ˣ =>
      (z : Matrix (Fin 2) (Fin 2) (coefficients T ⊗[K] D)))
    (unitHom_points σ hdim hsym T x)
  change tensorMatrixEquiv (coefficients T)
    (FiniteAlgebraUnits.pointsEquiv _ T (x ≫ (unitHom σ hdim hsym).hom.hom) :
      coefficients T ⊗[K] Matrix (Fin 2) (Fin 2) D) = _ at hu
  rw [IsometryCut.defect, _root_.map_sub, _root_.map_mul, _root_.map_mul,
    tensorMatrixEquiv_adjoint, tensorMatrix_hyperbolic, hu]
  exact BinaryAction.normOneAction_preserves σ hdim hsym (coefficients T)
    (pointsEquiv T x).1 (pointsEquiv T x).2

omit [Infinite K] [Algebra.IsCentral K D] in
private theorem isometry_represents :
    (SubgroupFunctor.range (σ.isometryGroupι (hyperbolicForm σ))).IsRepresentedBy
      (σ.isometryGroupι (hyperbolicForm σ)) := by
  exact ⟨(σ.isClosedSubgroup_isometryGroupι (hyperbolicForm σ)).mono_overHom, rfl⟩

/-- The actual product action as a morphism into the published hyperbolic isometry group. -/
def isometryHom : groupScheme (K := K) (D := D) ⟶ σ.isometryGroup (hyperbolicForm σ) :=
  (isometry_represents σ).factorHom (unitHom σ hdim hsym)
    (unitHom_range_le_isometry σ hdim hsym)

/-- The isometry morphism has exactly the concrete underlying algebra-unit action. -/
@[reassoc] theorem isometryHom_comp :
    isometryHom σ hdim hsym ≫ σ.isometryGroupι (hyperbolicForm σ) = unitHom σ hdim hsym :=
  (isometry_represents σ).factorHom_comp _ _

/-- The actual isometry morphism recovers the binary matrix action on every relative test. -/
theorem isometryHom_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (groupScheme (K := K) (D := D)).X) :
    matrixPointsEquiv T
      ((x ≫ (isometryHom σ hdim hsym).hom.hom) ≫
        (σ.isometryGroupι (hyperbolicForm σ)).hom.hom) = pointMatrix σ hdim hsym T x := by
  rw [Category.assoc, ← Grp.comp_hom_hom, isometryHom_comp, unitHom_points]

private theorem isometryHom_eq_one_iff (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (groupScheme (K := K) (D := D)).X) :
    x ≫ (isometryHom σ hdim hsym).hom.hom = 1 ↔
      x ≫ (unitHom σ hdim hsym).hom.hom = 1 := by
  have he : (x ≫ (isometryHom σ hdim hsym).hom.hom) ≫
      (σ.isometryGroupι (hyperbolicForm σ)).hom.hom =
      x ≫ (unitHom σ hdim hsym).hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, isometryHom_comp]
  constructor
  · intro h
    rw [← he, h, MonObj.one_comp]
  · intro h
    apply (isometry_represents σ).1.right_cancellation
    rw [he, h, MonObj.one_comp]

/-- The exact all-test diagonal μ₂ kernel also holds for the actual isometry morphism. -/
theorem isometryHom_kernel (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (groupScheme (K := K) (D := D)).X) :
    x ≫ (isometryHom σ hdim hsym).hom.hom = 1 ↔ ∃ r : coefficients T, r * r = 1 ∧
      ((pointsEquiv T x).1 : Matrix (Fin 2) (Fin 2) (coefficients T)) = Matrix.scalar (Fin 2) r ∧
      ((pointsEquiv T x).2.val : coefficients T ⊗[K] D) =
        algebraMap (coefficients T) (coefficients T ⊗[K] D) r := by
  rw [isometryHom_eq_one_iff]
  exact unitHom_kernel σ hdim hsym T x

/-- Centrality of the actual hyperbolic isometry kernel, on all relative tests. -/
theorem isometryHom_kernel_isCentral : IsCentral (kernelι (isometryHom σ hdim hsym)) := by
  apply (isCentral_kernelι_iff _).mpr
  intro T x hx
  exact ((isCentral_kernelι_iff (unitHom σ hdim hsym)).mp
    (unitHom_kernel_isCentral σ hdim hsym)) T x
      ((isometryHom_eq_one_iff σ hdim hsym T x).mp hx)

end Langlands.GroupScheme.Quaternionic.BinaryScheme
