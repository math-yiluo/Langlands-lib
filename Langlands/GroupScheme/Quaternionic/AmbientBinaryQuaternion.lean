import Langlands.GroupScheme.Quaternionic.BinaryQuaternionKernel
import Langlands.GroupScheme.Quaternionic.HyperbolicGroupSchemeExtension

/-! # The binary quaternionic product in the ambient isometry group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic.AmbientBinaryScheme

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
/-- The two published binary tensor comparisons have the same actual matrix entries. -/
theorem tensorMatrix_compare (R : Type u) [CommRing R] [Algebra K R]
    (z : R ⊗[K] Matrix (Fin 2) (Fin 2) D) :
    TensorMatrix.equiv R (Fin 2) z = BinaryScheme.tensorMatrixEquiv R z := by
  induction z using TensorProduct.inductionOn with
  | tmul r M => simp only [TensorMatrix.equiv_tmul, BinaryScheme.tensorMatrixEquiv_tmul]
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

omit [Algebra.IsCentral K D] in
/-- The corresponding all-test unit coordinates agree as well. -/
theorem matrixPoints_compare (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme
      (Module.finBasis K (Matrix (Fin 2) (Fin 2) D))).X) :
    HyperbolicScheme.matrixPointsEquiv (Fin 2) T x = BinaryScheme.matrixPointsEquiv T x := by
  apply Units.ext
  exact tensorMatrix_compare (BinaryScheme.coefficients T) _

variable [Infinite K] {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {e f : n → D} (h : σ.IsHyperbolicPair q e f)

/-- The actual product action on a supplied hyperbolic plane in the ambient form. -/
def isometryHom : BinaryScheme.groupScheme (K := K) (D := D) ⟶ σ.isometryGroup q :=
  BinaryScheme.isometryHom σ hdim hsym ≫ HyperbolicScheme.isometryHom h

/-- On every relative scheme the ambient action is the prescribed split extension. -/
theorem isometryHom_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    HyperbolicScheme.matrixPointsEquiv n T
      ((x ≫ (isometryHom σ hdim hsym h).hom.hom) ≫ (σ.isometryGroupι q).hom.hom) =
      HyperbolicScheme.extendUnits h (BinaryScheme.coefficients T)
        (BinaryScheme.pointMatrix σ hdim hsym T x) := by
  rw [isometryHom, Grp.comp_hom_hom, ← Category.assoc,
    HyperbolicScheme.isometryHom_points, matrixPoints_compare, BinaryScheme.isometryHom_points]

/-- The ambient extension introduces no additional product-action kernel points. -/
theorem isometryHom_eq_one_iff (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    x ≫ (isometryHom σ hdim hsym h).hom.hom = 1 ↔
      x ≫ (BinaryScheme.isometryHom σ hdim hsym).hom.hom = 1 := by
  change (x ≫ (BinaryScheme.isometryHom σ hdim hsym).hom.hom) ≫
    (HyperbolicScheme.isometryHom h).hom.hom = 1 ↔ _
  constructor
  · intro hx
    apply HyperbolicScheme.isometryHom_points_injective h T
    simpa only [MonObj.one_comp] using hx
  · intro hx
    rw [hx, MonObj.one_comp]

/-- The full ambient kernel is diagonal scalar square roots of one on the original test. -/
theorem isometryHom_kernel (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    x ≫ (isometryHom σ hdim hsym h).hom.hom = 1 ↔
      ∃ r : BinaryScheme.coefficients T, r * r = 1 ∧
        ((BinaryScheme.pointsEquiv T x).1 :
          Matrix (Fin 2) (Fin 2) (BinaryScheme.coefficients T)) = Matrix.scalar (Fin 2) r ∧
        ((BinaryScheme.pointsEquiv T x).2.val : BinaryScheme.coefficients T ⊗[K] D) =
          algebraMap (BinaryScheme.coefficients T) (BinaryScheme.coefficients T ⊗[K] D) r := by
  rw [isometryHom_eq_one_iff, BinaryScheme.isometryHom_kernel]

/-- Centrality includes the entire possibly non-smooth kernel functor. -/
theorem isometryHom_kernel_isCentral :
    IsCentral (kernelι (isometryHom σ hdim hsym h)) := by
  apply (isCentral_kernelι_iff _).mpr
  intro T x hx
  exact ((isCentral_kernelι_iff (BinaryScheme.isometryHom σ hdim hsym)).mp
    (BinaryScheme.isometryHom_kernel_isCentral σ hdim hsym)) T x
      ((isometryHom_eq_one_iff σ hdim hsym h T x).mp hx)

/-- The original diagonal μ₂ represents exactly the ambient action kernel on all tests. -/
theorem diagonal_range :
    SubgroupFunctor.range (BinaryKernel.diagonal hdim) =
      SubgroupFunctor.range (kernelι (isometryHom σ hdim hsym h)) := by
  rw [BinaryKernel.diagonal_range_isometry σ hdim hsym]
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [mem_range_kernelι_iff, mem_range_kernelι_iff, isometryHom_eq_one_iff]

/-- The ambient product-action kernel is the full group scheme μ₂ in every characteristic. -/
def muTwoKernelIso :
    BinaryKernel.muTwo (K := K) ≅ kernel (isometryHom σ hdim hsym h) :=
  (show (SubgroupFunctor.range (BinaryKernel.diagonal hdim)).IsRepresentedBy
      (BinaryKernel.diagonal hdim) from ⟨inferInstance, rfl⟩).isoOfIsRepresentedBy
    ⟨inferInstance, (diagonal_range σ hdim hsym h).symm⟩

/-- The kernel isomorphism preserves the given diagonal inclusion into the product. -/
@[reassoc] theorem muTwoKernelIso_comp :
    (muTwoKernelIso σ hdim hsym h).hom ≫ kernelι (isometryHom σ hdim hsym h) =
      BinaryKernel.diagonal hdim :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- The full ambient product-action kernel is finite, including in characteristic two. -/
theorem kernel_isFinite : IsFinite (kernel (isometryHom σ hdim hsym h)).X.hom := by
  have : IsFinite (BinaryKernel.muTwo (K := K)).X.hom := by
    change IsFinite
      (Diagonalizable.groupScheme (CommRingCat.of K) BinaryKernel.TwoLattice.{u}).X.hom
    infer_instance
  let i := muTwoKernelIso σ hdim hsym h
  rw [← i.inv.hom.hom.w]
  infer_instance

end Langlands.GroupScheme.Quaternionic.AmbientBinaryScheme
