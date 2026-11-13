import Langlands.GroupScheme.Examples.HermitianMatrixTransport
import Langlands.GroupScheme.Examples.HermitianRootIsometryGroupScheme

/-! # General Hermitian matrix points on every test scheme -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianMatrix.SchemeModel

open SU3Root

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Idx : Type v} [Fintype Idx] [DecidableEq Idx]

/-- Scalar extension to the actual tensor coefficient algebra of a test scheme. -/
def tensorForm (H : Form (fieldInvolution k L) Idx)
    (T : Over (Spec (CommRingCat.of k))) :
    Form (SU3Root.SchemeModel.coefficientInvolution k L T) Idx :=
  H.map (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T))
    (HermitianRoot.SchemeModel.tensorInclusion_bar k L T)

@[simp] theorem tensorForm_gram (H : Form (fieldInvolution k L) Idx)
    (T : Over (Spec (CommRingCat.of k))) :
    ((tensorForm k L H T).gram : Matrix Idx Idx
      (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
      (H.gram : Matrix Idx Idx L).map
        (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T)) := rfl

/-- Every actual test restriction respects the scalar-extended Gram matrix. -/
theorem tensorMap_gram (H : Form (fieldInvolution k L) Idx)
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) :
    ((tensorForm k L H T).gram : Matrix Idx Idx
      (SpecialLinear.WeilRoot.tensorAlgebra k L T)).map
        (SpecialLinear.WeilRoot.tensorMap k L a) = (tensorForm k L H T').gram := by
  ext i j
  change QuasiSplitUnitary.tensorCoefficientMap
    ((algΓ (CommRingCat.of k)).map a).unop.hom
    ((H.gram : Matrix Idx Idx L) i j ⊗ₜ[k] 1) =
      (H.gram : Matrix Idx Idx L) i j ⊗ₜ[k] 1
  rw [QuasiSplitUnitary.tensorCoefficientMap_tmul, map_one]

/-- The actual determinant-one Hermitian matrices on each test scheme. -/
abbrev tensorPoints (H : Form (fieldInvolution k L) Idx)
    (T : Over (Spec (CommRingCat.of k))) :=
  specialUnitarySubgroup (tensorForm k L H T)

/-- Restriction of actual matrices along any morphism of test schemes. -/
def tensorPointsMap (H : Form (fieldInvolution k L) Idx)
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) :
    tensorPoints k L H T →* tensorPoints k L H T' :=
  coefficientMap (SpecialLinear.WeilRoot.tensorMap k L a)
    (SU3Root.SchemeModel.tensorMap_bar k L a) (tensorMap_gram k L H a)

@[simp] theorem tensorPointsMap_val (H : Form (fieldInvolution k L) Idx)
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (g : tensorPoints k L H T) :
    ((tensorPointsMap k L H a g).1 : Matrix Idx Idx
      (SpecialLinear.WeilRoot.tensorAlgebra k L T')) =
      (g.1 : Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T)).map
        (SpecialLinear.WeilRoot.tensorMap k L a) := rfl

@[simp] theorem tensorPointsMap_id (H : Form (fieldInvolution k L) Idx)
    (T : Over (Spec (CommRingCat.of k))) (g : tensorPoints k L H T) :
    tensorPointsMap k L H (𝟙 T) g = g := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change SpecialLinear.WeilRoot.tensorMap k L (𝟙 T) _ = _
  simp [SpecialLinear.WeilRoot.tensorMap]

theorem tensorPointsMap_comp (H : Form (fieldInvolution k L) Idx)
    {T T' T'' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) (b : T'' ⟶ T')
    (g : tensorPoints k L H T) :
    tensorPointsMap k L H b (tensorPointsMap k L H a g) =
      tensorPointsMap k L H (b ≫ a) g := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change SpecialLinear.WeilRoot.tensorMap k L b
    (SpecialLinear.WeilRoot.tensorMap k L a _) =
      SpecialLinear.WeilRoot.tensorMap k L (b ≫ a) _
  simp only [SpecialLinear.WeilRoot.tensorMap, Functor.map_comp, unop_comp]
  rfl

/-- The contravariant actual determinant-one Hermitian matrix point functor. -/
def pointFunctor (H : Form (fieldInvolution k L) Idx) :
    (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ GrpCat.{max u v} where
  obj T := GrpCat.of (tensorPoints k L H T.unop)
  map a := GrpCat.ofHom (tensorPointsMap k L H a.unop)
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    exact tensorPointsMap_id k L H T.unop g
  map_comp a b := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    exact (tensorPointsMap_comp k L H a.unop b.unop g).symm

/-- Extend any actual invertible matrix, without restrictions on its determinant. -/
def tensorMatrix (P : Matrix.GeneralLinearGroup Idx L)
    (T : Over (Spec (CommRingCat.of k))) :
    Matrix.GeneralLinearGroup Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T) :=
  Matrix.GeneralLinearGroup.map
    (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T)) P

omit [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L] in
/-- Extended matrices are natural under every test restriction. -/
theorem tensorMatrix_map (P : Matrix.GeneralLinearGroup Idx L)
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) :
    Matrix.GeneralLinearGroup.map (SpecialLinear.WeilRoot.tensorMap k L a)
      (tensorMatrix k L P T) = tensorMatrix k L P T' := by
  apply Units.ext
  ext i j
  change QuasiSplitUnitary.tensorCoefficientMap
    ((algΓ (CommRingCat.of k)).map a).unop.hom
    ((P : Matrix Idx Idx L) i j ⊗ₜ[k] 1) = (P : Matrix Idx Idx L) i j ⊗ₜ[k] 1
  rw [QuasiSplitUnitary.tensorCoefficientMap_tmul, map_one]

variable (H J : Form (fieldInvolution k L) Idx)
  (P : Matrix.GeneralLinearGroup Idx L)
  (hP : adjoint (fieldInvolution k L) (P : Matrix Idx Idx L) *
    (J.gram : Matrix Idx Idx L) * (P : Matrix Idx Idx L) = H.gram)

include hP in
/-- An actual field Gram congruence remains a congruence on every test scheme. -/
theorem tensorGramCongruence (T : Over (Spec (CommRingCat.of k))) :
    adjoint (SU3Root.SchemeModel.coefficientInvolution k L T)
      (tensorMatrix k L P T : Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T)) *
      ((tensorForm k L J T).gram : Matrix Idx Idx
        (SpecialLinear.WeilRoot.tensorAlgebra k L T)) *
      (tensorMatrix k L P T : Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
      (tensorForm k L H T).gram :=
  gramCongruence_map (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T))
    (HermitianRoot.SchemeModel.tensorInclusion_bar k L T) rfl rfl P hP

/-- Congruence transport on the actual tensor point groups. -/
def tensorIsometryEquiv (T : Over (Spec (CommRingCat.of k))) :
    tensorPoints k L H T ≃* tensorPoints k L J T :=
  specialUnitaryIsometryEquiv (tensorMatrix k L P T)
    (tensorGramCongruence k L H J P hP T)

/-- Congruence transport respects all test-scheme restrictions. -/
theorem tensorIsometryEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (g : tensorPoints k L H T) :
    tensorPointsMap k L J a (tensorIsometryEquiv k L H J P hP T g) =
      tensorIsometryEquiv k L H J P hP T' (tensorPointsMap k L H a g) := by
  simpa only [tensorIsometryEquiv, tensorMatrix_map, tensorPointsMap] using
    specialUnitaryIsometryEquiv_map (SpecialLinear.WeilRoot.tensorMap k L a)
      (SU3Root.SchemeModel.tensorMap_bar k L a) (tensorMap_gram k L H a)
      (tensorMap_gram k L J a) (tensorMatrix k L P T)
      (tensorGramCongruence k L H J P hP T) g

end Langlands.GroupScheme.HermitianMatrix.SchemeModel
