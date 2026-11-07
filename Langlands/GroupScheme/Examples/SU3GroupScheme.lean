import Langlands.GroupScheme.Examples.SU3MatrixFixedPoints
import Langlands.GroupScheme.Examples.SU3RootParametersUnitaryComparison
import Langlands.GroupScheme.SpecialLinearWeilPointModels
import Langlands.GroupScheme.EndomorphismFixedSubgroup

/-! # The actual fixed-point special unitary group scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SU3Root.SchemeModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

attribute [local instance] SpecialLinear.WeilRoot.specialLinear_affine
  SpecialLinear.WeilRoot.specialLinear_finiteType

/-- The actual affine Weil restriction of SL3 from the quadratic extension. -/
abbrev ambient : GroupScheme (Spec (CommRingCat.of k)) :=
  SpecialLinear.WeilRoot.groupScheme (n := Fin 3) k L

instance ambient_isAffine : IsAffine (ambient k L).X.left := inferInstance

/-- The involution on the actual tensor coefficient ring of any test scheme. -/
abbrev coefficientInvolution (T : Over (Spec (CommRingCat.of k))) :
    RingInvolution (SpecialLinear.WeilRoot.tensorAlgebra k L T) :=
  unitaryTensorInvolution k L (SpecialLinear.WeilRoot.sectionAlgebra k T)

/-- Every actual test-scheme coefficient map commutes with tensor conjugation. -/
theorem tensorMap_bar {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (x : SpecialLinear.WeilRoot.tensorAlgebra k L T) :
    SpecialLinear.WeilRoot.tensorMap k L a ((coefficientInvolution k L T).bar x) =
      (coefficientInvolution k L T').bar (SpecialLinear.WeilRoot.tensorMap k L a x) := by
  change QuasiSplitUnitary.tensorCoefficientMap ((algΓ (CommRingCat.of k)).map a).unop.hom
      (QuasiSplitUnitary.scalarConjugation _ (conjugation k L) x) =
    QuasiSplitUnitary.scalarConjugation _ (conjugation k L)
      (QuasiSplitUnitary.tensorCoefficientMap ((algΓ (CommRingCat.of k)).map a).unop.hom x)
  induction x using TensorProduct.inductionOn with
  | tmul e r => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Inverse adjoint on actual restricted SL3 points. -/
def twistPoints (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (ambient k L).X) →* (T ⟶ (ambient k L).X) :=
  (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).symm.toMonoidHom.comp
    ((unitaryTwist (coefficientInvolution k L T)).comp
      (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).toMonoidHom)

@[simp] theorem tensorMatrixEquiv_twistPoints (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (ambient k L).X) :
    SpecialLinear.WeilRoot.tensorMatrixEquiv k L T (twistPoints k L T x) =
      unitaryTwist (coefficientInvolution k L T)
        (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T x) := by
  exact (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).apply_symm_apply _

/-- Inverse adjoint commutes with every change of test scheme. -/
theorem twistPoints_naturality {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ (ambient k L).X) :
    twistPoints k L T' (a ≫ x) = a ≫ twistPoints k L T x := by
  apply (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T').injective
  rw [tensorMatrixEquiv_twistPoints,
    SpecialLinear.WeilRoot.tensorMatrixEquiv_naturality,
    unitaryTwist_map _ (tensorMap_bar k L a),
    SpecialLinear.WeilRoot.tensorMatrixEquiv_naturality, tensorMatrixEquiv_twistPoints]

/-- The actual inverse-adjoint group-scheme endomorphism of restricted SL3. -/
def twist : ambient k L ⟶ ambient k L :=
  homOfPoints (twistPoints k L) (twistPoints_naturality k L)

@[simp] theorem tensorMatrixEquiv_twist (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (ambient k L).X) :
    SpecialLinear.WeilRoot.tensorMatrixEquiv k L T (x ≫ (twist k L).hom.hom) =
      unitaryTwist (coefficientInvolution k L T)
        (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T x) := by
  rw [twist, comp_homOfPoints, tensorMatrixEquiv_twistPoints]

/-- The fixed subgroup functor on all actual test schemes. -/
abbrev fixedFunctor : SubgroupFunctor (ambient k L) :=
  endomorphismFixedSubgroup (twist k L)

/-- Test points are fixed exactly when their actual tensor matrices are fixed. -/
theorem mem_fixedFunctor_iff (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (ambient k L).X) :
    x ∈ (fixedFunctor k L).carrier T ↔
      SpecialLinear.WeilRoot.tensorMatrixEquiv k L T x ∈
        twistFixedSubgroup (coefficientInvolution k L T) := by
  change x ≫ (twist k L).hom.hom = x ↔ _
  rw [← (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).injective.eq_iff,
    tensorMatrixEquiv_twist]
  rfl

/-- The actual group scheme carried by the scheme equalizer of inverse adjoint and identity. -/
def groupScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  (fixedFunctor k L).representingGroupScheme
    (equalizer.ι (twist k L).hom.hom (𝟙 (ambient k L).X))
    (fun _ x => mem_endomorphismFixedSubgroup_iff_factors (twist k L) x)

/-- The actual inclusion of the special unitary group into restricted SL3. -/
def inclusion : groupScheme k L ⟶ ambient k L :=
  (fixedFunctor k L).representingHom
    (equalizer.ι (twist k L).hom.hom (𝟙 (ambient k L).X))
    (fun _ x => mem_endomorphismFixedSubgroup_iff_factors (twist k L) x)

@[simp] theorem inclusion_hom :
    (inclusion k L).hom.hom =
      equalizer.ι (twist k L).hom.hom (𝟙 (ambient k L).X) :=
  (fixedFunctor k L).representingHom_hom _ _

/-- The actual inclusion is a closed immersion. -/
instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion k L).hom.hom.left := by
  have : IsSeparated (ambient k L).X.hom := inferInstance
  rw [inclusion_hom]
  exact AlgebraicGeometry.isClosedImmersion_equalizer_ι_left
    (twist k L).hom.hom (𝟙 (ambient k L).X)

/-- The constructed special unitary group scheme is affine. -/
instance groupScheme_isAffine : IsAffine (groupScheme k L).X.left := by
  have : IsAffine (ambient k L).X.left := inferInstance
  exact isAffine_of_isAffineHom (inclusion k L).hom.hom.left

/-- Scheme-equalizer points identify multiplicatively with the fixed subgroup functor. -/
def fixedPointsEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (groupScheme k L).X) ≃* (fixedFunctor k L).carrier T where
  toEquiv := ((fixedFunctor k L).schemeRepresentableBy
    (equalizer.ι (twist k L).hom.hom (𝟙 (ambient k L).X))
    (fun _ x => mem_endomorphismFixedSubgroup_iff_factors (twist k L) x)).homEquiv
  map_mul' x y := by
    apply Subtype.ext
    change (x * y) ≫ _ = (x ≫ _) * (y ≫ _)
    rw [← inclusion_hom k L, MonObj.mul_comp]

set_option maxRecDepth 2048 in
/-- The fixed subgroup functor has exactly the actual tensor SL3 fixed matrices. -/
def fixedTensorEquiv (T : Over (Spec (CommRingCat.of k))) :
    (fixedFunctor k L).carrier T ≃* twistFixedSubgroup (coefficientInvolution k L T) where
  toFun x := ⟨SpecialLinear.WeilRoot.tensorMatrixEquiv k L T x.1,
    (mem_fixedFunctor_iff k L T x.1).mp x.2⟩
  invFun x := ⟨(SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).symm x.1,
    (mem_fixedFunctor_iff k L T _).mpr (by
      change unitaryTwist _ ((SpecialLinear.WeilRoot.tensorMatrixEquiv k L T)
        ((SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).symm x.1)) =
          (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T)
            ((SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).symm x.1)
      rw [MulEquiv.apply_symm_apply]
      exact x.2)⟩
  left_inv x := Subtype.ext ((SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).symm_apply_apply x.1)
  right_inv x := Subtype.ext ((SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).apply_symm_apply x.1)
  map_mul' x y := by
    apply Subtype.ext
    exact (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).map_mul x.1 y.1

/-- All points of the actual special unitary group are determinant-one Hermitian tensor matrices. -/
def pointsEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (groupScheme k L).X) ≃* specialUnitarySubgroup (coefficientInvolution k L T) :=
  ((fixedPointsEquiv k L T).trans (fixedTensorEquiv k L T)).trans
    (fixedSpecialUnitaryEquiv (coefficientInvolution k L T))

/-- The comparison preserves the actual matrix of the ambient inclusion. -/
theorem pointsEquiv_val (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (groupScheme k L).X) :
    ((pointsEquiv k L T x).1 : Matrix (Fin 3) (Fin 3)
      (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
    (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T (x ≫ (inclusion k L).hom.hom) :
      Matrix (Fin 3) (Fin 3) (SpecialLinear.WeilRoot.tensorAlgebra k L T)) := by
  rw [inclusion_hom]
  rfl

/-- The all-test matrix comparison respects every restriction of test schemes. -/
theorem pointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme k L).X) :
    ((pointsEquiv k L T' (a ≫ x)).1 : Matrix (Fin 3) (Fin 3)
      (SpecialLinear.WeilRoot.tensorAlgebra k L T')) =
      (((pointsEquiv k L T x).1 : Matrix (Fin 3) (Fin 3)
        (SpecialLinear.WeilRoot.tensorAlgebra k L T))).map
          (SpecialLinear.WeilRoot.tensorMap k L a) := by
  rw [pointsEquiv_val, pointsEquiv_val, Category.assoc,
    SpecialLinear.WeilRoot.tensorMatrixEquiv_naturality]
  rfl

end Langlands.GroupScheme.SU3Root.SchemeModel
