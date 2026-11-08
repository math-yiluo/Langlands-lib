import Langlands.GroupScheme.Examples.HermitianRootMatrixNaturality
import Langlands.GroupScheme.Examples.SU3GroupScheme

/-! # The actual group scheme of a nondegenerate diagonal Hermitian form -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianRoot.SchemeModel

open SU3Root

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

attribute [local instance] SpecialLinear.WeilRoot.specialLinear_affine
  SpecialLinear.WeilRoot.specialLinear_finiteType

/-- The actual affine Weil restriction of the ambient special-linear group. -/
abbrev ambient (Middle : Type) [Fintype Middle] [DecidableEq Middle] :
    GroupScheme (Spec (CommRingCat.of k)) :=
  SpecialLinear.WeilRoot.groupScheme (n := Index Middle) k L

variable {Middle : Type}

/-- The original diagonal form extended to the actual tensor coefficient ring. -/
def tensorForm (H : DiagonalForm (fieldInvolution k L) Middle)
    (T : Over (Spec (CommRingCat.of k))) :
    DiagonalForm (SU3Root.SchemeModel.coefficientInvolution k L T) Middle where
  weight i := algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T) (H.weight i)
  bar_weight i := by
    change QuasiSplitUnitary.scalarConjugation
      (SpecialLinear.WeilRoot.sectionAlgebra k T) (conjugation k L)
        (H.weight i ⊗ₜ[k] 1) = H.weight i ⊗ₜ[k] 1
    rw [QuasiSplitUnitary.scalarConjugation_tmul]
    exact congrArg (fun a : L => a ⊗ₜ[k]
      (1 : SpecialLinear.WeilRoot.sectionAlgebra k T)) (H.bar_weight i)

/-- Actual unit witnesses for the tensor form's middle weights. -/
def tensorUnits (w : Middle → Lˣ) (T : Over (Spec (CommRingCat.of k))) :
    Middle → (SpecialLinear.WeilRoot.tensorAlgebra k L T)ˣ :=
  fun i => Units.map (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T)).toMonoidHom (w i)

theorem tensorUnits_val {H : DiagonalForm (fieldInvolution k L) Middle}
    {w : Middle → Lˣ} (hw : ∀ i, (w i : L) = H.weight i)
    (T : Over (Spec (CommRingCat.of k))) (i : Middle) :
    (tensorUnits k L w T i : SpecialLinear.WeilRoot.tensorAlgebra k L T) =
      (tensorForm k L H T).weight i :=
  congrArg (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T)) (hw i)

/-- Every test restriction carries the original included weights to themselves. -/
theorem tensorMap_weight (H : DiagonalForm (fieldInvolution k L) Middle)
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) (i : Middle) :
    SpecialLinear.WeilRoot.tensorMap k L a ((tensorForm k L H T).weight i) =
      (tensorForm k L H T').weight i := by
  change QuasiSplitUnitary.tensorCoefficientMap ((algΓ (CommRingCat.of k)).map a).unop.hom
    (H.weight i ⊗ₜ[k] 1) = H.weight i ⊗ₜ[k] 1
  rw [QuasiSplitUnitary.tensorCoefficientMap_tmul, map_one]

variable [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

instance ambient_isAffine : IsAffine (ambient k L Middle).X.left := inferInstance

/-- Inverse adjoint on points of the actual restricted ambient group. -/
def twistPoints (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (ambient k L Middle).X) →* (T ⟶ (ambient k L Middle).X) :=
  (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).symm.toMonoidHom.comp
    ((unitaryTwist (tensorForm k L H T) (tensorUnits k L w T)
      (tensorUnits_val k L hw T)).comp
        (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).toMonoidHom)

@[simp] theorem tensorMatrixEquiv_twistPoints (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (ambient k L Middle).X) :
    SpecialLinear.WeilRoot.tensorMatrixEquiv k L T (twistPoints k L H w hw T x) =
      unitaryTwist (tensorForm k L H T) (tensorUnits k L w T)
        (tensorUnits_val k L hw T) (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T x) :=
  (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).apply_symm_apply _

/-- The full weighted inverse adjoint commutes with every actual test restriction. -/
theorem twistPoints_naturality {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ (ambient k L Middle).X) :
    twistPoints k L H w hw T' (a ≫ x) = a ≫ twistPoints k L H w hw T x := by
  apply (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T').injective
  rw [tensorMatrixEquiv_twistPoints,
    SpecialLinear.WeilRoot.tensorMatrixEquiv_naturality,
    unitaryTwist_map _ (SU3Root.SchemeModel.tensorMap_bar k L a)
      (tensorMap_weight k L H a),
    SpecialLinear.WeilRoot.tensorMatrixEquiv_naturality, tensorMatrixEquiv_twistPoints]

/-- The actual inverse-adjoint endomorphism of the restricted special-linear group. -/
def twist : ambient k L Middle ⟶ ambient k L Middle :=
  homOfPoints (twistPoints k L H w hw) (twistPoints_naturality k L H w hw)

@[simp] theorem tensorMatrixEquiv_twist (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (ambient k L Middle).X) :
    SpecialLinear.WeilRoot.tensorMatrixEquiv k L T (x ≫ (twist k L H w hw).hom.hom) =
      unitaryTwist (tensorForm k L H T) (tensorUnits k L w T)
        (tensorUnits_val k L hw T) (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T x) := by
  rw [twist, comp_homOfPoints, tensorMatrixEquiv_twistPoints]

/-- The actual fixed subgroup functor of the weighted inverse adjoint. -/
abbrev fixedFunctor : SubgroupFunctor (ambient k L Middle) :=
  endomorphismFixedSubgroup (twist k L H w hw)

/-- Fixedness of a test point is precisely fixedness of its actual tensor matrix. -/
theorem mem_fixedFunctor_iff (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (ambient k L Middle).X) :
    x ∈ (fixedFunctor k L H w hw).carrier T ↔
      SpecialLinear.WeilRoot.tensorMatrixEquiv k L T x ∈
        twistFixedSubgroup (tensorForm k L H T) (tensorUnits k L w T)
          (tensorUnits_val k L hw T) := by
  change x ≫ (twist k L H w hw).hom.hom = x ↔ _
  rw [← (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).injective.eq_iff,
    tensorMatrixEquiv_twist]
  rfl

/-- The group scheme on the actual scheme equalizer of inverse adjoint and identity. -/
def groupScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  (fixedFunctor k L H w hw).representingGroupScheme
    (equalizer.ι (twist k L H w hw).hom.hom (𝟙 (ambient k L Middle).X))
    (fun _ x => mem_endomorphismFixedSubgroup_iff_factors (twist k L H w hw) x)

/-- The actual inclusion into the restricted special-linear group. -/
def inclusion : groupScheme k L H w hw ⟶ ambient k L Middle :=
  (fixedFunctor k L H w hw).representingHom
    (equalizer.ι (twist k L H w hw).hom.hom (𝟙 (ambient k L Middle).X))
    (fun _ x => mem_endomorphismFixedSubgroup_iff_factors (twist k L H w hw) x)

@[simp] theorem inclusion_hom :
    (inclusion k L H w hw).hom.hom =
      equalizer.ι (twist k L H w hw).hom.hom (𝟙 (ambient k L Middle).X) :=
  (fixedFunctor k L H w hw).representingHom_hom _ _

/-- The actual inclusion is a closed immersion. -/
instance inclusion_isClosedImmersion :
    IsClosedImmersion (inclusion k L H w hw).hom.hom.left := by
  have : IsSeparated (ambient k L Middle).X.hom := inferInstance
  rw [inclusion_hom]
  exact AlgebraicGeometry.isClosedImmersion_equalizer_ι_left
    (twist k L H w hw).hom.hom (𝟙 (ambient k L Middle).X)

/-- The constructed weighted special unitary group scheme is affine. -/
instance groupScheme_isAffine : IsAffine (groupScheme k L H w hw).X.left := by
  have : IsAffine (ambient k L Middle).X.left := inferInstance
  exact isAffine_of_isAffineHom (inclusion k L H w hw).hom.hom.left

/-- Points on the actual scheme equalizer are the fixed subgroup functor. -/
def fixedPointsEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (groupScheme k L H w hw).X) ≃* (fixedFunctor k L H w hw).carrier T where
  toEquiv := ((fixedFunctor k L H w hw).schemeRepresentableBy
    (equalizer.ι (twist k L H w hw).hom.hom (𝟙 (ambient k L Middle).X))
    (fun _ x => mem_endomorphismFixedSubgroup_iff_factors (twist k L H w hw) x)).homEquiv
  map_mul' x y := by
    apply Subtype.ext
    change (x * y) ≫ _ = (x ≫ _) * (y ≫ _)
    rw [← inclusion_hom k L H w hw, MonObj.mul_comp]

set_option maxRecDepth 2048 in
/-- The fixed subgroup functor has the actual fixed special-linear tensor matrices. -/
def fixedTensorEquiv (T : Over (Spec (CommRingCat.of k))) :
    (fixedFunctor k L H w hw).carrier T ≃*
      twistFixedSubgroup (tensorForm k L H T) (tensorUnits k L w T)
        (tensorUnits_val k L hw T) where
  toFun x := ⟨SpecialLinear.WeilRoot.tensorMatrixEquiv k L T x.1,
    (mem_fixedFunctor_iff k L H w hw T x.1).mp x.2⟩
  invFun x := ⟨(SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).symm x.1,
    (mem_fixedFunctor_iff k L H w hw T _).mpr (by
      change unitaryTwist _ _ _ ((SpecialLinear.WeilRoot.tensorMatrixEquiv k L T)
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

/-- All test points are exactly the actual determinant-one weighted Hermitian isometries. -/
def pointsEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (groupScheme k L H w hw).X) ≃* specialUnitarySubgroup (tensorForm k L H T) :=
  ((fixedPointsEquiv k L H w hw T).trans (fixedTensorEquiv k L H w hw T)).trans
    (fixedSpecialUnitaryEquiv (tensorForm k L H T) (tensorUnits k L w T)
      (tensorUnits_val k L hw T))

/-- The comparison keeps the actual tensor matrix of the ambient inclusion. -/
theorem pointsEquiv_val (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (groupScheme k L H w hw).X) :
    ((pointsEquiv k L H w hw T x).1 : Matrix (Index Middle) (Index Middle)
      (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
    (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T (x ≫ (inclusion k L H w hw).hom.hom) :
      Matrix (Index Middle) (Index Middle) (SpecialLinear.WeilRoot.tensorAlgebra k L T)) := by
  rw [inclusion_hom]
  rfl

/-- The actual point comparison respects every change of test scheme. -/
theorem pointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme k L H w hw).X) :
    ((pointsEquiv k L H w hw T' (a ≫ x)).1 : Matrix (Index Middle) (Index Middle)
      (SpecialLinear.WeilRoot.tensorAlgebra k L T')) =
      (((pointsEquiv k L H w hw T x).1 : Matrix (Index Middle) (Index Middle)
        (SpecialLinear.WeilRoot.tensorAlgebra k L T))).map
          (SpecialLinear.WeilRoot.tensorMap k L a) := by
  rw [pointsEquiv_val, pointsEquiv_val, Category.assoc,
    SpecialLinear.WeilRoot.tensorMatrixEquiv_naturality]
  rfl

/-- Naturality also holds as an equality in the actual determinant-one isometry subgroup. -/
theorem pointsEquiv_map {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme k L H w hw).X) :
    pointsEquiv k L H w hw T' (a ≫ x) =
      specialUnitaryMap (SpecialLinear.WeilRoot.tensorMap k L a)
        (SU3Root.SchemeModel.tensorMap_bar k L a) (tensorMap_weight k L H a)
        (pointsEquiv k L H w hw T x) := by
  apply Subtype.ext
  apply Units.ext
  exact pointsEquiv_naturality k L H w hw a x

end Langlands.GroupScheme.HermitianRoot.SchemeModel
