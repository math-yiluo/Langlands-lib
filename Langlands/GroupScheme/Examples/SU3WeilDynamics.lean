import Langlands.GroupScheme.Examples.SU3DynamicRoots
import Langlands.GroupScheme.AffineWeilDynamics

/-! # Actual Weil restriction and upper contraction for the SU3 model -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SU3Root

namespace SchemeModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

attribute [local instance] SpecialLinear.WeilRoot.specialLinear_affine
  SpecialLinear.WeilRoot.specialLinear_finiteType

/-- The closed SU3 scheme is locally of finite type over its actual base field. -/
instance groupScheme_locallyOfFiniteType : LocallyOfFiniteType (groupScheme k L).X.hom := by
  rw [← (inclusion k L).hom.hom.w]
  infer_instance

end SchemeModel

namespace WeilSchemeModel

variable (F k L : Type u) [Field F] [Field k] [Field L]
  [Algebra F k] [FiniteDimensional F k] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

/-- The actual affine Weil restriction of the closed special unitary scheme. -/
abbrev groupScheme : GroupScheme (Spec (CommRingCat.of F)) :=
  AffineWeil.groupScheme F k (SchemeModel.groupScheme k L)

instance groupScheme_isAffine : IsAffine (groupScheme F k L).X.left := inferInstance

instance groupScheme_locallyOfFiniteType :
    LocallyOfFiniteType (groupScheme F k L).X.hom := inferInstance

/-- The tensor-spectrum test over the intermediate field attached to any ground-base test. -/
abbrev tensorTest (T : Over (Spec (CommRingCat.of F))) :
    Over (Spec (CommRingCat.of k)) :=
  AffineWeil.tensorTest F k T

/-- The actual coefficient involution on the nested tensor point model. -/
abbrev coefficientInvolution (T : Over (Spec (CommRingCat.of F))) :=
  SchemeModel.coefficientInvolution k L (tensorTest F k T)

/-- Every restricted point is an actual original SU3 point on the tensor spectrum. -/
abbrev testPointsEquiv (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (groupScheme F k L).X) ≃*
      (tensorTest F k T ⟶ (SchemeModel.groupScheme k L).X) :=
  AffineWeil.testPointsEquiv F k (SchemeModel.groupScheme k L) T

/-- All-test coordinates in the actual determinant-one Hermitian subgroup. -/
def pointsEquiv (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (groupScheme F k L).X) ≃*
      specialUnitarySubgroup (coefficientInvolution F k L T) :=
  (testPointsEquiv F k L T).trans
    (SchemeModel.pointsEquiv k L (tensorTest F k T))

/-- The intermediate-field point comparison respects all ground-base pullbacks. -/
theorem testPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of F))}
    (a : T' ⟶ T) (g : T ⟶ (groupScheme F k L).X) :
    testPointsEquiv F k L T' (a ≫ g) =
      AffineWeil.tensorTestMap F k a ≫ testPointsEquiv F k L T g :=
  AffineWeil.testPointsEquiv_naturality F k (SchemeModel.groupScheme k L) a g

/-- Matrix restriction is precisely coefficient restriction on the actual tensor spectra. -/
theorem pointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of F))}
    (a : T' ⟶ T) (g : T ⟶ (groupScheme F k L).X) :
    pointsEquiv F k L T' (a ≫ g) =
      specialUnitaryMap
        (SpecialLinear.WeilRoot.tensorMap k L (AffineWeil.tensorTestMap F k a))
        (SchemeModel.tensorMap_bar k L (AffineWeil.tensorTestMap F k a))
        (pointsEquiv F k L T g) := by
  change SchemeModel.pointsEquiv k L _ (testPointsEquiv F k L T' (a ≫ g)) = _
  rw [testPointsEquiv_naturality]
  exact SchemeModel.pointsEquiv_map k L (AffineWeil.tensorTestMap F k a) _

/-- The original upper matrices, transported to actual restricted-group points. -/
def upperPoints (T : Over (Spec (CommRingCat.of F))) :
    Parameters (coefficientInvolution F k L T) →*
      (T ⟶ (groupScheme F k L).X) :=
  (testPointsEquiv F k L T).symm.toMonoidHom.comp
    (SchemeModel.upperPoints k L (tensorTest F k T))

/-- Point comparison retains exactly the original upper point. -/
@[simp] theorem testPointsEquiv_upperPoints (T : Over (Spec (CommRingCat.of F)))
    (x : Parameters (coefficientInvolution F k L T)) :
    testPointsEquiv F k L T (upperPoints F k L T x) =
      SchemeModel.upperPoints k L (tensorTest F k T) x :=
  (testPointsEquiv F k L T).apply_symm_apply _

/-- The matrix of a restricted upper point is the original coupled upper matrix. -/
@[simp] theorem pointsEquiv_upperPoints (T : Over (Spec (CommRingCat.of F)))
    (x : Parameters (coefficientInvolution F k L T)) :
    pointsEquiv F k L T (upperPoints F k L T x) =
      upperSpecialUnitaryHom (coefficientInvolution F k L T) x := by
  change SchemeModel.pointsEquiv k L _ (testPointsEquiv F k L T _) = _
  rw [testPointsEquiv_upperPoints, SchemeModel.pointsEquiv_upperPoints]

/-- Restriction of upper points pulls back their original two coordinates. -/
theorem upperPoints_naturality {T T' : Over (Spec (CommRingCat.of F))}
    (a : T' ⟶ T) (x : Parameters (coefficientInvolution F k L T)) :
    upperPoints F k L T'
        (Parameters.map
          (SpecialLinear.WeilRoot.tensorMap k L (AffineWeil.tensorTestMap F k a))
          (SchemeModel.tensorMap_bar k L (AffineWeil.tensorTestMap F k a)) x) =
      a ≫ upperPoints F k L T x := by
  apply (testPointsEquiv F k L T').injective
  rw [testPointsEquiv_upperPoints, testPointsEquiv_naturality, testPointsEquiv_upperPoints]
  exact SchemeModel.upperPoints_naturality k L (AffineWeil.tensorTestMap F k a) x

/-- The original upper image groups form a subgroup functor on every actual test scheme. -/
def upperFunctor : SubgroupFunctor (groupScheme F k L) where
  carrier T := (upperPoints F k L T).range
  comp_mem := by
    intro T T' a g hg
    obtain ⟨x, rfl⟩ := hg
    exact ⟨_, upperPoints_naturality F k L a x⟩

/-- The actual ground-base cocharacter obtained from the original SU3 diagonal. -/
abbrev cocharacter : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ groupScheme F k L :=
  AffineWeil.cocharacter F k (SchemeModel.cocharacter k L)

/-- The transferred cocharacter evaluates the original diagonal on the included scalar unit. -/
theorem testPointsEquiv_cocharacter {T : Over (Spec (CommRingCat.of F))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of F))).X) :
    testPointsEquiv F k L T (x ≫ (cocharacter F k L).hom.hom) =
      AffineWeil.scalarGmPoints F k T x ≫ (SchemeModel.cocharacter k L).hom.hom :=
  AffineWeil.testPointsEquiv_cocharacter F k (SchemeModel.cocharacter k L) x

/-- The explicit original upper contraction, transferred to the actual restricted group. -/
def upperContraction {T : Over (Spec (CommRingCat.of F))}
    (x : Parameters (coefficientInvolution F k L T)) :
    T ⊗ AffineLine.scheme (Spec (CommRingCat.of F)) ⟶ (groupScheme F k L).X :=
  AffineWeil.transferExtension F k (SchemeModel.upperContraction k L x)

/-- The transferred curve extends conjugation by the actual ground-base cocharacter. -/
theorem upperContraction_isOrbitExtension {T : Over (Spec (CommRingCat.of F))}
    (x : Parameters (coefficientInvolution F k L T)) :
    Dynamic.IsOrbitExtension (cocharacter F k L) (upperPoints F k L T x)
      (upperContraction F k L x) := by
  apply AffineWeil.transferExtension_isOrbitExtension F k (SchemeModel.cocharacter k L)
  rw [testPointsEquiv_upperPoints]
  exact SchemeModel.upperContraction_isOrbitExtension k L x

/-- The transferred upper contraction has the actual identity as its zero value. -/
@[simp] theorem evalZero_upperContraction {T : Over (Spec (CommRingCat.of F))}
    (x : Parameters (coefficientInvolution F k L T)) :
    Dynamic.evalZero (upperContraction F k L x) = 1 := by
  apply (testPointsEquiv F k L T).injective
  rw [map_one]
  exact (AffineWeil.testPointsEquiv_evalZero_transferExtension F k
    (SchemeModel.upperContraction k L x)).trans
      (SchemeModel.upperContraction_evalZero k L x)

/-- All actual restricted upper points contract to the identity on every relative test scheme. -/
theorem upperFunctor_le_dynamicUnipotent :
    upperFunctor F k L ≤ Dynamic.unipotent (cocharacter F k L) := by
  intro T g hg
  obtain ⟨x, rfl⟩ := hg
  exact ⟨upperContraction F k L x, upperContraction_isOrbitExtension F k L x,
    evalZero_upperContraction F k L x⟩

end WeilSchemeModel
end Langlands.GroupScheme.SU3Root
