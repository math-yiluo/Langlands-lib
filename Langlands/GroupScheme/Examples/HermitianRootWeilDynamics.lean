import Langlands.GroupScheme.Examples.HermitianRootDynamicRoots
import Langlands.GroupScheme.AffineWeilDynamics

/-! # Actual Weil restriction and upper contraction for the weighted Hermitian model -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

namespace SchemeModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

attribute [local instance] SpecialLinear.WeilRoot.specialLinear_affine
  SpecialLinear.WeilRoot.specialLinear_finiteType

/-- The closed weighted Hermitian scheme is locally of finite type over its actual base field. -/
instance groupScheme_locallyOfFiniteType : LocallyOfFiniteType (groupScheme k L H w hw).X.hom := by
  rw [← (inclusion k L H w hw).hom.hom.w]
  infer_instance

end SchemeModel

namespace WeilSchemeModel

variable (F k L : Type u) [Field F] [Field k] [Field L]
  [Algebra F k] [FiniteDimensional F k] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

/-- The actual affine Weil restriction of the closed weighted Hermitian scheme. -/
abbrev groupScheme : GroupScheme (Spec (CommRingCat.of F)) :=
  AffineWeil.groupScheme F k (SchemeModel.groupScheme k L H w hw)

instance groupScheme_isAffine : IsAffine (groupScheme F k L H w hw).X.left := inferInstance

instance groupScheme_locallyOfFiniteType :
    LocallyOfFiniteType (groupScheme F k L H w hw).X.hom := inferInstance

/-- The tensor-spectrum test over the intermediate field attached to any ground-base test. -/
abbrev tensorTest (T : Over (Spec (CommRingCat.of F))) :
    Over (Spec (CommRingCat.of k)) :=
  AffineWeil.tensorTest F k T

/-- The original weighted form on the nested tensor coefficient algebra. -/
abbrev tensorForm (T : Over (Spec (CommRingCat.of F))) :=
  SchemeModel.tensorForm k L H (tensorTest F k T)

/-- Every restricted point is an actual original weighted Hermitian point on the tensor spectrum. -/
abbrev testPointsEquiv (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (groupScheme F k L H w hw).X) ≃*
      (tensorTest F k T ⟶ (SchemeModel.groupScheme k L H w hw).X) :=
  AffineWeil.testPointsEquiv F k (SchemeModel.groupScheme k L H w hw) T

/-- All-test coordinates in the original full weighted determinant-one isometry subgroup. -/
def pointsEquiv (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (groupScheme F k L H w hw).X) ≃*
      specialUnitarySubgroup (tensorForm F k L H T) :=
  (testPointsEquiv F k L H w hw T).trans
    (SchemeModel.pointsEquiv k L H w hw (tensorTest F k T))

/-- The intermediate-field point comparison respects all ground-base pullbacks. -/
theorem testPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of F))}
    (a : T' ⟶ T) (g : T ⟶ (groupScheme F k L H w hw).X) :
    testPointsEquiv F k L H w hw T' (a ≫ g) =
      AffineWeil.tensorTestMap F k a ≫ testPointsEquiv F k L H w hw T g :=
  AffineWeil.testPointsEquiv_naturality F k (SchemeModel.groupScheme k L H w hw) a g

/-- Matrix restriction is precisely coefficient restriction on the actual tensor spectra. -/
theorem pointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of F))}
    (a : T' ⟶ T) (g : T ⟶ (groupScheme F k L H w hw).X) :
    pointsEquiv F k L H w hw T' (a ≫ g) =
      specialUnitaryMap
        (SpecialLinear.WeilRoot.tensorMap k L (AffineWeil.tensorTestMap F k a))
        (SU3Root.SchemeModel.tensorMap_bar k L (AffineWeil.tensorTestMap F k a))
        (SchemeModel.tensorMap_weight k L H (AffineWeil.tensorTestMap F k a))
        (pointsEquiv F k L H w hw T g) := by
  change SchemeModel.pointsEquiv k L H w hw _ (testPointsEquiv F k L H w hw T' (a ≫ g)) = _
  rw [testPointsEquiv_naturality]
  exact SchemeModel.pointsEquiv_map k L H w hw (AffineWeil.tensorTestMap F k a) _

/-- The original upper matrices, transported to actual restricted-group points. -/
def upperPoints (T : Over (Spec (CommRingCat.of F))) :
    Parameters (tensorForm F k L H T) →*
      (T ⟶ (groupScheme F k L H w hw).X) :=
  (testPointsEquiv F k L H w hw T).symm.toMonoidHom.comp
    (SchemeModel.upperPoints k L H w hw (tensorTest F k T))

/-- Point comparison retains exactly the original upper point. -/
@[simp] theorem testPointsEquiv_upperPoints (T : Over (Spec (CommRingCat.of F)))
    (x : Parameters (tensorForm F k L H T)) :
    testPointsEquiv F k L H w hw T (upperPoints F k L H w hw T x) =
      SchemeModel.upperPoints k L H w hw (tensorTest F k T) x :=
  (testPointsEquiv F k L H w hw T).apply_symm_apply _

/-- The matrix of a restricted upper point is the original coupled upper matrix. -/
@[simp] theorem pointsEquiv_upperPoints (T : Over (Spec (CommRingCat.of F)))
    (x : Parameters (tensorForm F k L H T)) :
    pointsEquiv F k L H w hw T (upperPoints F k L H w hw T x) =
      upperSpecialUnitaryHom (tensorForm F k L H T) x := by
  change SchemeModel.pointsEquiv k L H w hw _ (testPointsEquiv F k L H w hw T _) = _
  rw [testPointsEquiv_upperPoints, SchemeModel.pointsEquiv_upperPoints]

/-- Restriction of upper points pulls back their original two coordinates. -/
theorem upperPoints_naturality {T T' : Over (Spec (CommRingCat.of F))}
    (a : T' ⟶ T) (x : Parameters (tensorForm F k L H T)) :
    upperPoints F k L H w hw T'
        (Parameters.map
          (SpecialLinear.WeilRoot.tensorMap k L (AffineWeil.tensorTestMap F k a))
          (SU3Root.SchemeModel.tensorMap_bar k L (AffineWeil.tensorTestMap F k a))
          (SchemeModel.tensorMap_weight k L H (AffineWeil.tensorTestMap F k a)) x) =
      a ≫ upperPoints F k L H w hw T x := by
  apply (testPointsEquiv F k L H w hw T').injective
  rw [testPointsEquiv_upperPoints, testPointsEquiv_naturality, testPointsEquiv_upperPoints]
  exact SchemeModel.upperPoints_naturality k L H w hw (AffineWeil.tensorTestMap F k a) x

/-- The original upper image groups form a subgroup functor on every actual test scheme. -/
def upperFunctor : SubgroupFunctor (groupScheme F k L H w hw) where
  carrier T := (upperPoints F k L H w hw T).range
  comp_mem := by
    intro T T' a g hg
    obtain ⟨x, rfl⟩ := hg
    exact ⟨_, upperPoints_naturality F k L H w hw a x⟩

/-- The actual ground-base cocharacter obtained from the original weighted Hermitian diagonal. -/
abbrev cocharacter : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ groupScheme F k L H w hw :=
  AffineWeil.cocharacter F k (SchemeModel.cocharacter k L H w hw)

/-- The transferred cocharacter evaluates the original diagonal on the included scalar unit. -/
theorem testPointsEquiv_cocharacter {T : Over (Spec (CommRingCat.of F))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of F))).X) :
    testPointsEquiv F k L H w hw T (x ≫ (cocharacter F k L H w hw).hom.hom) =
      AffineWeil.scalarGmPoints F k T x ≫ (SchemeModel.cocharacter k L H w hw).hom.hom :=
  AffineWeil.testPointsEquiv_cocharacter F k (SchemeModel.cocharacter k L H w hw) x

/-- The explicit original upper contraction, transferred to the actual restricted group. -/
def upperContraction {T : Over (Spec (CommRingCat.of F))}
    (x : Parameters (tensorForm F k L H T)) :
    T ⊗ AffineLine.scheme (Spec (CommRingCat.of F)) ⟶ (groupScheme F k L H w hw).X :=
  AffineWeil.transferExtension F k (SchemeModel.upperContraction k L H w hw x)

/-- The transferred curve extends conjugation by the actual ground-base cocharacter. -/
theorem upperContraction_isOrbitExtension {T : Over (Spec (CommRingCat.of F))}
    (x : Parameters (tensorForm F k L H T)) :
    Dynamic.IsOrbitExtension (cocharacter F k L H w hw) (upperPoints F k L H w hw T x)
      (upperContraction F k L H w hw x) := by
  apply AffineWeil.transferExtension_isOrbitExtension F k (SchemeModel.cocharacter k L H w hw)
  rw [testPointsEquiv_upperPoints]
  exact SchemeModel.upperContraction_isOrbitExtension k L H w hw x

/-- The transferred upper contraction has the actual identity as its zero value. -/
@[simp] theorem evalZero_upperContraction {T : Over (Spec (CommRingCat.of F))}
    (x : Parameters (tensorForm F k L H T)) :
    Dynamic.evalZero (upperContraction F k L H w hw x) = 1 := by
  apply (testPointsEquiv F k L H w hw T).injective
  rw [map_one]
  exact (AffineWeil.testPointsEquiv_evalZero_transferExtension F k
    (SchemeModel.upperContraction k L H w hw x)).trans
      (SchemeModel.upperContraction_evalZero k L H w hw x)

/-- All actual restricted upper points contract to the identity on every relative test scheme. -/
theorem upperFunctor_le_dynamicUnipotent :
    upperFunctor F k L H w hw ≤ Dynamic.unipotent (cocharacter F k L H w hw) := by
  intro T g hg
  obtain ⟨x, rfl⟩ := hg
  exact ⟨upperContraction F k L H w hw x, upperContraction_isOrbitExtension F k L H w hw x,
    evalZero_upperContraction F k L H w hw x⟩

end WeilSchemeModel
end Langlands.GroupScheme.HermitianRoot
