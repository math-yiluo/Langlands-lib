import Langlands.Geometry.FormalGroup.AtlasBaseChangePoints
import Langlands.Geometry.FormalGroup.SpecialAtlasBaseChange

/-! # Order-linear compatible-family comparison under coefficient extension -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ]
variable {X : BasicAtlas O R σ} (E : OrderAction D X) (S : CommAlgCat.{v} R)

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The identity tuple map with the full order-linearity of the formal chart comparison. -/
def baseChangeChartMap (A : CommAlgCat.{v} S) (b : X.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) :
    E.ChartPoint (restrictTest S A) (X.baseSource S b) (X.baseSource_unit S A b hb) →ₗ[D]
      (E.baseChange S).ChartPoint A b hb :=
  (E.baseChangeChartEquiv S A b hb).symm.toLinearMap.copy (fun x => x)
    (funext (fun x => (E.baseChangeChartEquiv_symm_apply S A b hb x).symm))

/-- Restriction of full compatible families respects every element of the order. -/
def toBaseChangePoints (A : CommAlgCat.{v} S) :
    E.Point (restrictTest S A) →ₗ[D] (E.baseChange S).Point A where
  toFun := X.toBaseChangePoints S A
  map_add' := (X.toBaseChangePoints S A).map_add
  map_smul' d x := by
    apply Subtype.ext
    funext t
    exact (E.baseChangeChartMap S t.algebra t.chart t.isUnit).map_smul d
      (x.val (X.restrictChartTest S t))

/-- The order-linear map has the same actual family restriction formula. -/
@[simp]
theorem toBaseChangePoints_apply (A : CommAlgCat.{v} S)
    (x : E.Point (restrictTest S A)) (t : (X.baseChange S).ChartTest A) :
    (E.toBaseChangePoints S A x).val t = x.val (X.restrictChartTest S t) := rfl

/-- The full compatible-family comparison is linear over the entire order. -/
def baseChangePointEquiv (A : CommAlgCat.{v} S) :
    E.Point (restrictTest S A) ≃ₗ[D] (E.baseChange S).Point A :=
  { E.toBaseChangePoints S A with
    invFun := X.fromBaseChangePoints S A
    left_inv := X.from_toBaseChangePoints S A
    right_inv := X.to_fromBaseChangePoints S A }

/-- Forgetting the order gives the previously constructed comparison of actual families. -/
theorem baseChangePointEquiv_eq (A : CommAlgCat.{v} S)
    (x : E.Point (restrictTest S A)) :
    E.baseChangePointEquiv S A x = X.baseChangePointEquiv S A x := rfl

/-- The forward order-linear equivalence restricts the actual chart tests. -/
@[simp]
theorem baseChangePointEquiv_apply (A : CommAlgCat.{v} S)
    (x : E.Point (restrictTest S A)) (t : (X.baseChange S).ChartTest A) :
    (E.baseChangePointEquiv S A x).val t = x.val (X.restrictChartTest S t) := rfl

/-- Its inverse is the constructed family on all induced coefficient tests. -/
@[simp]
theorem baseChangePointEquiv_symm_apply (A : CommAlgCat.{v} S)
    (y : (E.baseChange S).Point A) :
    (E.baseChangePointEquiv S A).symm y = X.fromBaseChangePoints S A y := rfl

/-- The full order-linear comparison is natural in the actual coefficient maps. -/
theorem toBaseChangePoints_natural {A B : CommAlgCat.{v} S} (φ : A ⟶ B)
    (x : E.Point (restrictTest S A)) :
    (E.baseChange S).mapPoints φ (E.toBaseChangePoints S A x) =
      E.toBaseChangePoints S B (E.mapPoints (restrictTestHom S φ) x) :=
  X.toBaseChangePoints_natural S φ x

/-- Coefficient extension gives a natural isomorphism of full order-module point functors. -/
def baseChangePointFunctorIso :
    restrictCoefficientFunctor (IsScalarTower.toAlgHom O R S) ⋙ E.pointFunctor ≅
      (E.baseChange S).pointFunctor :=
  NatIso.ofComponents
    (fun A => (E.baseChangePointEquiv S A).toModuleIso)
    (by
      intro A B φ
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (E.toBaseChangePoints_natural S φ x).symm)

/-- Restrict the same order-linear comparison to coefficient tests where pi is nilpotent. -/
def baseChangeNilpPointFunctorIso (π : R) :
    Nilp.forget S (algebraMap R S π) ⋙
        (restrictCoefficientFunctor (IsScalarTower.toAlgHom O R S) ⋙ E.pointFunctor) ≅
      (E.baseChange S).nilpPointFunctor (algebraMap R S π) :=
  Functor.isoWhiskerLeft (Nilp.forget S (algebraMap R S π)) (E.baseChangePointFunctorIso S)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable (X : SpecialAtlas K D ι R) (S : CommAlgCat.{v} R)

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Full compatible-family points of a special atlas commute with coefficient extension. -/
def baseChangePointEquiv (A : CommAlgCat.{v} S) :
    X.Point (BasicAtlas.restrictTest S A) ≃ₗ[IntegerRing K D] (X.baseChange S).Point A :=
  X.order.baseChangePointEquiv S A

/-- The special-atlas comparison is the actual restriction of compatible chart families. -/
@[simp]
theorem baseChangePointEquiv_apply (A : CommAlgCat.{v} S)
    (x : X.Point (BasicAtlas.restrictTest S A)) (t : (X.baseChange S).atlas.ChartTest A) :
    (X.baseChangePointEquiv S A x).val t = x.val (X.atlas.restrictChartTest S t) := rfl

/-- The original constructed inverse recovers every special-atlas chart test. -/
@[simp]
theorem baseChangePointEquiv_symm_apply (A : CommAlgCat.{v} S)
    (y : (X.baseChange S).Point A) :
    (X.baseChangePointEquiv S A).symm y = X.atlas.fromBaseChangePoints S A y := rfl

/-- The full special-atlas comparison commutes with coefficient maps. -/
theorem baseChangePointEquiv_natural {A B : CommAlgCat.{v} S} (φ : A ⟶ B)
    (x : X.Point (BasicAtlas.restrictTest S A)) :
    (X.baseChange S).order.mapPoints φ (X.baseChangePointEquiv S A x) =
      X.baseChangePointEquiv S B (X.order.mapPoints (BasicAtlas.restrictTestHom S φ) x) :=
  X.order.toBaseChangePoints_natural S φ x

/-- Natural comparison of the actual special-atlas division-order point functors. -/
def baseChangePointFunctorIso :
    restrictCoefficientFunctor (IsScalarTower.toAlgHom 𝒪[K] R S) ⋙ X.pointFunctor ≅
      (X.baseChange S).pointFunctor :=
  X.order.baseChangePointFunctorIso S

/-- Natural comparison of special-atlas points on nilpotent coefficient tests. -/
def baseChangeNilpPointFunctorIso (π : R) :
    Nilp.forget S (algebraMap R S π) ⋙
        (restrictCoefficientFunctor (IsScalarTower.toAlgHom 𝒪[K] R S) ⋙ X.pointFunctor) ≅
      (X.baseChange S).nilpPointFunctor (algebraMap R S π) :=
  X.order.baseChangeNilpPointFunctorIso S π

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
