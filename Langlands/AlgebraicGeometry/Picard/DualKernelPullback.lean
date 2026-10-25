import Langlands.AlgebraicGeometry.Picard.DualGroupSchemeMap
import Langlands.AlgebraicGeometry.Picard.UniversalFamilyTriviality
import Langlands.AbelianScheme.Kernel

/-! # Poincaré pullback trivializations for points of a dual kernel -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule Langlands.Scheme.Modules

variable {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)

/-- The actual parameter pullback of the chosen rigidified Poincaré family. -/
def dualPointFamily {T : Over S} (p : T ⟶ dualScheme A hA) : RigidifiedFamily A T :=
  (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
    p).obj (poincareFamily A hA)

/-- The representative has exactly the class already classified by the dual point. -/
lemma dualPointFamily_class (stability : PicardZeroPullbackStatement.{u})
    {T : Over S} (p : T ⟶ dualScheme A hA) :
    RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
      (dualPointFamily A hA p) = (dualPointClass stability A hA p).val := rfl

/-- The actual representative satisfies the geometric Picard-zero condition. -/
lemma dualPointFamily_picardZero (stability : PicardZeroPullbackStatement.{u})
    {T : Over S} (p : T ⟶ dualScheme A hA) : IsPicardZeroFamily A (dualPointFamily A hA p) :=
  (dualPointClass stability A hA p).property

/-- The Poincaré representatives commute with parameter pullback up to the usual iso. -/
def dualPointFamilyPullbackIso {T U : Over S} (a : T ⟶ U)
    (p : U ⟶ dualScheme A hA) :
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      a).obj (dualPointFamily A hA p) ≅ dualPointFamily A hA (a ≫ p) :=
  (RigidifiedLineBundle.relativePullbackComp RigidifiedModule.pullbackCoherence
    A.X.hom (unitSection A) (unitSection_comp A) a p).app (poincareFamily A hA)

variable {A} {B : AbelianScheme S} (stability : PicardZeroPullbackStatement.{u})
variable (f : A ⟶ B) (hB : HasDualScheme B)

include stability in
/-- A dual point lies over the origin exactly when its actual homomorphism pullback
is trivial as a rigidified family. -/
lemma dualSchemeMap_eq_origin_iff {T : Over S} (p : T ⟶ dualScheme B hB) :
    p ≫ dualSchemeMap homPicardZeroPullback f hA hB =
        (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA ↔
      Nonempty ((homFamilyPullback f T).obj (dualPointFamily B hB p) ≅
        RigidifiedLineBundle.relativeTrivial A.X.hom (unitSection A)
          (unitSection_comp A) T) := by
  rw [← (dualPointClass_injective stability A hA T).eq_iff,
    dualPointClass_dualSchemeMap, dualPointClass_origin]
  rw [Subtype.ext_iff]
  exact Quotient.eq

/-- Choose an actual rigidified trivialization from the dual-kernel equation. -/
def dualKernelPullbackIso {T : Over S} (p : T ⟶ dualScheme B hB)
    (hp : p ≫ dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) :
    (homFamilyPullback f T).obj (dualPointFamily B hB p) ≅
      RigidifiedLineBundle.relativeTrivial A.X.hom (unitSection A)
        (unitSection_comp A) T :=
  Classical.choice ((dualSchemeMap_eq_origin_iff hA stability f hB p).mp hp)

/-- Forget rigidification to obtain the line-bundle trivialization on `T ×_S A`. -/
def dualKernelPullbackLineBundleIso {T : Over S} (p : T ⟶ dualScheme B hB)
    (hp : p ≫ dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) :
    (LineBundle.pullback ((homFamilySpaceMap f).app T)).obj
        ((RigidifiedLineBundle.forget _).obj (dualPointFamily B hB p)) ≅
      LineBundle.trivial ((relativeSpace A.X.hom).obj T) :=
  (RigidifiedLineBundle.forget _).mapIso (dualKernelPullbackIso hA stability f hB p hp)

/-- The same trivialization on the actual module sheaves. -/
def dualKernelPullbackModuleIso {T : Over S} (p : T ⟶ dualScheme B hB)
    (hp : p ≫ dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) :
    (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj
        (dualPointFamily B hB p).obj.carrier ≅
      structureSheaf ((relativeSpace A.X.hom).obj T) :=
  (LineBundle.forget _).mapIso (dualKernelPullbackLineBundleIso hA stability f hB p hp)

/-- The origin equation is stable under every change of parameter scheme. -/
lemma dualKernelPoint_restrict {T U : Over S} (a : T ⟶ U)
    (p : U ⟶ dualScheme B hB)
    (hp : p ≫ dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk U.hom : U ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) :
    (a ≫ p) ≫ dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA := by
  rw [Category.assoc, hp, ← Category.assoc]
  congr 1
  apply Over.OverMorphism.ext
  exact a.w

/-- Homomorphism pullback of the Poincaré representative commutes with parameter change. -/
def dualPointHomFamilyPullbackIso {T U : Over S} (a : T ⟶ U)
    (p : U ⟶ dualScheme B hB) :
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      a).obj ((homFamilyPullback f U).obj (dualPointFamily B hB p)) ≅
      (homFamilyPullback f T).obj (dualPointFamily B hB (a ≫ p)) :=
  (homFamilyPullbackNaturality RigidifiedModule.pullbackCoherence f a).app
      (dualPointFamily B hB p) ≪≫
    (homFamilyPullback f T).mapIso (dualPointFamilyPullbackIso B hB a p)

section GroupKernel

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
variable (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
  structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))

local notation "df" => Langlands.CommGroupScheme.groupHom
  (dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
    comparison symmetry stability hA hB MA evaluationA MB evaluationB f)

/-- Actual points of the scheme-theoretic dual kernel satisfy the required origin equation. -/
lemma dualKernelPoint_eq_origin (T : Over S)
    (x : T ⟶ (Langlands.GroupScheme.kernel df).X) :
    (x ≫ (Langlands.GroupScheme.kernelι df).hom.hom) ≫
        dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA := by
  have hx := (Langlands.GroupScheme.kernelPointsEquiv df T x).property
  change (x ≫ (Langlands.GroupScheme.kernelι df).hom.hom) ≫
      dualSchemeMap homPicardZeroPullback f hA hB =
    CategoryTheory.CartesianMonoidalCategory.toUnit T ≫
      ((Over.homMk (MonoidalCategory.tensorUnit (Over S)).hom :
        MonoidalCategory.tensorUnit (Over S) ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) at hx
  rw [← Category.assoc] at hx
  have ht : CategoryTheory.CartesianMonoidalCategory.toUnit T ≫
      (Over.homMk (MonoidalCategory.tensorUnit (Over S)).hom :
        MonoidalCategory.tensorUnit (Over S) ⟶ Over.mk (𝟙 S)) =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) := by
    apply Over.OverMorphism.ext
    exact (CategoryTheory.CartesianMonoidalCategory.toUnit T).w
  rwa [ht] at hx

/-- Rigidified pullback trivialization for an actual point of the dual group-scheme kernel. -/
def dualKernelPointPullbackIso (T : Over S)
    (x : T ⟶ (Langlands.GroupScheme.kernel df).X) :
    (homFamilyPullback f T).obj
        (dualPointFamily B hB (x ≫ (Langlands.GroupScheme.kernelι df).hom.hom)) ≅
      RigidifiedLineBundle.relativeTrivial A.X.hom (unitSection A)
        (unitSection_comp A) T :=
  dualKernelPullbackIso hA stability f hB _
    (dualKernelPoint_eq_origin hA stability f hB preservation composition unitCoherence
      associativity comparison symmetry MA evaluationA MB evaluationB T x)

/-- The actual module-sheaf trivialization needed by the intrinsic character construction. -/
def dualKernelPointPullbackModuleIso (T : Over S)
    (x : T ⟶ (Langlands.GroupScheme.kernel df).X) :
    (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj
        (dualPointFamily B hB (x ≫ (Langlands.GroupScheme.kernelι df).hom.hom)).obj.carrier ≅
      structureSheaf ((relativeSpace A.X.hom).obj T) :=
  dualKernelPullbackModuleIso hA stability f hB _
    (dualKernelPoint_eq_origin hA stability f hB preservation composition unitCoherence
      associativity comparison symmetry MA evaluationA MB evaluationB T x)

end GroupKernel

end Langlands.AbelianScheme
