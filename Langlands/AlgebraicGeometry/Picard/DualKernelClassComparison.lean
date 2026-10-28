import Langlands.AlgebraicGeometry.Picard.DualKernelCharacter
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso

/-! # Actual dual-kernel points and trivial-pullback bundle classes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable {S : Scheme.{u}} {A B : AbelianScheme S} (f : A ⟶ B) {T : Over S}

/-- Restrict a trivial homomorphism pullback to the identity section to
rigidify the original line bundle without changing its underlying bundle. -/
def trivialHomPullbackRigidifiedFamily
    (L : LineBundle ((relativeSpace B.X.hom).obj T)) (hL : HasTrivialHomPullback f T L) :
    RigidifiedFamily B T :=
  RigidifiedLineBundle.ofLineBundle L
    ((pullbackUnitIso
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)).symm ≪≫
      (Scheme.Modules.pullback
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)).mapIso
          hL.some.symm ≪≫
      (Scheme.Modules.pullbackComp
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)
        ((homFamilySpaceMap f).app T)).app L.obj ≪≫
      (Scheme.Modules.pullbackCongr (relativeSection_homFamilySpaceMap f T)).app L.obj)

@[simp]
lemma trivialHomPullbackRigidifiedFamily_forget
    (L : LineBundle ((relativeSpace B.X.hom).obj T)) (hL : HasTrivialHomPullback f T L) :
    (RigidifiedLineBundle.forget _).obj (trivialHomPullbackRigidifiedFamily f L hL) = L := rfl

/-- The rigidified homomorphism pullback is also trivial as a rigidified family. -/
def trivialHomPullbackRigidifiedFamilyPullbackIso
    (L : LineBundle ((relativeSpace B.X.hom).obj T)) (hL : HasTrivialHomPullback f T L) :
    (homFamilyPullback f T).obj (trivialHomPullbackRigidifiedFamily f L hL) ≅
      RigidifiedLineBundle.relativeTrivial A.X.hom (unitSection A) (unitSection_comp A) T :=
  RigidifiedLineBundle.trivialIsoOfCarrierIso ((relativeProjection A.X.hom).app T)
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)
    (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) T)
    _ hL.some

variable (hA : HasDualScheme A) (stability : PicardZeroPullbackStatement.{u})
  (hB : HasDualScheme B)

include stability in
/-- Forgetting the rigidification of dual-kernel representatives loses no
information about their classifying dual point. -/
lemma dualKernelPullbackClass_injective (T : Over S)
    {p q : T ⟶ dualScheme B hB}
    (hp : p ≫ dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA)
    (hq : q ≫ dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA)
    (he : dualKernelPullbackClass hA stability f hB p hp =
      dualKernelPullbackClass hA stability f hB q hq)
    (preservation : pullbackTensorComparisonIsIsoStatement.{u}) : p = q := by
  obtain ⟨e⟩ := Quotient.exact he
  have e' := (trivialHomPullbackForget f T).mapIso e
  have er := RigidifiedLineBundle.isoOfCarrierIso preservation
    ((relativeProjection B.X.hom).app T)
    (relativeSection_projection B.X.hom (unitSection B) (unitSection_comp B) T)
    (L := dualPointFamily B hB p) (M := dualPointFamily B hB q)
    ((LineBundle.forget _).mapIso e')
  apply dualPointClass_injective stability B hB T
  apply Subtype.ext
  exact Quotient.sound ⟨er⟩

include stability in
/-- A geometric Picard-zero criterion lets every actual trivial-pullback bundle
class be represented by an actual dual point satisfying the origin equation. -/
lemma exists_dualKernelPullbackClass (T : Over S)
    (picardZero : ∀ L : RigidifiedFamily B T,
      HasTrivialHomPullback f T ((RigidifiedLineBundle.forget _).obj L) →
        IsPicardZeroFamily B L)
    (q : TrivialHomPullbackClasses f T) :
    ∃ (p : T ⟶ dualScheme B hB)
      (hp : p ≫ dualSchemeMap homPicardZeroPullback f hA hB =
        (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA),
      dualKernelPullbackClass hA stability f hB p hp = q := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  let M := trivialHomPullbackRigidifiedFamily f L.obj L.property
  have hM : IsPicardZeroFamily B M := picardZero M L.property
  let p := dualClassify B hB T
    ⟨RigidifiedLineBundle.classOf B.X.hom (unitSection B) (unitSection_comp B) M, hM⟩
  let e : dualPointFamily B hB p ≅ M := dualClassifyPullbackIso B hB M hM
  have hp : p ≫ dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA := by
    apply (dualSchemeMap_eq_origin_iff hA stability f hB p).mpr
    exact ⟨(homFamilyPullback f T).mapIso e ≪≫
      trivialHomPullbackRigidifiedFamilyPullbackIso f L.obj L.property⟩
  refine ⟨p, hp, ?_⟩
  exact trivialHomPullbackClassOf_eq_of_iso f
    ⟨dualKernelPullbackModuleIso hA stability f hB p hp⟩ L.property
    ((RigidifiedLineBundle.forget _).mapIso e)

section GroupKernel

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))

local notation "df" => Langlands.CommGroupScheme.groupHom
  (dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
    comparison symmetry stability hA hB MA evaluationA MB evaluationB f)

/-- Lift an actual origin equation to a point of the scheme-theoretic dual kernel. -/
def dualKernelPointOfOrigin (T : Over S) (p : T ⟶ dualScheme B hB)
    (hp : p ≫ dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) :
    T ⟶ (GroupScheme.kernel df).X :=
  (GroupScheme.kernelPointsEquiv df T).symm
    ⟨p, by
      change p ≫ dualSchemeMap homPicardZeroPullback f hA hB =
        CategoryTheory.CartesianMonoidalCategory.toUnit T ≫
          ((Over.homMk (MonoidalCategory.tensorUnit (Over S)).hom :
            MonoidalCategory.tensorUnit (Over S) ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA)
      rw [← Category.assoc]
      have ht : CategoryTheory.CartesianMonoidalCategory.toUnit T ≫
          (Over.homMk (MonoidalCategory.tensorUnit (Over S)).hom :
            MonoidalCategory.tensorUnit (Over S) ⟶ Over.mk (𝟙 S)) =
          (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) := by
        apply Over.OverMorphism.ext
        exact (CategoryTheory.CartesianMonoidalCategory.toUnit T).w
      rwa [ht]⟩

@[simp]
lemma dualKernelPointOfOrigin_ι (T : Over S) (p : T ⟶ dualScheme B hB)
    (hp : p ≫ dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) :
    dualKernelPointOfOrigin f hA stability hB preservation composition unitCoherence
        associativity comparison symmetry MA evaluationA MB evaluationB T p hp ≫
      (GroupScheme.kernelι df).hom.hom = p := by
  exact congrArg Subtype.val ((GroupScheme.kernelPointsEquiv df T).apply_symm_apply ⟨p, _⟩)

/-- Send an actual scheme-theoretic dual-kernel point to its Poincaré bundle class. -/
def dualKernelPointPullbackClass (T : Over S)
    (x : T ⟶ (GroupScheme.kernel df).X) : TrivialHomPullbackClasses f T :=
  dualKernelPullbackClass hA stability f hB (x ≫ (GroupScheme.kernelι df).hom.hom)
    (dualKernelPoint_eq_origin hA stability f hB preservation composition unitCoherence
      associativity comparison symmetry MA evaluationA MB evaluationB T x)

/-- The actual character is exactly the existing class character of this representative. -/
lemma dualKernelPointCharacter_eq_classCharacter (T : Over S)
    (x : T ⟶ (GroupScheme.kernel df).X) :
    dualKernelPointCharacter hA stability f hB preservation composition unitCoherence
        associativity comparison symmetry MA evaluationA MB evaluationB T x =
      trivialHomPullbackClassCharacter f (universalGlobalFunctions A)
        (dualKernelPointPullbackClass f hA stability hB preservation composition unitCoherence
          associativity comparison symmetry MA evaluationA MB evaluationB T x) := rfl

include preservation in
/-- Actual dual-kernel points are determined by their unrigidified Poincaré classes. -/
lemma dualKernelPointPullbackClass_injective (T : Over S) :
    Function.Injective
      (dualKernelPointPullbackClass f hA stability hB preservation composition unitCoherence
        associativity comparison symmetry MA evaluationA MB evaluationB T) := by
  intro x y he
  apply (cancel_mono (GroupScheme.kernelι df).hom.hom).mp
  exact dualKernelPullbackClass_injective f hA stability hB T _ _ he preservation

/-- Under an explicit geometric Picard-zero criterion, the actual class map is
surjective on every bundle class at the specified parameter scheme. -/
lemma dualKernelPointPullbackClass_surjective (T : Over S)
    (picardZero : ∀ L : RigidifiedFamily B T,
      HasTrivialHomPullback f T ((RigidifiedLineBundle.forget _).obj L) →
        IsPicardZeroFamily B L) :
    Function.Surjective
      (dualKernelPointPullbackClass f hA stability hB preservation composition unitCoherence
        associativity comparison symmetry MA evaluationA MB evaluationB T) := by
  intro q
  obtain ⟨p, hp, he⟩ := exists_dualKernelPullbackClass f hA stability hB T picardZero q
  refine ⟨dualKernelPointOfOrigin f hA stability hB preservation composition unitCoherence
    associativity comparison symmetry MA evaluationA MB evaluationB T p hp, ?_⟩
  dsimp only [dualKernelPointPullbackClass]
  simpa only [dualKernelPointOfOrigin_ι] using he

/-- The comparison is an actual equivalence once the geometric Picard-zero
criterion is proved; no character or descent equivalence is chosen. -/
def dualKernelPointPullbackClassEquiv (T : Over S)
    (picardZero : ∀ L : RigidifiedFamily B T,
      HasTrivialHomPullback f T ((RigidifiedLineBundle.forget _).obj L) →
        IsPicardZeroFamily B L) :
    (T ⟶ (GroupScheme.kernel df).X) ≃ TrivialHomPullbackClasses f T :=
  Equiv.ofBijective
    (dualKernelPointPullbackClass f hA stability hB preservation composition unitCoherence
      associativity comparison symmetry MA evaluationA MB evaluationB T)
    ⟨dualKernelPointPullbackClass_injective f hA stability hB preservation composition
        unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB T,
      dualKernelPointPullbackClass_surjective f hA stability hB preservation composition
        unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB T
        picardZero⟩

/-- Bijectivity of the two explicit comparison maps implies bijectivity of the
specific existing normalized dual-kernel character. The geometric and descent
proofs remain explicit hypotheses of this intermediate assembly lemma. -/
lemma dualKernelPointCharacter_bijective_of_classification (T : Over S)
    (picardZero : ∀ L : RigidifiedFamily B T,
      HasTrivialHomPullback f T ((RigidifiedLineBundle.forget _).obj L) →
        IsPicardZeroFamily B L)
    (classification : Function.Bijective
      (trivialHomPullbackClassCharacter f (T := T) (universalGlobalFunctions A))) :
    Function.Bijective
      (dualKernelPointCharacter hA stability f hB preservation composition unitCoherence
        associativity comparison symmetry MA evaluationA MB evaluationB T) :=
  classification.comp
    (dualKernelPointPullbackClassEquiv f hA stability hB preservation composition unitCoherence
      associativity comparison symmetry MA evaluationA MB evaluationB T picardZero).bijective

end GroupKernel

end Langlands.AbelianScheme
