import Langlands.AbelianScheme.KernelCharacterIndependence
import Langlands.AlgebraicGeometry.Modules.SquarePullbackComparison
import Langlands.GroupScheme.Cartier.RelativeHomFunctoriality

/-! # Test-scheme naturality of the intrinsic kernel character -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.GroupScheme.Cartier

/-- Restriction of actual characters preserves every evaluated global unit. -/
lemma characterHomRestrict_points {S : Scheme.{u}} (G : CommGroupScheme S)
    {T U : Over S} (b : U ⟶ T) (χ : CharacterHom G T) (V : Over U.left)
    (x : V ⟶ (testBaseChange U G).X) :
    Gm.pointsEquiv U.left V (x ≫ (characterHomRestrict G b χ).toMul.hom.hom) =
      Gm.pointsEquiv T.left ((Over.map b.left).obj V)
        (restrictPointsEquiv G b V x ≫ χ.toMul.hom.hom) := by
  have hx :
      baseChangePointsEquiv b.left (testBaseChange T G).toGrp V
          (x ≫ (baseChangeCompIso G b).hom.hom.hom) =
        restrictPointsEquiv G b V x := by
    apply Over.OverMorphism.ext
    simp only [baseChangePointsEquiv_left, Over.comp_left, Category.assoc,
      restrictPointsEquiv_left]
    change x.left ≫ (baseChangeCompIso G b).hom.hom.hom.left ≫
        pullback.fst (pullback.snd G.X.hom T.hom) b.left =
      x.left ≫ baseChangeProj G b
    rw [baseChangeCompIso_hom_fst]
  change Gm.pointsEquiv U.left V
    ((x ≫ (baseChangeCompIso G b).hom.hom.hom ≫
      ((GroupScheme.baseChange b.left).map χ.toMul).hom.hom) ≫
        (Gm.baseChangeIso b.left).hom.hom.hom) = _
  rw [Gm.pointsEquiv_baseChangeIso_hom, Gm.baseChangeUnitsEquiv_apply,
    ← Category.assoc]
  rw [baseChangePointsEquiv_comp b.left χ.toMul V
    (x ≫ (baseChangeCompIso G b).hom.hom.hom)]
  rw [hx]

end Langlands.GroupScheme.Cartier

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable {S : Scheme.{u}} {A B : AbelianScheme S} (f : A ⟶ B)

/-- Pull an actual homomorphism-pullback trivialization to a new test scheme. -/
def kernelCharacterPullbackTrivialization {U T : Over S} (b : U ⟶ T)
    {M : ((relativeSpace B.X.hom).obj T).Modules}
    (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj M ≅
      structureModule ((relativeSpace A.X.hom).obj T)) :
    (Scheme.Modules.pullback ((homFamilySpaceMap f).app U)).obj
        ((Scheme.Modules.pullback ((relativeSpace B.X.hom).map b)).obj M) ≅
      structureModule ((relativeSpace A.X.hom).obj U) :=
  squarePullbackIso ((homFamilySpaceMap f).app T) ((homFamilySpaceMap f).app U)
      ((relativeSpace A.X.hom).map b) ((relativeSpace B.X.hom).map b)
      ((homFamilySpaceMap f).naturality b).symm M ≪≫
    (Scheme.Modules.pullback ((relativeSpace A.X.hom).map b)).mapIso α ≪≫
      pullbackUnitIso ((relativeSpace A.X.hom).map b)

variable {T : Over S} {M : ((relativeSpace B.X.hom).obj T).Modules}
  (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj M ≅
    structureModule ((relativeSpace A.X.hom).obj T))

/-- Translation followed by a change of test scheme is translation over the composite. -/
lemma kernelShear_map {V U : Over S} (a : V ⟶ U) (b : U ⟶ T)
    (k : V ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelShear f a k ≫ (relativeSpace A.X.hom).map b =
      kernelShear f (a ≫ b) k := by
  simpa only [kernelShear_one, MonObj.comp_one, one_mul] using
    kernelShear_comp f a b k 1

/-- Pulling back the actual bundle and its trivialization preserves the action. -/
lemma kernelTranslationAut_pullback {V U : Over S} (b : U ⟶ T) (a : V ⟶ U)
    (k : V ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationAut f (kernelCharacterPullbackTrivialization f b α) a k =
      kernelTranslationAut f α (a ≫ b) k := by
  have hab :
      ((relativeSpace A.X.hom).map a ≫ (relativeSpace A.X.hom).map b) ≫
          (homFamilySpaceMap f).app T =
        (kernelShear f a k ≫ (relativeSpace A.X.hom).map b) ≫
          (homFamilySpaceMap f).app T := by
    rw [← (relativeSpace A.X.hom).map_comp, kernelShear_map]
    exact (kernelShear_homFamilySpaceMap f (a ≫ b) k).symm
  simpa only [kernelTranslationAut, kernelCharacterPullbackTrivialization,
      ← (relativeSpace A.X.hom).map_comp, kernelShear_map] using
    equalCompositeUnitAut_square ((homFamilySpaceMap f).app T)
      ((homFamilySpaceMap f).app U) ((relativeSpace A.X.hom).map b)
      ((relativeSpace B.X.hom).map b) ((homFamilySpaceMap f).naturality b).symm α
      ((relativeSpace A.X.hom).map a) (kernelShear f a k)
      (kernelShear_homFamilySpaceMap f a k).symm hab

/-- The actual global action scalar is unchanged by pulling back the bundle data. -/
lemma kernelTranslationScalar_pullback {V U : Over S} (b : U ⟶ T) (a : V ⟶ U)
    (k : V ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationScalar f (kernelCharacterPullbackTrivialization f b α) a k =
      kernelTranslationScalar f α (a ≫ b) k := by
  simp only [kernelTranslationScalar, kernelTranslationAut_pullback]

/-- The descended character values commute with change of test scheme. -/
lemma kernelTranslationUnit_pullback (h : UniversalGlobalFunctions A)
    {V U : Over S} (b : U ⟶ T) (a : V ⟶ U)
    (k : V ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationUnit f (kernelCharacterPullbackTrivialization f b α) h a k =
      kernelTranslationUnit f α h (a ≫ b) k := by
  simp only [kernelTranslationUnit, kernelTranslationScalar_pullback]

/-- The actual character homomorphism pulls back with the actual bundle. -/
lemma intrinsicKernelCharacterHom_pullback (h : UniversalGlobalFunctions A)
    {U : Over S} (b : U ⟶ T) :
    intrinsicKernelCharacterHom f (kernelCharacterPullbackTrivialization f b α) h =
      Cartier.characterHomRestrict (kernelCommGroupScheme f) b
        (intrinsicKernelCharacterHom f α h) := by
  apply Additive.toMul.injective
  apply hom_ext_points
  intro V k
  apply (Gm.pointsEquiv U.left V).injective
  rw [intrinsicKernelCharacterHom_points, Cartier.characterHomRestrict_points,
    intrinsicKernelCharacterHom_points, kernelTranslationUnit_pullback,
    Cartier.baseChangePointsEquiv_restrictPointsEquiv]
  have hp :
      (Cartier.restrictOverIso b V).hom ≫
          kernelCharacterParameter V ≫ b =
        kernelCharacterParameter ((Over.map b.left).obj V) := by
    ext
    simp [Cartier.restrictOverIso, kernelCharacterParameter]
  rw [← hp]
  simpa [Cartier.restrictOverIso] using
    (kernelTranslationUnit_precomp f α h (Cartier.restrictOverIso b V).hom
      (kernelCharacterParameter V ≫ b)
      (baseChangePointsEquiv U.hom (kernelCommGroupScheme f).toGrp V k)).symm

/-- The existing Cartier character commutes with change of test scheme. -/
lemma intrinsicKernelCharacter_pullback (h : UniversalGlobalFunctions A)
    {U : Over S} (b : U ⟶ T) :
    intrinsicKernelCharacter f (kernelCharacterPullbackTrivialization f b α) h =
      (Cartier.characters (kernelCommGroupScheme f)).map b.op
        (intrinsicKernelCharacter f α h) := by
  apply (Cartier.characterHomEquiv (kernelCommGroupScheme f) U).injective
  rw [characterHomEquiv_intrinsicKernelCharacter, Cartier.characterHomEquiv_restrict,
    characterHomEquiv_intrinsicKernelCharacter, intrinsicKernelCharacterHom_pullback]

/-- The character of a line bundle with trivial homomorphism pullback is natural. -/
lemma trivialHomPullbackCharacter_pullback (h : UniversalGlobalFunctions A)
    {U : Over S} (b : U ⟶ T)
    (L : LineBundle ((relativeSpace B.X.hom).obj T)) (hL : HasTrivialHomPullback f T L) :
    trivialHomPullbackCharacter f h
        ((LineBundle.pullback ((relativeSpace B.X.hom).map b)).obj L)
        (hasTrivialHomPullback_pullback f b L hL) =
      (Cartier.characters (kernelCommGroupScheme f)).map b.op
        (trivialHomPullbackCharacter f h L hL) := by
  calc
    _ = intrinsicKernelCharacter f
        (kernelCharacterPullbackTrivialization f b hL.some) h :=
      trivialHomPullbackCharacter_eq f h
        ((LineBundle.pullback ((relativeSpace B.X.hom).map b)).obj L)
        (hasTrivialHomPullback_pullback f b L hL)
        (kernelCharacterPullbackTrivialization f b hL.some)
    _ = _ := intrinsicKernelCharacter_pullback f hL.some h b

/-- Restriction of actual line-bundle classes commutes with the intrinsic character. -/
lemma trivialHomPullbackClassCharacter_restrict (h : UniversalGlobalFunctions A)
    {U : Over S} (b : U ⟶ T) (q : TrivialHomPullbackClasses f T) :
    trivialHomPullbackClassCharacter f h (trivialHomPullbackClassesRestrict f b q) =
      (Cartier.characters (kernelCommGroupScheme f)).map b.op
        (trivialHomPullbackClassCharacter f h q) := by
  refine Quotient.inductionOn q fun L ↦ ?_
  exact trivialHomPullbackCharacter_pullback f h b L.obj L.property

/-- The intrinsic character as a map from actual bundle classes to the existing
character presheaf, with only its carrier lifted to the input universe. -/
def trivialHomPullbackCharacterNatTrans (h : UniversalGlobalFunctions A) :
    trivialHomPullbackClassPresheaf f ⟶
      Cartier.characters (kernelCommGroupScheme f) ⋙
        forget AddCommGrpCat.{u} ⋙ uliftFunctor.{u + 1, u} where
  app T := TypeCat.ofHom (fun q ↦ ULift.up (trivialHomPullbackClassCharacter f h q))
  naturality T U b := by
    ext q
    exact congrArg ULift.up (trivialHomPullbackClassCharacter_restrict f h b.unop q)

@[simp]
lemma trivialHomPullbackCharacterNatTrans_classOf (h : UniversalGlobalFunctions A)
    (L : LineBundle ((relativeSpace B.X.hom).obj T)) (hL : HasTrivialHomPullback f T L) :
    ((trivialHomPullbackCharacterNatTrans f h).app (op T)
      (trivialHomPullbackClassOf f L hL)).down = trivialHomPullbackCharacter f h L hL :=
  rfl

end Langlands.AbelianScheme
