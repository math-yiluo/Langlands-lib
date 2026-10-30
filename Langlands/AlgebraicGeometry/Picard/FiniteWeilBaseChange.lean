import Langlands.AlgebraicGeometry.Picard.DualBaseChangeClasses
import Langlands.AbelianScheme.Tate.WeilIntegral
import Langlands.AbelianScheme.Tate.IntegralBaseChange
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeEquivalence
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeNaturality
import Langlands.AlgebraicGeometry.Picard.DualSchemeBaseChange
import Langlands.AlgebraicGeometry.Picard.FiniteWeilTransitionProof
import Langlands.AlgebraicGeometry.Picard.FiniteWeilFunctorialityProof

/-! # Ground base change of the actual finite Weil pairing -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

section Space

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {A B : AbelianScheme S}

/-- Shear maps commute with the comparison of relative spaces across ground base change. -/
lemma shear_familyBaseChangeSpaceMap {U T : Over S'} (a : U ⟶ T)
    (c : U ⟶ ((baseChange b).obj A).X) :
    shear ((baseChange b).obj A) a c ≫ familyBaseChangeSpaceMap b A T =
      familyBaseChangeSpaceMap b A U ≫
        shear A ((Over.map b).map a) (baseChangePointsEquiv b A.toGrp U c) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, familyBaseChangeSpaceMap_fst, shear_fst,
      familyBaseChangeSpaceMap_fst_assoc]
    rfl
  · rw [Category.assoc, familyBaseChangeSpaceMap_snd, shear_snd_assoc, Category.assoc,
      shear_snd]
    let m : (Over.map b).obj (relativeOver ((baseChange b).obj A) U) ⟶
        relativeOver A ((Over.map b).obj U) :=
      Over.homMk (familyBaseChangeSpaceMap b A U) (by
        change familyBaseChangeSpaceMap b A U ≫
            pullback.fst ((Over.map b).obj U).hom A.X.hom ≫ (U.hom ≫ b) = _
        rw [familyBaseChangeSpaceMap_fst_assoc]
        exact (Category.assoc _ _ _).symm)
    have hm₁ : m ≫ relativeFst A ((Over.map b).obj U) =
        (Over.map b).map (relativeFst ((baseChange b).obj A) U) := by
      ext
      exact familyBaseChangeSpaceMap_fst b A U
    have hm₂ : m ≫ relativeSnd A ((Over.map b).obj U) =
        baseChangePointsEquiv b A.toGrp _ (relativeSnd ((baseChange b).obj A) U) := by
      ext
      exact familyBaseChangeSpaceMap_snd b A U
    change (baseChangePointsEquiv b A.toGrp _
        ((relativeFst ((baseChange b).obj A) U ≫ c) *
          relativeSnd ((baseChange b).obj A) U)).left =
      (m ≫ ((relativeFst A ((Over.map b).obj U) ≫ baseChangePointsEquiv b A.toGrp U c) *
        relativeSnd A ((Over.map b).obj U))).left
    rw [map_mul, MonObj.comp_mul, reassoc_of% hm₁, hm₂, baseChangePointsEquiv_naturality]

variable (f : A ⟶ B) (f' : (baseChange b).obj A ⟶ (baseChange b).obj B)
  (hf : hom f' ≫ pullback.fst B.X.hom b = pullback.fst A.X.hom b ≫ hom f)

include hf in
/-- Homomorphism family maps commute with the comparison of relative spaces. -/
lemma homFamilySpaceMap_familyBaseChangeSpaceMap (T : Over S') :
    (homFamilySpaceMap f').app T ≫ familyBaseChangeSpaceMap b B T =
      familyBaseChangeSpaceMap b A T ≫ (homFamilySpaceMap f).app ((Over.map b).obj T) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, familyBaseChangeSpaceMap_fst, homFamilySpaceMap_fst]
  · simp only [Category.assoc, familyBaseChangeSpaceMap_snd, homFamilySpaceMap_snd,
      homFamilySpaceMap_snd_assoc, familyBaseChangeSpaceMap_snd_assoc, hf]

/-- Translation by a kernel point of `f'` lies over translation by the corresponding kernel
point of `f`. -/
lemma kernelShear_familyBaseChangeSpaceMap {U T : Over S'} (a : U ⟶ T)
    (k' : U ⟶ (GroupScheme.kernel (groupHom f')).X)
    (k : (Over.map b).obj U ⟶ (GroupScheme.kernel (groupHom f)).X)
    (hk : k ≫ (GroupScheme.kernelι (groupHom f)).hom.hom =
      baseChangePointsEquiv b A.toGrp U (k' ≫ (GroupScheme.kernelι (groupHom f')).hom.hom)) :
    kernelShear f' a k' ≫ familyBaseChangeSpaceMap b A T =
      familyBaseChangeSpaceMap b A U ≫ kernelShear f ((Over.map b).map a) k := by
  rw [kernelShear, shear_familyBaseChangeSpaceMap, kernelShear, hk]

/-- Base units pulled back to `U ×_S A` and then to `U ×_{S'} A_{S'}` are base units. -/
lemma relativeUnitsPullback_familyBaseChangeSpaceMap (U : Over S') (c : Γ(U.left, ⊤)ˣ) :
    Units.map (familyBaseChangeSpaceMap b A U).appTop.hom.toMonoidHom
        (relativeUnitsPullback A ((Over.map b).obj U) c) =
      relativeUnitsPullback ((baseChange b).obj A) U c := by
  have he := congrArg Scheme.Hom.appTop (familyBaseChangeSpaceMap_fst b A U)
  rw [Scheme.Hom.comp_appTop] at he
  apply Units.ext
  exact congrArg (fun m ↦ m (c : Γ(U.left, ⊤))) he

variable {T : Over S'} {M : ((relativeSpace B.X.hom).obj ((Over.map b).obj T)).Modules}
  (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app ((Over.map b).obj T))).obj M ≅
    structureModule ((relativeSpace A.X.hom).obj ((Over.map b).obj T)))

/-- Transport a trivialization of `f^* M` over `T ×_S A` to the base-changed family. -/
def familyBaseChangeKernelTrivialization :
    (Scheme.Modules.pullback ((homFamilySpaceMap f').app T)).obj
        ((Scheme.Modules.pullback (familyBaseChangeSpaceMap b B T)).obj M) ≅
      structureModule ((relativeSpace ((baseChange b).obj A).X.hom).obj T) :=
  squarePullbackIso ((homFamilySpaceMap f).app ((Over.map b).obj T))
      ((homFamilySpaceMap f').app T) (familyBaseChangeSpaceMap b A T)
      (familyBaseChangeSpaceMap b B T)
      (homFamilySpaceMap_familyBaseChangeSpaceMap b f f' hf T) M ≪≫
    (Scheme.Modules.pullback (familyBaseChangeSpaceMap b A T)).mapIso α ≪≫
      pullbackUnitIso (familyBaseChangeSpaceMap b A T)

/-- The transported kernel action after base change is the pullback of the original one. -/
lemma kernelTranslationAut_familyBaseChange {U : Over S'} (a : U ⟶ T)
    (k' : U ⟶ (GroupScheme.kernel (groupHom f')).X)
    (k : (Over.map b).obj U ⟶ (GroupScheme.kernel (groupHom f)).X)
    (hk : k ≫ (GroupScheme.kernelι (groupHom f)).hom.hom =
      baseChangePointsEquiv b A.toGrp U (k' ≫ (GroupScheme.kernelι (groupHom f')).hom.hom)) :
    kernelTranslationAut f' (familyBaseChangeKernelTrivialization b f f' hf α) a k' =
      structureAutPullback (familyBaseChangeSpaceMap b A U)
        (kernelTranslationAut f α ((Over.map b).map a) k) := by
  have ha : (relativeSpace ((baseChange b).obj A).X.hom).map a ≫
        familyBaseChangeSpaceMap b A T =
      familyBaseChangeSpaceMap b A U ≫ (relativeSpace A.X.hom).map ((Over.map b).map a) :=
    familyBaseChangeSpaceMap_naturality b A a
  have hk' := kernelShear_familyBaseChangeSpaceMap b f f' a k' k hk
  have hab : ((relativeSpace ((baseChange b).obj A).X.hom).map a ≫
        familyBaseChangeSpaceMap b A T) ≫ (homFamilySpaceMap f).app ((Over.map b).obj T) =
      (kernelShear f' a k' ≫ familyBaseChangeSpaceMap b A T) ≫
        (homFamilySpaceMap f).app ((Over.map b).obj T) := by
    rw [ha, hk', Category.assoc, Category.assoc,
      kernelShear_homFamilySpaceMap f ((Over.map b).map a) k]
  have hab' : (familyBaseChangeSpaceMap b A U ≫
        (relativeSpace A.X.hom).map ((Over.map b).map a)) ≫
        (homFamilySpaceMap f).app ((Over.map b).obj T) =
      (familyBaseChangeSpaceMap b A U ≫ kernelShear f ((Over.map b).map a) k) ≫
        (homFamilySpaceMap f).app ((Over.map b).obj T) := by
    rw [Category.assoc, Category.assoc, kernelShear_homFamilySpaceMap]
  unfold kernelTranslationAut structureAutPullback familyBaseChangeKernelTrivialization
  rw [equalCompositeUnitAut_square _ _ _ _ _ α _ _ _ hab,
    equalCompositeUnitAut_congr _ ha hk' hab hab',
    equalCompositeUnitAut_precomp ((homFamilySpaceMap f).app ((Over.map b).obj T))
      ((relativeSpace A.X.hom).map ((Over.map b).map a)) (kernelShear f ((Over.map b).map a) k)
      α (familyBaseChangeSpaceMap b A U)
      (kernelShear_homFamilySpaceMap f ((Over.map b).map a) k).symm hab']

/-- The corresponding global scalars agree after pullback along the space comparison. -/
lemma kernelTranslationScalar_familyBaseChange {U : Over S'} (a : U ⟶ T)
    (k' : U ⟶ (GroupScheme.kernel (groupHom f')).X)
    (k : (Over.map b).obj U ⟶ (GroupScheme.kernel (groupHom f)).X)
    (hk : k ≫ (GroupScheme.kernelι (groupHom f)).hom.hom =
      baseChangePointsEquiv b A.toGrp U (k' ≫ (GroupScheme.kernelι (groupHom f')).hom.hom)) :
    kernelTranslationScalar f' (familyBaseChangeKernelTrivialization b f f' hf α) a k' =
      Units.map (familyBaseChangeSpaceMap b A U).appTop.hom.toMonoidHom
        (kernelTranslationScalar f α ((Over.map b).map a) k) := by
  rw [kernelTranslationScalar, kernelTranslationAut_familyBaseChange b f f' hf α a k' k hk,
    structureAutScalar_pullback, kernelTranslationScalar]

/-- The descended units on the common parameter scheme agree. -/
lemma kernelTranslationUnit_familyBaseChange {U : Over S'} (a : U ⟶ T)
    (k' : U ⟶ (GroupScheme.kernel (groupHom f')).X)
    (k : (Over.map b).obj U ⟶ (GroupScheme.kernel (groupHom f)).X)
    (hk : k ≫ (GroupScheme.kernelι (groupHom f)).hom.hom =
      baseChangePointsEquiv b A.toGrp U (k' ≫ (GroupScheme.kernelι (groupHom f')).hom.hom)) :
    kernelTranslationUnit f' (familyBaseChangeKernelTrivialization b f f' hf α)
        (universalGlobalFunctions _) a k' =
      kernelTranslationUnit f α (universalGlobalFunctions A) ((Over.map b).map a) k := by
  apply relativeUnitsPullback_injective _ (universalGlobalFunctions _) U
  rw [relativeUnitsPullback_kernelTranslationUnit,
    kernelTranslationScalar_familyBaseChange b f f' hf α a k' k hk,
    ← relativeUnitsPullback_kernelTranslationUnit f α (universalGlobalFunctions A),
    relativeUnitsPullback_familyBaseChangeSpaceMap]

/-- Evaluation of the transported intrinsic character at a point of the base-changed kernel
is evaluation of the original intrinsic character at the corresponding point. -/
lemma intrinsicKernelCharacter_evaluation_familyBaseChange
    (x' : T ⟶ (kernelCommGroupScheme f').X)
    (x : (Over.map b).obj T ⟶ (kernelCommGroupScheme f).X)
    (hx : x ≫ (GroupScheme.kernelι (groupHom f)).hom.hom =
      baseChangePointsEquiv b A.toGrp T (x' ≫ (GroupScheme.kernelι (groupHom f')).hom.hom)) :
    Gm.pointsEquiv S' T (Cartier.characterEvaluation
        (intrinsicKernelCharacter f' (familyBaseChangeKernelTrivialization b f f' hf α)
          (universalGlobalFunctions _)) x') =
      Gm.pointsEquiv S ((Over.map b).obj T) (Cartier.characterEvaluation
        (intrinsicKernelCharacter f α (universalGlobalFunctions A)) x) := by
  rw [← Cartier.characterEvaluation_section, ← Cartier.characterEvaluation_section,
    characterHomEquiv_intrinsicKernelCharacter, characterHomEquiv_intrinsicKernelCharacter,
    intrinsicKernelCharacterHom_points, intrinsicKernelCharacterHom_points,
    baseChangePointsEquiv_sectionPointsEquiv_symm,
    baseChangePointsEquiv_sectionPointsEquiv_symm]
  let c : (Over.map ((Over.map b).obj T).hom).obj (Over.mk (𝟙 ((Over.map b).obj T).left)) ⟶
      (Over.map b).obj ((Over.map T.hom).obj (Over.mk (𝟙 T.left))) :=
    Over.homMk (𝟙 T.left) (by simp)
  have hca : c ≫ (Over.map b).map (kernelCharacterParameter (T := T) (Over.mk (𝟙 T.left))) =
      kernelCharacterParameter (T := (Over.map b).obj T)
        (Over.mk (𝟙 ((Over.map b).obj T).left)) := by
    ext
    simp [c, kernelCharacterParameter]
  have hcs : c ≫ (Over.map b).map (Cartier.sectionBaseIso T).hom =
      (Cartier.sectionBaseIso ((Over.map b).obj T)).hom := by
    ext
    simp [c, Cartier.sectionBaseIso]
  rw [kernelTranslationUnit_familyBaseChange b f f' hf α _ _
      ((Over.map b).map (Cartier.sectionBaseIso T).hom ≫ x) (by
        rw [Category.assoc, hx, ← baseChangePointsEquiv_naturality, Category.assoc]),
    ← hca, ← hcs, Category.assoc, kernelTranslationUnit_precomp]
  simp [c]

end Space

section DualPoint

variable (universality : PicardZeroUniversalBaseChangeStatement.{u})
  {S S' : Scheme.{u}} (b : S' ⟶ S) (B : AbelianScheme S) (hB : HasDualScheme B)
  (hB' : HasDualScheme ((baseChange b).obj B))

/-- The dual point over the old base corresponding to a point of the dual of the base change,
through the canonical comparison `dualSchemeBaseChangeIso`. -/
def dualPointBaseChange {T : Over S'} (p' : T ⟶ dualScheme ((baseChange b).obj B) hB') :
    (Over.map b).obj T ⟶ dualScheme B hB :=
  baseChangeParameterMate b (p' ≫ (dualSchemeBaseChangeIso universality b B hB hB').inv)

/-- The Poincaré representative of a dual point of the base change is the ground base change
of the representative of the corresponding old dual point. -/
def dualPointFamilyBaseChangeIso {T : Over S'}
    (p' : T ⟶ dualScheme ((baseChange b).obj B) hB') :
    dualPointFamily ((baseChange b).obj B) hB' p' ≅
      (familyBaseChange b B T).obj
        (dualPointFamily B hB (dualPointBaseChange universality b B hB hB' p')) :=
  eqToIso (congrArg (dualPointFamily ((baseChange b).obj B) hB')
      (by simp : p' = (p' ≫ (dualSchemeBaseChangeIso universality b B hB hB').inv) ≫
        (dualSchemeBaseChangeIso universality b B hB hB').hom)) ≪≫
    (dualPointFamilyPullbackIso ((baseChange b).obj B) hB'
      (p' ≫ (dualSchemeBaseChangeIso universality b B hB hB').inv)
      (dualSchemeBaseChangeIso universality b B hB hB').hom).symm ≪≫
    (RigidifiedLineBundle.relativePullback ((baseChange b).obj B).X.hom
      (unitSection ((baseChange b).obj B)) (unitSection_comp _)
      (p' ≫ (dualSchemeBaseChangeIso universality b B hB hB').inv)).mapIso
        (dualSchemeBaseChangePullbackIso universality b B hB hB') ≪≫
    (baseChangeFamilyPullbackIso b B
      (p' ≫ (dualSchemeBaseChangeIso universality b B hB hB').inv)).app (poincareFamily B hB)

variable (stability : PicardZeroPullbackStatement.{u}) {A : AbelianScheme S}
  (hA : HasDualScheme A) (hA' : HasDualScheme ((baseChange b).obj A))
  (f : A ⟶ B) (f' : (baseChange b).obj A ⟶ (baseChange b).obj B)
  (hf : hom f' ≫ pullback.fst B.X.hom b = pullback.fst A.X.hom b ≫ hom f)

include hf in
/-- The dual-kernel character of a dual point of the base change, evaluated at a kernel point,
is the dual-kernel character of the corresponding old dual point at the corresponding old
kernel point. -/
lemma dualKernelCharacter_evaluation_familyBaseChange {T : Over S'}
    (p' : T ⟶ dualScheme ((baseChange b).obj B) hB')
    (hp' : p' ≫ dualSchemeMap homPicardZeroPullback f' hA' hB' =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S')) ≫ dualOrigin ((baseChange b).obj A) hA')
    (hp : dualPointBaseChange universality b B hB hB' p' ≫
        dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk ((Over.map b).obj T).hom : (Over.map b).obj T ⟶ Over.mk (𝟙 S)) ≫
        dualOrigin A hA)
    (x' : T ⟶ (kernelCommGroupScheme f').X)
    (x : (Over.map b).obj T ⟶ (kernelCommGroupScheme f).X)
    (hx : x ≫ (GroupScheme.kernelι (groupHom f)).hom.hom =
      baseChangePointsEquiv b A.toGrp T (x' ≫ (GroupScheme.kernelι (groupHom f')).hom.hom)) :
    Gm.pointsEquiv S' T (Cartier.characterEvaluation
        (dualKernelCharacter hA' stability f' hB' p' hp') x') =
      Gm.pointsEquiv S ((Over.map b).obj T) (Cartier.characterEvaluation
        (dualKernelCharacter hA stability f hB
          (dualPointBaseChange universality b B hB hB' p') hp) x) := by
  rw [dualKernelCharacter_eq_of_iso hA' stability f' hB' p' hp'
      ((RigidifiedLineBundle.forget _ ⋙ LineBundle.forget _).mapIso
        (dualPointFamilyBaseChangeIso universality b B hB hB' p'))
      (familyBaseChangeKernelTrivialization b f f' hf
        (dualKernelPullbackModuleIso hA stability f hB _ hp)),
    dualKernelCharacter_eq_intrinsic hA stability f hB _ hp
      (dualKernelPullbackModuleIso hA stability f hB _ hp)]
  exact intrinsicKernelCharacter_evaluation_familyBaseChange b f f' hf _ x' x hx

end DualPoint

/-- An isomorphism of commutative group objects identifies the actual torsion levels. -/
def levelEquivOfIso {S : Scheme.{u}} {G H : Grp (Over S)} [IsCommMonObj G.X]
    [IsCommMonObj H.X] (E : G ≅ H) (T : Over S) (n : ℕ) :
    GroupScheme.Tate.Level G T n ≃+ GroupScheme.Tate.Level H T n where
  toFun := GroupScheme.Tate.levelMap T E.hom n
  invFun := GroupScheme.Tate.levelMap T E.inv n
  left_inv x := by
    apply GroupScheme.Tate.toSection_injective G T n
    change ((Additive.toMul x).val ≫ E.hom.hom.hom) ≫ E.inv.hom.hom = (Additive.toMul x).val
    rw [Category.assoc, ← Grp.comp_hom_hom, E.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  right_inv y := by
    apply GroupScheme.Tate.toSection_injective H T n
    change ((Additive.toMul y).val ≫ E.inv.hom.hom) ≫ E.hom.hom.hom = (Additive.toMul y).val
    rw [Category.assoc, ← Grp.comp_hom_hom, E.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  map_add' := map_add _

section DualLevel

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (hA : HasDualScheme A)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (hA' : HasDualScheme ((baseChange b).obj A))
  (MA' : LineBundle ((relativeSpace ((baseChange b).obj A).X.hom).obj
    (dualScheme ((baseChange b).obj A) hA')))
  (evaluationA' : tensorObj (poincareFamily ((baseChange b).obj A) hA').obj.carrier
    MA'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj A).X.hom).obj
      (dualScheme ((baseChange b).obj A) hA')))

local notation "GA" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry
set_option quotPrecheck false in
local notation "GAb" => dualCommGroupSchemeFromEvaluation ((baseChange b).obj A) hA'
  preservation MA' evaluationA' stability composition unitCoherence associativity comparison
  symmetry
local notation "eD" => dualSchemeBaseChangeIso universality b A hA hA'

/-- The canonical comparison is multiplicative for the actual dual group laws. -/
lemma dualSchemeBaseChangeIso_hom_mul (T : Over S')
    (p q : T ⟶ ((Over.pullback b).mapGrp.obj (Langlands.CommGroupScheme.toGrp GA)).X) :
    ((p * q) ≫ (eD).hom : T ⟶ (GAb).X) =
      (p ≫ (eD).hom : T ⟶ (GAb).X) * (q ≫ (eD).hom : T ⟶ (GAb).X) := by
  let := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
    symmetry A ((Over.map b).obj T)
  let := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
    symmetry ((baseChange b).obj A) T
  let := RigidifiedLineBundle.classesCommMonoid preservation unitCoherence associativity
    comparison symmetry A.X.hom (unitSection A) (unitSection_comp A) ((Over.map b).obj T)
  let := RigidifiedLineBundle.classesCommMonoid preservation unitCoherence associativity
    comparison symmetry ((baseChange b).obj A).X.hom (unitSection ((baseChange b).obj A))
    (unitSection_comp _) T
  let F : (T ⟶ ((Over.pullback b).mapGrp.obj (Langlands.CommGroupScheme.toGrp GA)).X) →*
      RigidifiedClasses A ((Over.map b).obj T) :=
    (picardZeroInclusionMonoidHom preservation unitCoherence associativity comparison symmetry
      A ((Over.map b).obj T)).comp
      ((dualCommGroupSchemePointMulEquiv A hA preservation MA evaluationA stability
        composition unitCoherence associativity comparison symmetry
        ((Over.map b).obj T)).toMonoidHom.comp
        (GroupScheme.baseChangePointsEquiv b (Langlands.CommGroupScheme.toGrp GA) T).toMonoidHom)
  let G : (T ⟶ (GAb).X) →* RigidifiedClasses ((baseChange b).obj A) T :=
    (picardZeroInclusionMonoidHom preservation unitCoherence associativity comparison symmetry
      ((baseChange b).obj A) T).comp
      (dualCommGroupSchemePointMulEquiv ((baseChange b).obj A) hA' preservation
        MA' evaluationA' stability composition unitCoherence associativity comparison
        symmetry T).toMonoidHom
  have hG : Function.Injective G :=
    Subtype.val_injective.comp (dualCommGroupSchemePointMulEquiv ((baseChange b).obj A) hA'
      preservation MA' evaluationA' stability composition unitCoherence associativity
      comparison symmetry T).injective
  have hc (x : T ⟶ ((Over.pullback b).mapGrp.obj (Langlands.CommGroupScheme.toGrp GA)).X) :
      G (x ≫ (eD).hom) = rigidifiedClassesBaseChange b A T (F x) :=
    dualPointClass_dualSchemeBaseChangeIso b A stability universality hA hA' x
  apply hG
  rw [map_mul, hc, hc, hc, map_mul]
  exact rigidifiedClassesBaseChange_tensor b A preservation composition unitCoherence.1 T
    (F p) (F q)

/-- The canonical comparison as an isomorphism of actual group objects. -/
def dualGrpBaseChangeIso :
    (Over.pullback b).mapGrp.obj (Langlands.CommGroupScheme.toGrp GA) ≅
      Langlands.CommGroupScheme.toGrp GAb := by
  have hmul := dualSchemeBaseChangeIso_hom_mul b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA MA evaluationA hA' MA'
    evaluationA'
  let e : ((Over.pullback b).mapGrp.obj (Langlands.CommGroupScheme.toGrp GA)).X ≅
      (Langlands.CommGroupScheme.toGrp GAb).X := eD
  have hone : η[((Over.pullback b).mapGrp.obj (Langlands.CommGroupScheme.toGrp GA)).X] ≫
      e.hom = η[(Langlands.CommGroupScheme.toGrp GAb).X] := by
    have h := hmul (MonoidalCategory.tensorUnit (Over S')) 1 1
    rw [mul_one] at h
    have h1 := left_eq_mul.mp h
    simpa only [CategoryTheory.Hom.one_def,
      CartesianMonoidalCategory.toUnit_unique
        (CartesianMonoidalCategory.toUnit (MonoidalCategory.tensorUnit (Over S'))) (𝟙 _),
      Category.id_comp] using h1
  have hprod : μ[((Over.pullback b).mapGrp.obj (Langlands.CommGroupScheme.toGrp GA)).X] ≫
      e.hom = MonoidalCategory.tensorHom e.hom e.hom ≫
        μ[(Langlands.CommGroupScheme.toGrp GAb).X] := by
    have h := hmul _
      (CartesianMonoidalCategory.fst
        ((Over.pullback b).mapGrp.obj (Langlands.CommGroupScheme.toGrp GA)).X
        ((Over.pullback b).mapGrp.obj (Langlands.CommGroupScheme.toGrp GA)).X)
      (CartesianMonoidalCategory.snd
        ((Over.pullback b).mapGrp.obj (Langlands.CommGroupScheme.toGrp GA)).X
        ((Over.pullback b).mapGrp.obj (Langlands.CommGroupScheme.toGrp GA)).X)
    simpa only [CategoryTheory.Hom.mul_def, CartesianMonoidalCategory.lift_fst_snd,
      Category.id_comp, CartesianMonoidalCategory.lift_fst_comp_snd_comp] using h
  exact Grp.mkIso e hone hprod

/-- The canonical identification of actual dual torsion before and after ground base change. -/
def dualLevelBaseChange (T : Over S') (n : ℕ) :
    GroupScheme.Tate.Level (Langlands.CommGroupScheme.toGrp GAb) T n ≃+
      GroupScheme.Tate.Level (Langlands.CommGroupScheme.toGrp GA) ((Over.map b).obj T) n :=
  (levelEquivOfIso (dualGrpBaseChangeIso b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA MA evaluationA hA' MA'
    evaluationA').symm T n).trans
    (GroupScheme.Tate.levelBaseChange b (Langlands.CommGroupScheme.toGrp GA) T n)

/-- On underlying dual points it is the comparison `dualPointBaseChange`. -/
lemma toSection_dualLevelBaseChange (T : Over S') (n : ℕ)
    (y : GroupScheme.Tate.Level (Langlands.CommGroupScheme.toGrp GAb) T n) :
    Additive.toMul (GroupScheme.Tate.toSection _ ((Over.map b).obj T) n
        (dualLevelBaseChange b A preservation composition unitCoherence associativity
          comparison symmetry stability universality hA MA evaluationA hA' MA'
          evaluationA' T n y)) =
      dualPointBaseChange universality b A hA hA'
        (Additive.toMul (GroupScheme.Tate.toSection _ T n y)) := by
  apply Over.OverMorphism.ext
  rfl

/-- Multiplication on the base change lies over multiplication on `A`. -/
lemma hom_multiplication_baseChange_fst (n : ℤ) :
    hom (multiplication ((baseChange b).obj A) n) ≫ pullback.fst A.X.hom b =
      pullback.fst A.X.hom b ≫ hom (multiplication A n) := by
  change (GroupScheme.multiplication ((Over.pullback b).mapGrp.obj A.toGrp) n).hom.hom.left ≫
    _ = _
  rw [← GroupScheme.multiplication_baseChange b A.toGrp n]
  simp

variable [QuasiSeparatedSpace S]

/-- Points of actual dual torsion satisfy the dual-kernel equation of `[n]`. -/
lemma torsion_dualSchemeMap_eq_origin (n : ℕ) {T : Over S}
    (y : T ⟶ (GroupScheme.torsion (Langlands.CommGroupScheme.toGrp GA) (n : ℤ)).X) :
    (y ≫ (GroupScheme.torsionι (Langlands.CommGroupScheme.toGrp GA) (n : ℤ)).hom.hom) ≫
        dualSchemeMap homPicardZeroPullback (multiplication A (n : ℤ)) hA hA =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA := by
  have hiA := congrArg (fun φ ↦ φ.hom.hom)
    (relativeDualMultiplicationKernelIso_inv_ι preservation composition unitCoherence
      associativity comparison symmetry stability hA MA evaluationA (n : ℤ))
  dsimp only at hiA
  rw [Grp.comp_hom_hom] at hiA
  have h := dualKernelPoint_eq_origin hA stability (multiplication A (n : ℤ)) hA preservation
    composition unitCoherence associativity comparison symmetry MA evaluationA MA evaluationA T
    (y ≫ (relativeDualMultiplicationKernelIso preservation composition unitCoherence
      associativity comparison symmetry stability hA MA evaluationA (n : ℤ)).inv.hom.hom)
  simp only [Category.assoc] at h ⊢
  rwa [reassoc_of% hiA] at h

/-- The dual torsion character is the dual-kernel character of the underlying dual point. -/
lemma dualTorsionCharacter_eq_dualKernelCharacter (n : ℕ) {T : Over S}
    (y : T ⟶ (GroupScheme.torsion (Langlands.CommGroupScheme.toGrp GA) (n : ℤ)).X)
    (hy : (y ≫ (GroupScheme.torsionι (Langlands.CommGroupScheme.toGrp GA) (n : ℤ)).hom.hom) ≫
        dualSchemeMap homPicardZeroPullback (multiplication A (n : ℤ)) hA hA =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) :
    dualTorsionCharacter preservation composition unitCoherence associativity comparison
        symmetry stability hA MA evaluationA n y =
      dualKernelCharacter hA stability (multiplication A (n : ℤ)) hA
        (y ≫ (GroupScheme.torsionι (Langlands.CommGroupScheme.toGrp GA) (n : ℤ)).hom.hom) hy := by
  have hiA := congrArg (fun φ ↦ φ.hom.hom)
    (relativeDualMultiplicationKernelIso_inv_ι preservation composition unitCoherence
      associativity comparison symmetry stability hA MA evaluationA (n : ℤ))
  dsimp only at hiA
  rw [Grp.comp_hom_hom] at hiA
  unfold dualTorsionCharacter dualKernelPointCharacter
  refine dualKernelCharacter_congr stability hA hA _ ?_ _
  rw [Category.assoc, hiA]

/-- The unit underlying an actual root of unity on `T` is the corresponding `Gm` point. -/
lemma mu_pointsLevelEquiv_coe {S : Scheme.{u}} (n : ℕ) (T : Over S) (z : T ⟶ (mu S n).X) :
    ((Additive.toMul (mu.pointsLevelEquiv n T (Additive.ofMul z)) :
        rootsOfUnity n Γ(T.left, ⊤)) : Γ(T.left, ⊤)ˣ) =
      Gm.pointsEquiv S T (z ≫ (mu.incl S n).toMul.hom.hom) := rfl

/-- The unit underlying a value of the actual finite Weil pairing is the dual torsion
character evaluated at the primal kernel lift. -/
lemma finiteWeilLevelBilinearMap_coe (n : ℕ) (T : Over S)
    (x : GroupScheme.Tate.Level A.toGrp T n)
    (y : GroupScheme.Tate.Level (Langlands.CommGroupScheme.toGrp GA) T n) :
    ((Additive.toMul (finiteWeilLevelBilinearMap preservation composition unitCoherence
        associativity comparison symmetry stability hA MA evaluationA n T x y) :
          rootsOfUnity n Γ(T.left, ⊤)) : Γ(T.left, ⊤)ˣ) =
      Gm.pointsEquiv S T (Cartier.characterEvaluation
        (dualTorsionCharacter preservation composition unitCoherence associativity comparison
          symmetry stability hA MA evaluationA n
          (GroupScheme.Tate.kernelLift (Langlands.CommGroupScheme.toGrp GA) T n y))
        (GroupScheme.Tate.kernelLift A.toGrp T n x)) := by
  rw [finiteWeilLevelBilinearMap_apply, finiteWeilPairing_points, mu_pointsLevelEquiv_coe,
    finiteWeilValue_incl]

variable [QuasiSeparatedSpace S']

/-- The actual finite Weil pairing of the base-changed abelian scheme on a test scheme `T`
over `S'` is the actual finite Weil pairing of `A` on `T` regarded over `S`, after the
canonical identifications of primal and dual torsion points. -/
theorem finiteWeilLevelBilinearMap_baseChange (n : ℕ) (T : Over S')
    (x : GroupScheme.Tate.Level ((baseChange b).obj A).toGrp T n)
    (y : GroupScheme.Tate.Level (Langlands.CommGroupScheme.toGrp GAb) T n) :
    finiteWeilLevelBilinearMap preservation composition unitCoherence associativity comparison
        symmetry stability hA' MA' evaluationA' n T x y =
      finiteWeilLevelBilinearMap preservation composition unitCoherence associativity
        comparison symmetry stability hA MA evaluationA n ((Over.map b).obj T)
        (GroupScheme.Tate.levelBaseChange b A.toGrp T n x)
        (dualLevelBaseChange b A preservation composition unitCoherence associativity
          comparison symmetry stability universality hA MA evaluationA hA' MA'
          evaluationA' T n y) := by
  have hL := finiteWeilLevelBilinearMap_coe ((baseChange b).obj A) preservation composition
    unitCoherence associativity comparison symmetry stability hA' MA' evaluationA' n T x y
  have hR := finiteWeilLevelBilinearMap_coe A preservation composition unitCoherence
    associativity comparison symmetry stability hA MA evaluationA n ((Over.map b).obj T)
    (GroupScheme.Tate.levelBaseChange b A.toGrp T n x)
    (dualLevelBaseChange b A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA MA evaluationA hA' MA' evaluationA' T n y)
  apply Additive.toMul.injective
  apply Subtype.ext
  refine hL.trans (Eq.trans ?_ hR.symm)
  set y' := GroupScheme.Tate.kernelLift (Langlands.CommGroupScheme.toGrp GAb) T n y
  set y₀ := GroupScheme.Tate.kernelLift (Langlands.CommGroupScheme.toGrp GA)
    ((Over.map b).obj T) n
    (dualLevelBaseChange b A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA MA evaluationA hA' MA' evaluationA' T n y)
  have hy' := torsion_dualSchemeMap_eq_origin ((baseChange b).obj A) preservation composition
    unitCoherence associativity comparison symmetry stability hA' MA' evaluationA' n y'
  have hy₀ := torsion_dualSchemeMap_eq_origin A preservation composition
    unitCoherence associativity comparison symmetry stability hA MA evaluationA n y₀
  have hq : y₀ ≫ (GroupScheme.torsionι (Langlands.CommGroupScheme.toGrp GA) (n : ℤ)).hom.hom =
      dualPointBaseChange universality b A hA hA'
        (y' ≫ (GroupScheme.torsionι (Langlands.CommGroupScheme.toGrp GAb) (n : ℤ)).hom.hom) := by
    have h₀ := GroupScheme.Tate.kernelLift_ι (Langlands.CommGroupScheme.toGrp GA)
      ((Over.map b).obj T) n
      (dualLevelBaseChange b A preservation composition unitCoherence associativity
        comparison symmetry stability universality hA MA evaluationA hA' MA' evaluationA' T n y)
    have h' := GroupScheme.Tate.kernelLift_ι (Langlands.CommGroupScheme.toGrp GAb) T n y
    refine h₀.trans ((toSection_dualLevelBaseChange b A preservation composition unitCoherence
      associativity comparison symmetry stability universality hA MA evaluationA hA' MA'
      evaluationA' T n y).trans ?_)
    exact congrArg (dualPointBaseChange universality b A hA hA') h'.symm
  rw [dualTorsionCharacter_eq_dualKernelCharacter ((baseChange b).obj A) preservation
      composition unitCoherence associativity comparison symmetry stability hA' MA'
      evaluationA' n y' hy',
    dualTorsionCharacter_eq_dualKernelCharacter A preservation composition unitCoherence
      associativity comparison symmetry stability hA MA evaluationA n y₀ hy₀,
    dualKernelCharacter_congr stability hA hA _ hq hy₀]
  refine dualKernelCharacter_evaluation_familyBaseChange universality b A hA hA' stability hA hA'
    (multiplication A (n : ℤ)) (multiplication ((baseChange b).obj A) (n : ℤ))
    (hom_multiplication_baseChange_fst b A (n : ℤ)) _ hy' _ _ _ ?_
  have h₁ := GroupScheme.Tate.kernelLift_ι A.toGrp ((Over.map b).obj T) n
    (GroupScheme.Tate.levelBaseChange b A.toGrp T n x)
  have h₂ := GroupScheme.Tate.kernelLift_ι ((baseChange b).obj A).toGrp T n x
  refine h₁.trans ?_
  change _ = baseChangePointsEquiv b A.toGrp T
    (GroupScheme.Tate.kernelLift ((baseChange b).obj A).toGrp T n x ≫
      (GroupScheme.kernelι (GroupScheme.multiplication ((baseChange b).obj A).toGrp
        (n : ℤ))).hom.hom)
  rw [h₂]
  rfl

include universality in
/-- Trivial left and right kernels of the actual finite Weil pairing are equivalent before and
after ground base change. -/
theorem finiteWeilLevelBilinearMap_nondegenerate_baseChange_iff (n : ℕ) (T : Over S') :
    ((∀ x, (∀ y, finiteWeilLevelBilinearMap preservation composition unitCoherence
          associativity comparison symmetry stability hA' MA' evaluationA' n T x y = 0) →
        x = 0) ∧
      (∀ y, (∀ x, finiteWeilLevelBilinearMap preservation composition unitCoherence
          associativity comparison symmetry stability hA' MA' evaluationA' n T x y = 0) →
        y = 0)) ↔
    ((∀ x, (∀ y, finiteWeilLevelBilinearMap preservation composition unitCoherence
          associativity comparison symmetry stability hA MA evaluationA n
          ((Over.map b).obj T) x y = 0) → x = 0) ∧
      (∀ y, (∀ x, finiteWeilLevelBilinearMap preservation composition unitCoherence
          associativity comparison symmetry stability hA MA evaluationA n
          ((Over.map b).obj T) x y = 0) → y = 0)) := by
  have key := finiteWeilLevelBilinearMap_baseChange b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA MA evaluationA hA' MA'
    evaluationA' n T
  set eP := GroupScheme.Tate.levelBaseChange b A.toGrp T n
  set eL := dualLevelBaseChange b A preservation composition unitCoherence associativity
    comparison symmetry stability universality hA MA evaluationA hA' MA' evaluationA' T n
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨fun x₀ hx₀ ↦ ?_, fun y₀ hy₀ ↦ ?_⟩
    · obtain ⟨x, rfl⟩ := eP.surjective x₀
      rw [hl x (fun y ↦ (key x y).trans (hx₀ (eL y))), map_zero]
    · obtain ⟨y, rfl⟩ := eL.surjective y₀
      rw [hr y (fun x ↦ (key x y).trans (hy₀ (eP x))), map_zero]
  · rintro ⟨hl, hr⟩
    refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
    · apply eP.injective
      rw [map_zero]
      refine hl (eP x) (fun y₀ ↦ ?_)
      obtain ⟨y, rfl⟩ := eL.surjective y₀
      exact (key x y).symm.trans (hx y)
    · apply eL.injective
      rw [map_zero]
      refine hr (eL y) (fun x₀ ↦ ?_)
      obtain ⟨x, rfl⟩ := eP.surjective x₀
      exact (key x y).symm.trans (hy x)

end DualLevel

end Langlands.AbelianScheme
