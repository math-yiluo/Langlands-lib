import Langlands.GroupScheme.IntegralModel.FiniteRecoveryInterface
import Langlands.GroupScheme.IntegralModel.FiniteUnramifiedStageRecovery

/-! # Exact finite unramified recovery of smooth integral models -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000

namespace Langlands.GroupScheme.IntegralModel
open Descent Descent.FiniteUnramified GaloisPointComparison

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance recoveryConstructionNormedField : NontriviallyNormedField F :=
  localNormedField F
local instance recoveryConstructionUltrametric : IsUltrametricDist F :=
  localNormedField_ultrametric F
local instance recoveryConstructionComplete : CompleteSpace F :=
  localNormedField_complete F

section AtField

variable (E : IntermediateField F (SeparableClosure F))
  [hEinertia : Fact (E ≤ inertiaFixedField F)]
local notation "hE" => hEinertia.out
local instance recoveryConstructionFieldAlgebra : Algebra E (inertiaFixedField F) :=
  (IntermediateField.inclusion hE).toAlgebra
local instance recoveryConstructionFieldTower : IsScalarTower F E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance recoveryConstructionIntegerAlgebra :
    Algebra (extensionIntegers F E) (fixedFieldIntegers F) :=
  (spectralIntegerInclusion F E hE).toAlgebra
local instance recoveryConstructionGenericAlgebra :
    Algebra (extensionIntegers F E) (inertiaFixedField F) :=
  ((IntermediateField.inclusion hE).toRingHom.comp
    (algebraMap (extensionIntegers F E) E)).toAlgebra
local instance recoveryConstructionGenericTower :
    IsScalarTower (extensionIntegers F E) E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance recoveryConstructionIntegralTower :
    IsScalarTower (extensionIntegers F E) (fixedFieldIntegers F) (inertiaFixedField F) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact spectralIntegerInclusion_inertia F E hE x

/-- The model's specified generic coefficient comparison is the actual
finite-stage square followed by its original generic identification. -/
theorem finiteStage_baseChangeGenericIso
    {G : GroupScheme (Spec (CommRingCat.of E))}
    (N : IntegralModel (extensionIntegers F E) E G) :
    N.baseChangeGenericIso (fixedFieldIntegers F) (inertiaFixedField F) =
      inertiaGenericSquare F E hE N.group ≪≫
        (GroupScheme.baseChange (fieldSpecMap F hE)).mapIso N.genericIso := by
  rw [N.baseChangeGenericIso_eq_square]
  rfl

variable (G : GroupScheme (Spec (CommRingCat.of F)))
  (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))

private theorem finiteInertiaGenericIso_eq_comparison :
    finiteInertiaGenericIso F E G =
      pullbackComparison (Spec.algebraMap F E) (fieldSpecMap F hE)
        (Spec.algebraMap F (inertiaFixedField F)) (fieldSpecMap_base F hE) G := by
  rfl

private theorem finiteModelIso_of_square
    (N : IntegralModel (extensionIntegers F E) E (baseChanged F E G))
    (e : (GroupScheme.baseChange (spectralIntegerMap F E hE)).obj N.group ≅ P.group)
    (he : (GroupScheme.baseChange
        (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).map e.hom ≫
        P.genericIso.hom =
      (inertiaGenericSquare F E hE N.group).hom ≫
        (GroupScheme.baseChange (fieldSpecMap F hE)).map N.genericIso.hom ≫
          (finiteInertiaGenericIso F E G).hom) :
    Nonempty ((N.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).Iso P
      (finiteInertiaGenericIso F E G)) := by
  refine ⟨{ iso := e, generic_comm := ?_ }⟩
  dsimp only [baseChange]
  rw [finiteStage_baseChangeGenericIso F E N]
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using he

/-- The actual finite integral model obtained from an explicit enlarged stage. -/
def finiteRecoveryModel
    (K : IntermediateField F (SeparableClosure F)) (h : K ≤ E)
    (H : GroupScheme (Spec (CommRingCat.of (extensionIntegers F K))))
    (hHaff : IsAffineHom H.X.hom) (hHsm : Smooth H.X.hom)
    (a : (GroupScheme.baseChange (fieldSpecMap F h)).obj
        ((GroupScheme.baseChange (Spec.algebraMap F K)).obj G) ≅
      (GroupScheme.baseChange (fieldSpecMap F h)).obj
        ((GroupScheme.baseChange (Spec.algebraMap (extensionIntegers F K) K)).obj H)) :
    IntegralModel (extensionIntegers F E) E (baseChanged F E G) where
  group := (GroupScheme.baseChange (stageIntegerMap F h)).obj H
  affine := MorphismProperty.pullback_snd _ _ hHaff
  flat := by
    let := hHsm
    exact MorphismProperty.pullback_snd _ _ (inferInstance : Flat H.X.hom)
  finiteType := by
    let := hHsm
    exact MorphismProperty.pullback_snd _ _
      (inferInstance : LocallyOfFiniteType H.X.hom)
  genericIso := rawStageGenericIso F K E h H a

set_option maxHeartbeats 400000 in
/-- An explicit finite stage with exact generic coherence is an exact
coefficient recovery of the original model. -/
theorem finiteRecoveryAt_of_rawStage
    (K : IntermediateField F (SeparableClosure F))
    (h : K ≤ E) (hK : K ≤ inertiaFixedField F)
    (H : GroupScheme (Spec (CommRingCat.of (extensionIntegers F K))))
    (hHaff : IsAffineHom H.X.hom) (hHsm : Smooth H.X.hom)
    (d : P.group ≅ (GroupScheme.baseChange (spectralIntegerMap F K hK)).obj H)
    (a : (GroupScheme.baseChange (fieldSpecMap F h)).obj
        ((GroupScheme.baseChange (Spec.algebraMap F K)).obj G) ≅
      (GroupScheme.baseChange (fieldSpecMap F h)).obj
        ((GroupScheme.baseChange (Spec.algebraMap (extensionIntegers F K) K)).obj H))
    (ha : pullIso (fieldSpecMap F hE) (fieldSpecMap_comp F h hE)
        (fieldSpecMap_comp F h hE) a =
      pullbackComparison (Spec.algebraMap F K) (fieldSpecMap F hK)
          (Spec.algebraMap F (inertiaFixedField F)) (fieldSpecMap_base F hK) G ≪≫
        P.genericIso.symm ≪≫
          (GroupScheme.baseChange
            (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).mapIso d ≪≫
            inertiaGenericSquare F K hK H) :
    HasFiniteRecoveryAt F E G P := by
  let N : IntegralModel (extensionIntegers F E) E (baseChanged F E G) :=
    finiteRecoveryModel F E G K h H hHaff hHsm a
  refine ⟨N, finiteModelIso_of_square F E G P N
    (stageIntegralComparison F h hK hE H ≪≫ d.symm) ?_⟩
  simpa only [N, finiteRecoveryModel, rawStageGenericIso,
    finiteInertiaGenericIso_eq_comparison] using
    rawStage_generic F P K E h hK hE H d a ha

end AtField

set_option maxHeartbeats 400000 in
/-- Every specified smooth integral model over the maximal-unramified integers
has exact recovery from finite Galois unramified coefficients. -/
theorem finiteUnramifiedRecovery : FiniteUnramifiedRecoveryStatement.{u} := by
  intro F _ _ _ _ G P hP
  let : IsAffine P.group.X.left := isAffine_of_isAffineHom P.group.X.hom
  let : Smooth P.group.X.hom := hP
  obtain ⟨E, hfin, hgal, hE, hun, H, hHaff, hHsm, d⟩ :=
    spectralGroupModel F P.group
  let D : SpectralGroupModel F P.group :=
    ⟨E, hfin, hgal, hE, hun, H, hHaff, hHsm, d⟩
  obtain ⟨⟨E', hfin', hgal', h, hE', hun', a, ha⟩⟩ :=
    nonempty_modelIsoStage F P D
  let : Fact (E' ≤ inertiaFixedField F) := ⟨hE'⟩
  refine ⟨E', ⟨hE'⟩, hfin', hgal', hun', ?_⟩
  apply finiteRecoveryAt_of_rawStage F E' G P E h hE H hHaff hHsm d a
  exact ha

end Langlands.GroupScheme.IntegralModel
