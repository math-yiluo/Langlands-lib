import Langlands.Automorphic.GroupSchemeAmbientFunctorial

/-! # Compact-open topology on the original group-scheme ambient functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions.CompactOpen

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- The faithful continuous-function realization of the original ambient carrier. -/
def toContinuousMap :
    ContinuousRationalFunctions F G →ₗ[ℂ] C(AdelicGroupPoints F G, ℂ) where
  toFun f := ⟨f.val.val, f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem toContinuousMap_apply (f : ContinuousRationalFunctions F G)
    (x : AdelicGroupPoints F G) :
    toContinuousMap F G f x = f.val.val x := rfl

theorem toContinuousMap_injective : Function.Injective (toContinuousMap F G) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun c : C(AdelicGroupPoints F G, ℂ) => (c : AdelicGroupPoints F G → ℂ)) h

/-- Opt-in compact-open topology on the unchanged ambient carrier. -/
scoped instance instTopologicalSpace : TopologicalSpace (ContinuousRationalFunctions F G) :=
  TopologicalSpace.induced (toContinuousMap F G) inferInstance

theorem isEmbedding_toContinuousMap : Topology.IsEmbedding (toContinuousMap F G) :=
  ⟨Topology.IsInducing.induced _, toContinuousMap_injective F G⟩

scoped instance instIsTopologicalAddGroup :
    IsTopologicalAddGroup (ContinuousRationalFunctions F G) :=
  (isEmbedding_toContinuousMap F G).isInducing.isTopologicalAddGroup (toContinuousMap F G)

scoped instance instContinuousSMul : ContinuousSMul ℂ (ContinuousRationalFunctions F G) :=
  continuousSMul_induced (toContinuousMap F G)

scoped instance instT2Space : T2Space (ContinuousRationalFunctions F G) :=
  (isEmbedding_toContinuousMap F G).t2Space

/-- Faithful continuous linear realization for the selected topology. -/
def toContinuousMapCLM :
    ContinuousRationalFunctions F G →L[ℂ] C(AdelicGroupPoints F G, ℂ) :=
  ⟨toContinuousMap F G, (isEmbedding_toContinuousMap F G).continuous⟩

/-- Evaluation at an actual adelic point is continuous and complex linear. -/
def evalCLM (x : AdelicGroupPoints F G) : ContinuousRationalFunctions F G →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ x).comp (toContinuousMapCLM F G)

@[simp]
theorem evalCLM_apply (x : AdelicGroupPoints F G) (f : ContinuousRationalFunctions F G) :
    evalCLM F G x f = f.val.val x := rfl

/-- Each fixed positive right translation is continuous for the compact-open topology. -/
theorem continuous_rightAction (g : AdelicGroupPoints F G) :
    Continuous (continuousRightAction F G g) := by
  apply continuous_induced_rng.mpr
  let r : C(AdelicGroupPoints F G, AdelicGroupPoints F G) :=
    ⟨fun x => x * g, continuous_id.mul continuous_const⟩
  exact (ContinuousMap.continuous_precomp r).comp
    (isEmbedding_toContinuousMap F G).continuous

/-- The original fixed positive right translation as a continuous linear operator. -/
def rightTranslationCLM (g : AdelicGroupPoints F G) :
    ContinuousRationalFunctions F G →L[ℂ] ContinuousRationalFunctions F G :=
  ⟨continuousRightAction F G g, continuous_rightAction F G g⟩

@[simp]
theorem rightTranslationCLM_apply (g x : AdelicGroupPoints F G)
    (f : ContinuousRationalFunctions F G) :
    (rightTranslationCLM F G g f).val.val x = f.val.val (x * g) := rfl

variable {G} {H K : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [IsAffine K.X.left]

/-- Pullback along an actual group-scheme morphism is compact-open continuous. -/
theorem continuous_pullback (φ : G ⟶ H) : Continuous (continuousPullback F φ) := by
  apply continuous_induced_rng.mpr
  let a : C(AdelicGroupPoints F G, AdelicGroupPoints F H) :=
    ⟨AdelicGroupPoints.map F G H φ, (AdelicGroupPoints.map F G H φ).continuous⟩
  exact (ContinuousMap.continuous_precomp a).comp
    (isEmbedding_toContinuousMap F H).continuous

/-- The existing pullback, with continuity bundled for the selected topologies. -/
def pullbackCLM (φ : G ⟶ H) :
    ContinuousRationalFunctions F H →L[ℂ] ContinuousRationalFunctions F G :=
  ⟨continuousPullback F φ, continuous_pullback F φ⟩

@[simp]
theorem pullbackCLM_toLinearMap (φ : G ⟶ H) :
    (pullbackCLM F φ).toLinearMap = continuousPullback F φ := rfl

@[simp]
theorem pullbackCLM_apply (φ : G ⟶ H) (f : ContinuousRationalFunctions F H)
    (x : AdelicGroupPoints F G) :
    (pullbackCLM F φ f).val.val x = f.val.val (AdelicGroupPoints.map F G H φ x) := rfl

@[simp]
theorem pullbackCLM_id : pullbackCLM F (𝟙 G) = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro f
  exact continuousPullback_id F f

/-- The original contravariant composition law holds for continuous linear pullbacks. -/
theorem pullbackCLM_comp (φ : G ⟶ H) (ψ : H ⟶ K) :
    pullbackCLM F (φ ≫ ψ) = (pullbackCLM F φ).comp (pullbackCLM F ψ) := by
  apply ContinuousLinearMap.ext
  intro f
  exact continuousPullback_comp F φ ψ f

/-- The original positive action law for the continuous linear pullback. -/
theorem pullbackCLM_rightAction (φ : G ⟶ H) (f : ContinuousRationalFunctions F H)
    (g : AdelicGroupPoints F G) :
    pullbackCLM F φ (continuousRightAction F H (AdelicGroupPoints.map F G H φ g) f) =
      continuousRightAction F G g (pullbackCLM F φ f) :=
  continuousPullback_rightAction F φ f g

/-- The existing pullback equivalence of an actual scheme isomorphism is continuous. -/
def pullbackContinuousLinearEquiv (e : G ≅ H) :
    ContinuousRationalFunctions F H ≃L[ℂ] ContinuousRationalFunctions F G where
  toLinearEquiv := continuousPullbackEquiv F e
  continuous_toFun := continuous_pullback F e.hom
  continuous_invFun := continuous_pullback F e.inv

@[simp]
theorem pullbackContinuousLinearEquiv_toLinearEquiv (e : G ≅ H) :
    (pullbackContinuousLinearEquiv F e).toLinearEquiv = continuousPullbackEquiv F e := rfl

@[simp]
theorem pullbackContinuousLinearEquiv_apply (e : G ≅ H)
    (f : ContinuousRationalFunctions F H) (x : AdelicGroupPoints F G) :
    (pullbackContinuousLinearEquiv F e f).val.val x =
      f.val.val (AdelicGroupPoints.map F G H e.hom x) := rfl

@[simp]
theorem pullbackContinuousLinearEquiv_symm_apply (e : G ≅ H)
    (f : ContinuousRationalFunctions F G) (x : AdelicGroupPoints F H) :
    ((pullbackContinuousLinearEquiv F e).symm f).val.val x =
      f.val.val (AdelicGroupPoints.map F H G e.inv x) := rfl

variable (n : ℕ)

local instance generalLinearIsAffine :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

/-- Continuity of the original forward general-linear ambient comparison. -/
theorem continuous_generalLinearEquiv :
    Continuous (continuousGeneralLinearEquiv F n) := by
  apply (Langlands.Automorphic.ContinuousRationalFunctions.isEmbedding_toContinuousMap F n
    ).continuous_iff.mpr
  let a : C(AdelicGL F n,
      AdelicGroupPoints F (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :=
    ⟨(GeneralLinearGroupPoints.adelicHomeomorph F n).symm,
      (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous⟩
  exact (ContinuousMap.continuous_precomp a).comp
    (isEmbedding_toContinuousMap F _).continuous

/-- Continuity of the original inverse general-linear ambient comparison. -/
theorem continuous_generalLinearEquiv_symm :
    Continuous (continuousGeneralLinearEquiv F n).symm := by
  apply (isEmbedding_toContinuousMap F _).continuous_iff.mpr
  let a : C(AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)), AdelicGL F n) :=
    ⟨GeneralLinearGroupPoints.adelicHomeomorph F n,
      (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous⟩
  exact (ContinuousMap.continuous_precomp a).comp
    (Langlands.Automorphic.ContinuousRationalFunctions.isEmbedding_toContinuousMap F n).continuous

/-- The original general-linear comparison, now as a continuous linear equivalence. -/
def generalLinearContinuousLinearEquiv :
    ContinuousRationalFunctions F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
      ≃L[ℂ] Langlands.Automorphic.ContinuousRationalFunctions F n where
  toLinearEquiv := continuousGeneralLinearEquiv F n
  continuous_toFun := continuous_generalLinearEquiv F n
  continuous_invFun := continuous_generalLinearEquiv_symm F n

@[simp]
theorem generalLinearContinuousLinearEquiv_toLinearEquiv :
    (generalLinearContinuousLinearEquiv F n).toLinearEquiv = continuousGeneralLinearEquiv F n := rfl

@[simp]
theorem generalLinearContinuousLinearEquiv_apply
    (f : ContinuousRationalFunctions F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))
    (x : AdelicGL F n) :
    (generalLinearContinuousLinearEquiv F n f).val.val x =
      f.val.val ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm x) := rfl

@[simp]
theorem generalLinearContinuousLinearEquiv_symm_apply
    (f : Langlands.Automorphic.ContinuousRationalFunctions F n)
    (x : AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :
    ((generalLinearContinuousLinearEquiv F n).symm f).val.val x =
      f.val.val (GeneralLinearGroupPoints.adelicHomeomorph F n x) := rfl

/-- The topological comparison preserves the full original positive right action. -/
theorem generalLinearContinuousLinearEquiv_rightAction
    (f : ContinuousRationalFunctions F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))
    (g : AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :
    generalLinearContinuousLinearEquiv F n (continuousRightAction F _ g f) =
      Langlands.Automorphic.continuousRightAction F n
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (generalLinearContinuousLinearEquiv F n f) :=
  continuousGeneralLinearEquiv_rightAction F n f g

end Langlands.Automorphic.GroupSchemeFunctions.CompactOpen
