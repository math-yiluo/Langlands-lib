import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameBundle
import Langlands.AlgebraicGeometry.ProjectiveBundle.CocycleComparison

/-! # Independence of the local frames used in projective gluing -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {M : S.Modules} {n : ℕ}

/-- An arbitrary genuine frame on each open of the frame-bearing cover. -/
abbrev FrameFamily (M : S.Modules) (n : ℕ) :=
  ∀ U : FrameOpen M n, LocalFrame M n U.val

/-- The strict dual-frame coordinate cocycle for any family of local frames. -/
def familyCocycle (hM : IsLocallyFreeOfRank M (n + 1)) (b : FrameFamily M n) :
    CoordinateCocycle n (frameCover M n hM) where
  transition {U V} h :=
    coordinatesOnOpen n U.val
      ((b U).dual.change (b V).dual U.val le_rfl (leOfHom h))
  transition_id U := by
    dsimp [coordinatesOnOpen]
    rw [LocalFrame.change_self, ProjectiveSpace.coordinateBaseChange_refl]
  transition_comp {U V W} hUV hVW := by
    change coordinatesOnOpen n U.val
        ((b U).dual.change (b W).dual U.val le_rfl
          ((leOfHom hUV).trans (leOfHom hVW))) =
      (coordinatesOnOpen n U.val
        ((b U).dual.change (b V).dual U.val le_rfl (leOfHom hUV))).trans
      (coordinatePullback n ((frameCover M n hM).trans hUV)
        (coordinatesOnOpen n V.val
          ((b V).dual.change (b W).dual V.val le_rfl (leOfHom hVW))))
    rw [frameCover_trans, coordinatesOnOpen_restrict, LocalFrame.change_restrict]
    dsimp [coordinatesOnOpen]
    rw [← ProjectiveSpace.coordinateBaseChange_trans, LocalFrame.change_trans]

/-- The actual projective scheme constructed using an arbitrary family of frames. -/
abbrev familyBundle (hM : IsLocallyFreeOfRank M (n + 1)) (b : FrameFamily M n) : Scheme.{u} :=
  (familyCocycle hM b).scheme

/-- Changes between genuine dual frames intertwine the associated strict cocycles. -/
def familyChange (hM : IsLocallyFreeOfRank M (n + 1)) (b c : FrameFamily M n) :
    CoordinateCocycle.Change (familyCocycle hM b) (familyCocycle hM c) where
  coordinate U := coordinatesOnOpen n U.val
    ((b U).dual.change (c U).dual U.val le_rfl le_rfl)
  compatible {U V} h := by
    change (coordinatesOnOpen n U.val
        ((b U).dual.change (b V).dual U.val le_rfl (leOfHom h))).trans
        (coordinatePullback n ((frameCover M n hM).trans h)
          (coordinatesOnOpen n V.val
            ((b V).dual.change (c V).dual V.val le_rfl le_rfl))) =
      (coordinatesOnOpen n U.val
        ((b U).dual.change (c U).dual U.val le_rfl le_rfl)).trans
        (coordinatesOnOpen n U.val
          ((c U).dual.change (c V).dual U.val le_rfl (leOfHom h)))
    rw [frameCover_trans, coordinatesOnOpen_restrict, LocalFrame.change_restrict]
    dsimp [coordinatesOnOpen]
    rw [← ProjectiveSpace.coordinateBaseChange_trans,
      ← ProjectiveSpace.coordinateBaseChange_trans,
      LocalFrame.change_trans, LocalFrame.change_trans]

/-- The canonical isomorphism comparing two choices of genuine local frames. -/
def frameChoiceIso (hM : IsLocallyFreeOfRank M (n + 1)) (b c : FrameFamily M n) :
    familyBundle hM b ≅ familyBundle hM c :=
  (familyChange hM b c).schemeIso

@[reassoc (attr := simp)]
lemma chart_frameChoiceIso_hom (hM : IsLocallyFreeOfRank M (n + 1))
    (b c : FrameFamily M n) (U : FrameOpen M n) :
    (familyCocycle hM b).chart U ≫ (frameChoiceIso hM b c).hom =
      globalLinearAction n
          (coordinatesOnOpen n U.val
            ((b U).dual.change (c U).dual U.val le_rfl le_rfl)) ≫
        (familyCocycle hM c).chart U :=
  (familyChange hM b c).chart_schemeIso_hom U

@[reassoc (attr := simp)]
lemma frameChoiceIso_hom_toBase (hM : IsLocallyFreeOfRank M (n + 1))
    (b c : FrameFamily M n) :
    (frameChoiceIso hM b c).hom ≫ (familyCocycle hM c).toBase =
      (familyCocycle hM b).toBase :=
  (familyChange hM b c).schemeIso_hom_toBase

@[simp]
lemma frameChoiceIso_refl (hM : IsLocallyFreeOfRank M (n + 1))
    (b : FrameFamily M n) : frameChoiceIso hM b b = Iso.refl _ := by
  apply Iso.ext
  symm
  apply (familyChange hM b b).hom_eq
  intro U
  simp [familyChange, coordinatesOnOpen]

lemma frameChoiceIso_trans (hM : IsLocallyFreeOfRank M (n + 1))
    (b c d : FrameFamily M n) :
    frameChoiceIso hM b c ≪≫ frameChoiceIso hM c d = frameChoiceIso hM b d := by
  apply Iso.ext
  apply (familyChange hM b d).hom_eq
  intro U
  rw [Iso.trans_hom, chart_frameChoiceIso_hom_assoc, chart_frameChoiceIso_hom,
    ← Category.assoc, globalLinearAction_comp]
  dsimp [familyChange, coordinatesOnOpen]
  rw [← ProjectiveSpace.coordinateBaseChange_trans, LocalFrame.change_trans]

/-- Every frame-family construction is isomorphic over the base to the fixed frame bundle. -/
def toFrameBundleIso (hM : IsLocallyFreeOfRank M (n + 1)) (b : FrameFamily M n) :
    familyBundle hM b ≅ frameBundle M n hM :=
  frameChoiceIso hM b (frame M n)

@[reassoc (attr := simp)]
lemma toFrameBundleIso_hom_toBase (hM : IsLocallyFreeOfRank M (n + 1))
    (b : FrameFamily M n) :
    (toFrameBundleIso hM b).hom ≫ FrameBundle.toBase hM = (familyCocycle hM b).toBase :=
  frameChoiceIso_hom_toBase hM b (frame M n)

end Langlands.AlgebraicGeometry.ProjectiveBundle
