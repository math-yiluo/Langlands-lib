import Langlands.AlgebraicGeometry.Picard.LineBundleBaseOpenBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic

/-! # Representation of the line-bundle base-change condition by an open scheme -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

variable {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules)

/-- The ordinary cartesian pullback of the actual module to a test scheme is
locally free of rank one. -/
def IsLineBundleBaseChange (T : Over S) : Prop :=
  IsLocallyFreeRankOne ((Scheme.Modules.pullback (pullback.snd T.hom f)).obj M)

variable [UniversallyClosed f] [LocallyOfFinitePresentation f]
  [M.IsFinitePresentation] (hM : Modules.IsFlatOver f M)

include hM

/-- The actual base-change condition is exactly the image condition for the
full-fibre rank-one open. -/
lemma isLineBundleBaseChange_iff (T : Over S) :
    IsLineBundleBaseChange f M T ↔ ∀ t : T.left, T.hom t ∈ rankOneBaseOpen f M :=
  isLocallyFreeRankOne_pullback_iff_mem_baseOpen
    (IsPullback.of_hasPullback T.hom f).flip M hM

/-- The subterminal presheaf of tests on which the actual pulled-back module
is a line bundle, with restrictions along every slice morphism. -/
def lineBundleBaseChangePresheaf : AlgebraicSpace.Presheaf S where
  obj T := ULift.{u + 1} (PLift (IsLineBundleBaseChange f M T.unop))
  map q := ↾fun h ↦ ULift.up ⟨(isLineBundleBaseChange_iff f M hM _).mpr (by
    intro t
    have ht := (isLineBundleBaseChange_iff f M hM _).mp h.down.down (q.unop.left t)
    simpa only [← Scheme.Hom.comp_apply, Over.w] using ht)⟩
  map_id _ := by ext; exact Subsingleton.elim _ _
  map_comp _ _ := by ext; exact Subsingleton.elim _ _

/-- Maps into the actual open scheme correspond to the actual line-bundle
condition for cartesian pullback. -/
def lineBundleBaseChangeYonedaEquiv (T : Over S) :
    ULift.{u + 1} (T ⟶ Over.mk (rankOneBaseOpen f M).ι) ≃
      ULift.{u + 1} (PLift (IsLineBundleBaseChange f M T)) where
  toFun a := ULift.up ⟨(isLineBundleBaseChange_iff f M hM T).mpr (by
    intro t
    have ha := a.down.w
    rw [← ha]
    exact (a.down.left t).property)⟩
  invFun h := ULift.up (Over.homMk
    (rankOneBaseOpenLift (IsPullback.of_hasPullback T.hom f).flip M hM h.down.down)
    (rankOneBaseOpenLift_fac (IsPullback.of_hasPullback T.hom f).flip M hM h.down.down))
  left_inv a := by
    apply congrArg ULift.up
    apply Over.OverMorphism.ext
    apply (cancel_mono (rankOneBaseOpen f M).ι).mp
    dsimp only [Over.homMk, CostructuredArrow.homMk]
    rw [rankOneBaseOpenLift_fac]
    exact a.down.w.symm
  right_inv _ := Subsingleton.elim _ _

/-- The full presheaf of the actual line-bundle base-change condition is
naturally represented by the full-fibre rank-one open scheme. -/
def lineBundleBaseChangePresheafIso :
    (AlgebraicSpace.schemeYoneda S).obj (Over.mk (rankOneBaseOpen f M).ι) ≅
      lineBundleBaseChangePresheaf f M hM :=
  NatIso.ofComponents (fun T ↦ (lineBundleBaseChangeYonedaEquiv f M hM T.unop).toIso)
    (by intros; ext; dsimp only [lineBundleBaseChangePresheaf]; exact Subsingleton.elim _ _)

end Langlands.AlgebraicGeometry.Picard
