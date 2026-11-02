import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameBundle
import Langlands.AlgebraicGeometry.ProjectiveBundle.CoverComparison

/-! # Comparison of projective bundles from different frame bases -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} (M : S.Modules) (n : ℕ)

/-- A topological basis of opens carrying specified genuine module-sheaf frames. -/
structure FrameAtlas where
  opens : Set S.Opens
  isBasis : TopologicalSpace.Opens.IsBasis opens
  frame (U : opens) : LocalFrame M n U.val

namespace FrameAtlas

/-- Local freeness supplies a frame atlas without an additional existence hypothesis. -/
def ofLocallyFree (hM : IsLocallyFreeOfRank M (n + 1)) : FrameAtlas M n where
  opens := { U | Nonempty (LocalFrame M n U) }
  isBasis := by
    simpa [FrameOpen] using isBasis_frameOpen M n hM
  frame U := U.property.some

variable {M n} (a : FrameAtlas M n)

/-- The actual open-subscheme cover of a frame basis. -/
abbrev openCover : S.OpenCover where
  I₀ := a.opens
  X U := U.val.toScheme
  f U := U.val.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun U => inferInstance⟩
    obtain ⟨U, hU, hx, _⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp a.isBasis
        (show x ∈ (⊤ : S.Opens) from trivial)
    exact ⟨⟨U, hU⟩, ⟨x, hx⟩, rfl⟩

instance : Preorder a.openCover.I₀ :=
  inferInstanceAs (Preorder a.opens)

instance : a.openCover.LocallyDirected :=
  Scheme.Cover.LocallyDirected.ofIsBasisOpensRange
    (by intros; simp [openCover]) (by
      simpa [openCover] using a.isBasis)

@[simp]
lemma openCover_trans {U V : a.openCover.I₀} (h : U ⟶ V) :
    a.openCover.trans h = S.homOfLE (show U.val ≤ V.val from leOfHom h) := by
  apply (cancel_mono V.val.ι).mp
  rw [Scheme.homOfLE_ι]
  exact a.openCover.trans_map h

/-- The dual-frame cocycle on this particular basis of trivializing opens. -/
def cocycle : CoordinateCocycle n a.openCover where
  transition {U V} h :=
    coordinatesOnOpen n U.val
      ((a.frame U).dual.change (a.frame V).dual U.val le_rfl (leOfHom h))
  transition_id U := by
    dsimp [coordinatesOnOpen]
    rw [LocalFrame.change_self, ProjectiveSpace.coordinateBaseChange_refl]
  transition_comp {U V W} hUV hVW := by
    change coordinatesOnOpen n U.val
        ((a.frame U).dual.change (a.frame W).dual U.val le_rfl
          ((leOfHom hUV).trans (leOfHom hVW))) =
      (coordinatesOnOpen n U.val
        ((a.frame U).dual.change (a.frame V).dual U.val le_rfl (leOfHom hUV))).trans
      (coordinatePullback n (a.openCover.trans hUV)
        (coordinatesOnOpen n V.val
          ((a.frame V).dual.change (a.frame W).dual V.val le_rfl (leOfHom hVW))))
    rw [a.openCover_trans, coordinatesOnOpen_restrict, LocalFrame.change_restrict]
    dsimp [coordinatesOnOpen]
    rw [← ProjectiveSpace.coordinateBaseChange_trans, LocalFrame.change_trans]

/-- The actual scheme glued from the specified basis and its genuine frames. -/
abbrev bundle : Scheme.{u} := a.cocycle.scheme

/-- The structure morphism of this frame-atlas construction. -/
abbrev toBase : a.bundle ⟶ S := a.cocycle.toBase

/-- A basis member is also an open in the cover of all frame-bearing opens. -/
abbrev toFrameOpen (U : a.opens) : FrameOpen M n :=
  ⟨U.val, ⟨a.frame U⟩⟩

/-- The actual dual-coordinate change to the fixed frame on the same open. -/
def comparisonCoordinate (U : a.opens) :
    (Fin (n + 1) → Γ(U.val.toScheme, ⊤)) ≃ₗ[Γ(U.val.toScheme, ⊤)]
      (Fin (n + 1) → Γ(U.val.toScheme, ⊤)) :=
  coordinatesOnOpen n U.val
    ((a.frame U).dual.change (ProjectiveBundle.frame M n (a.toFrameOpen U)).dual
      U.val le_rfl le_rfl)

/-- Actual changes of dual frames intertwine the two transition systems. -/
lemma comparisonCoordinate_compatible (hM : IsLocallyFreeOfRank M (n + 1))
    {U V : a.openCover.I₀} (h : U ⟶ V) :
    (a.cocycle.transition h).trans
        (coordinatePullback n (a.openCover.trans h)
          (a.comparisonCoordinate V)) =
      (a.comparisonCoordinate U).trans
        ((frameCocycle M n hM).transition
          (homOfLE (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h))) := by
  change (coordinatesOnOpen n U.val
      ((a.frame U).dual.change (a.frame V).dual U.val le_rfl (leOfHom h))).trans
      (coordinatePullback n (a.openCover.trans h)
        (coordinatesOnOpen n V.val
          ((a.frame V).dual.change
            (ProjectiveBundle.frame M n (a.toFrameOpen V)).dual V.val le_rfl le_rfl))) =
    (coordinatesOnOpen n U.val
      ((a.frame U).dual.change
        (ProjectiveBundle.frame M n (a.toFrameOpen U)).dual U.val le_rfl le_rfl)).trans
      (coordinatesOnOpen n U.val
        ((ProjectiveBundle.frame M n (a.toFrameOpen U)).dual.change
          (ProjectiveBundle.frame M n (a.toFrameOpen V)).dual U.val le_rfl (leOfHom h)))
  rw [a.openCover_trans, coordinatesOnOpen_restrict, LocalFrame.change_restrict]
  dsimp [coordinatesOnOpen]
  rw [← ProjectiveSpace.coordinateBaseChange_trans,
    ← ProjectiveSpace.coordinateBaseChange_trans,
    LocalFrame.change_trans, LocalFrame.change_trans]

/-- The chart into the fixed frame bundle, expressed in this atlas's coordinates. -/
def comparisonChart (hM : IsLocallyFreeOfRank M (n + 1)) (U : a.opens) :
    RelativeProjectiveSpace U.val.toScheme n ⟶ frameBundle M n hM :=
  globalLinearAction n (a.comparisonCoordinate U) ≫
    FrameBundle.chart hM (a.toFrameOpen U)

lemma comparisonChart_compatible (hM : IsLocallyFreeOfRank M (n + 1))
    {U V : a.openCover.I₀} (hUV : U ⟶ V) :
    a.cocycle.chartFunctor.map hUV ≫ a.comparisonChart hM V =
      a.comparisonChart hM U := by
  change globalLinearAction n (a.cocycle.transition hUV) ≫
      RelativeProjectiveSpace.map n (a.openCover.trans hUV) ≫
        (globalLinearAction n (a.comparisonCoordinate V) ≫
          FrameBundle.chart hM (a.toFrameOpen V)) = _
  rw [map_globalLinearAction_assoc, ← Category.assoc, globalLinearAction_comp,
    a.comparisonCoordinate_compatible hM hUV,
    ← globalLinearAction_comp]
  simp only [Category.assoc]
  rw [a.openCover_trans]
  exact congrArg (fun f => globalLinearAction n (a.comparisonCoordinate U) ≫ f)
    (FrameBundle.transition_chart hM
      (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom hUV))

/-- Each comparison chart is Cartesian over its original base open. -/
lemma isPullback_comparisonChart (hM : IsLocallyFreeOfRank M (n + 1)) (U : a.opens) :
    IsPullback (RelativeProjectiveSpace.toBase U.val.toScheme n)
      (a.comparisonChart hM U) U.val.ι (FrameBundle.toBase hM) := by
  refine (FrameBundle.isPullback_chart hM (a.toFrameOpen U)).of_iso'
    (globalLinearActionIso n (a.comparisonCoordinate U))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp [comparisonChart]
  · simp
  · simp

/-- The actual frame bundle carries the Cartesian atlas constructed from this basis. -/
def cartesianAtlas (hM : IsLocallyFreeOfRank M (n + 1)) :
    a.cocycle.CartesianAtlas (frameBundle M n hM) (FrameBundle.toBase hM) where
  chart := a.comparisonChart hM
  compatible := a.comparisonChart_compatible hM
  cartesian := a.isPullback_comparisonChart hM

/-- Canonical comparison with the fixed projective frame bundle across covers. -/
def toFrameBundleIso (hM : IsLocallyFreeOfRank M (n + 1)) :
    a.bundle ≅ frameBundle M n hM :=
  (a.cartesianAtlas hM).schemeIso

@[reassoc (attr := simp)]
lemma chart_toFrameBundleIso_hom (hM : IsLocallyFreeOfRank M (n + 1)) (U : a.opens) :
    a.cocycle.chart U ≫ (a.toFrameBundleIso hM).hom =
      a.comparisonChart hM U :=
  (a.cartesianAtlas hM).chart_schemeIso_hom U

@[reassoc (attr := simp)]
lemma toFrameBundleIso_hom_toBase (hM : IsLocallyFreeOfRank M (n + 1)) :
    (a.toFrameBundleIso hM).hom ≫ FrameBundle.toBase hM = a.toBase :=
  (a.cartesianAtlas hM).schemeIso_hom_toBase

@[reassoc (attr := simp)]
lemma toFrameBundleIso_inv_toBase (hM : IsLocallyFreeOfRank M (n + 1)) :
    (a.toFrameBundleIso hM).inv ≫ a.toBase = FrameBundle.toBase hM := by
  rw [← a.toFrameBundleIso_hom_toBase hM, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Comparison between the actual projective bundles from any two frame bases. -/
def comparisonIso (hM : IsLocallyFreeOfRank M (n + 1)) (b : FrameAtlas M n) :
    a.bundle ≅ b.bundle :=
  a.toFrameBundleIso hM ≪≫ (b.toFrameBundleIso hM).symm

@[simp]
lemma comparisonIso_refl (hM : IsLocallyFreeOfRank M (n + 1)) :
    a.comparisonIso hM a = Iso.refl _ := by
  simp [comparisonIso]

lemma comparisonIso_trans (hM : IsLocallyFreeOfRank M (n + 1))
    (b c : FrameAtlas M n) :
    a.comparisonIso hM b ≪≫ b.comparisonIso hM c = a.comparisonIso hM c := by
  apply Iso.ext
  simp [comparisonIso]

@[reassoc (attr := simp)]
lemma comparisonIso_hom_toBase (hM : IsLocallyFreeOfRank M (n + 1))
    (b : FrameAtlas M n) :
    (a.comparisonIso hM b).hom ≫ b.toBase = a.toBase := by
  simp [comparisonIso]

end FrameAtlas

end Langlands.AlgebraicGeometry.ProjectiveBundle
