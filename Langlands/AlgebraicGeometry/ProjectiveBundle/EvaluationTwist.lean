import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationGeneration
import Langlands.AlgebraicGeometry.ProjectiveBundle.Tautological

/-! # Degree-one comparisons for actual projective evaluation maps -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.SchemeModule.RigidifiedModule
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.LinearSystem

/-- Compatibility of four module maps with the canonical pullback comparison
around a commuting square. -/
def PullbackSquareCompatible {X Y X' Y' : Scheme.{u}}
    {N : X.Modules} {M : Y.Modules} {N' : X'.Modules} {M' : Y'.Modules}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (w : p' ≫ b = a ≫ p)
    (δ : (Scheme.Modules.pullback p).obj M ⟶ N)
    (α : (Scheme.Modules.pullback p').obj M' ⟶ N')
    (β : (Scheme.Modules.pullback b).obj M ⟶ M')
    (γ : (Scheme.Modules.pullback a).obj N ⟶ N') : Prop :=
  (Scheme.Modules.pullback p').map β ≫ α =
    (squarePullbackIso p p' a b w M).hom ≫
      (Scheme.Modules.pullback a).map δ ≫ γ

/-- Unpack the equation in a pullback-square compatibility proposition. -/
lemma PullbackSquareCompatible.eq {X Y X' Y' : Scheme.{u}}
    {N : X.Modules} {M : Y.Modules} {N' : X'.Modules} {M' : Y'.Modules}
    {p : X ⟶ Y} {p' : X' ⟶ Y'} {a : X' ⟶ X} {b : Y' ⟶ Y}
    {w : p' ≫ b = a ≫ p}
    {δ : (Scheme.Modules.pullback p).obj M ⟶ N}
    {α : (Scheme.Modules.pullback p').obj M' ⟶ N'}
    {β : (Scheme.Modules.pullback b).obj M ⟶ M'}
    {γ : (Scheme.Modules.pullback a).obj N ⟶ N'}
    (h : PullbackSquareCompatible p p' a b w δ α β γ) :
    (Scheme.Modules.pullback p').map β ≫ α =
      (squarePullbackIso p p' a b w M).hom ≫
        (Scheme.Modules.pullback a).map δ ≫ γ :=
  h

/-- A covering coordinate family detects the comparison law over a square
whose four schemes and four module sheaves may be different. -/
lemma pullback_comparison_square_between {X Y X' Y' : Scheme.{u}}
    {N : X.Modules} {M : Y.Modules} {N' : X'.Modules} {M' : Y'.Modules}
    (hM : IsLocallyFreeRankOne M) {ι : Type*} (s : ι → GlobalSections M)
    (hs : (⨆ i, trivializationOpen M (s i)) = ⊤)
    (p : X ⟶ Y) (p' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (w : p' ≫ b = a ≫ p)
    (δ : (Scheme.Modules.pullback p).obj M ⟶ N)
    (α : (Scheme.Modules.pullback p').obj M' ⟶ N')
    (β : (Scheme.Modules.pullback b).obj M ⟶ M')
    (γ : (Scheme.Modules.pullback a).obj N ⟶ N')
    (h : ∀ i,
      α.app ⊤ (pullbackSection p' M' (β.app ⊤ (pullbackSection b M (s i)))) =
        γ.app ⊤ (pullbackSection a N (δ.app ⊤ (pullbackSection p M (s i))))) :
    PullbackSquareCompatible p p' a b w δ α β γ := by
  unfold PullbackSquareCompatible
  have hs' := frameCover_pullback hM s hs b
  have hs'' := frameCover_pullback (hM.pullback b)
    (fun i ↦ pullbackSection b M (s i)) hs' p'
  apply hom_ext_of_generating_sections
    (fun i ↦ pullbackSection p' ((Scheme.Modules.pullback b).obj M)
      (pullbackSection b M (s i))) hs''
  intro i
  rw [pullbackMap_comp_coordinate]
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    squarePullbackIso_coordinate, pullbackMap_comp_coordinate]
  exact h i

end Langlands.AlgebraicGeometry.LinearSystem

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

variable {X S : Scheme.{u}} (p : X ⟶ S) {M : S.Modules} (L : LineBundle X)
    (ev : M ⟶ (Scheme.Modules.pushforward p).obj L.obj) {n : ℕ}

/-- A local evaluation pulls the actual projective degree-one twist back to the given line bundle. -/
def localEvaluationTwistIso {U : S.Opens} (e : LocalFrame M n U)
    (W : S.Opens) (h : W ≤ U)
    (hs : ∀ x : (p ⁻¹ᵁ W).toScheme, ∃ i,
      x ∈ nonvanishingLocus (evaluationLineBundle p L W).obj
        (localEvaluationSections p L ev e W h i)) :
    (Scheme.Modules.pullback (localEvaluationMap p L ev e W h hs)).obj
        (RelativeProjectiveSpace.twistOne W.toScheme n).obj ≅
      (evaluationLineBundle p L W).obj :=
  relativeLinearSystemTwistIso (localEvaluationSections p L ev e W h)
    (evaluationBase p W) hs

/-- This comparison carries each actual pulled-back coordinate to the evaluated basis section. -/
lemma localEvaluationTwistIso_coordinate {U : S.Opens} (e : LocalFrame M n U)
    (W : S.Opens) (h : W ≤ U)
    (hs : ∀ x : (p ⁻¹ᵁ W).toScheme, ∃ i,
      x ∈ nonvanishingLocus (evaluationLineBundle p L W).obj
        (localEvaluationSections p L ev e W h i)) (i : Fin (n + 1)) :
    (localEvaluationTwistIso p L ev e W h hs).hom.app ⊤
        (pullbackSection (localEvaluationMap p L ev e W h hs)
          (RelativeProjectiveSpace.twistOne W.toScheme n).obj
          (RelativeProjectiveSpace.twistOneCoordinate W.toScheme n i)) =
      localEvaluationSections p L ev e W h i :=
  relativeLinearSystemTwistIso_coordinate (localEvaluationSections p L ev e W h)
    (evaluationBase p W) hs i

/-- The evaluated coordinate equations uniquely determine the local comparison. -/
lemma localEvaluationTwistIso_unique {U : S.Opens} (e : LocalFrame M n U)
    (W : S.Opens) (h : W ≤ U)
    (hs : ∀ x : (p ⁻¹ᵁ W).toScheme, ∃ i,
      x ∈ nonvanishingLocus (evaluationLineBundle p L W).obj
        (localEvaluationSections p L ev e W h i))
    (α : (Scheme.Modules.pullback (localEvaluationMap p L ev e W h hs)).obj
        (RelativeProjectiveSpace.twistOne W.toScheme n).obj ⟶
      (evaluationLineBundle p L W).obj)
    (hα : ∀ i, α.app ⊤
      (pullbackSection (localEvaluationMap p L ev e W h hs)
        (RelativeProjectiveSpace.twistOne W.toScheme n).obj
        (RelativeProjectiveSpace.twistOneCoordinate W.toScheme n i)) =
      localEvaluationSections p L ev e W h i) :
    α = (localEvaluationTwistIso p L ev e W h hs).hom := by
  apply hom_ext_of_pullback_generating_sections
    (L := RelativeProjectiveSpace.twistOne W.toScheme n)
    (RelativeProjectiveSpace.twistOneCoordinate W.toScheme n)
    (relativeProjectiveCoordinates_generate W.toScheme n)
    (localEvaluationMap p L ev e W h hs)
  intro i
  exact (hα i).trans (localEvaluationTwistIso_coordinate p L ev e W h hs i).symm

/-- The same comparison carries any changed coordinate family to the changed evaluated family. -/
lemma localEvaluationTwistIso_linearChange {U : S.Opens} (e : LocalFrame M n U)
    (W : S.Opens) (h : W ≤ U)
    (hs : ∀ x : (p ⁻¹ᵁ W).toScheme, ∃ i,
      x ∈ nonvanishingLocus (evaluationLineBundle p L W).obj
        (localEvaluationSections p L ev e W h i))
    (a : (Fin (n + 1) → Γ(W.toScheme, ⊤)) →ₗ[Γ(W.toScheme, ⊤)]
      (Fin (n + 1) → Γ(W.toScheme, ⊤))) (i : Fin (n + 1)) :
    (localEvaluationTwistIso p L ev e W h hs).hom.app ⊤
        (pullbackSection (localEvaluationMap p L ev e W h hs)
          (RelativeProjectiveSpace.twistOne W.toScheme n).obj
          (linearChangeSections
            (RelativeProjectiveSpace.toBase W.toScheme n ≫ W.toScheme.toSpecΓ)
            (RelativeProjectiveSpace.twistOneCoordinate W.toScheme n) a i)) =
      linearChangeSections (L := evaluationLineBundle p L W)
        (evaluationBase p W ≫ W.toScheme.toSpecΓ)
        (localEvaluationSections p L ev e W h) a i := by
  apply pullback_comparison_linearChange_baseChange
    (L := RelativeProjectiveSpace.twistOne W.toScheme n)
    (M := evaluationLineBundle p L W)
    (RelativeProjectiveSpace.toBase W.toScheme n ≫ W.toScheme.toSpecΓ)
    (evaluationBase p W ≫ W.toScheme.toSpecΓ)
    (RelativeProjectiveSpace.twistOneCoordinate W.toScheme n)
    (localEvaluationSections p L ev e W h)
    (localEvaluationMap p L ev e W h hs) (RingHom.id _)
    (by simp only [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id,
      ← Category.assoc, localEvaluationMap_toBase])
    (localEvaluationTwistIso p L ev e W h hs).hom
    (localEvaluationTwistIso_coordinate p L ev e W h hs) a a
    (fun _ _ => rfl) i

namespace EvaluationTwist

variable (hM : IsLocallyFreeOfRank M (n + 1))
    (hs : FrameEvaluationGenerates p L ev n)

/-- The map to an actual chosen frame's relative projective chart. -/
abbrev localMap (U : FrameOpen M n) :=
  localEvaluationMap p L ev (frame M n U) U.val le_rfl (hs U)

/-- The degree-one comparison on a chosen frame. -/
abbrev localIso (U : FrameOpen M n) :=
  localEvaluationTwistIso p L ev (frame M n U) U.val le_rfl (hs U)

/-- Actual evaluation maps commute with the full chart transition, including frame change. -/
lemma localMap_chartMap {U V : FrameOpen M n} (hUV : U ≤ V) :
    localMap p L ev hs U ≫ FrameBundle.chartMap hM hUV =
      X.homOfLE (p.preimage_mono hUV) ≫ localMap p L ev hs V := by
  apply (cancel_mono (FrameBundle.chart hM V)).mp
  simp only [Category.assoc, FrameBundle.chartMap_chart]
  exact (evaluationChartMap_restrict p L ev hM hs hUV).symm

/-- The comparison after changing projective charts evaluates the larger frame
on the smaller inverse-image open. -/
lemma localIso_chartTwistIso_coordinate {U V : (frameCover M n hM).I₀} (hUV : U ≤ V)
    (i : Fin (n + 1)) :
    (localIso p L ev hs U).hom.app ⊤
        (pullbackSection (localMap p L ev hs U)
          (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X U) n).obj
          (((frameCocycle M n hM).chartTwistIso (homOfLE hUV)).hom.app ⊤
            (pullbackSection ((frameCocycle M n hM).chartFunctor.map (homOfLE hUV))
              (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X V) n).obj
              (RelativeProjectiveSpace.twistOneCoordinate ((frameCover M n hM).X V) n i)))) =
      localEvaluationSections p L ev (frame M n V) U.val hUV i := by
  let a := coordinatesOnOpen n U.val
    ((frame M n U).dual.change (frame M n V).dual U.val le_rfl hUV)
  have hc : ((frameCocycle M n hM).chartTwistIso (homOfLE hUV)).hom.app ⊤
      (pullbackSection ((frameCocycle M n hM).chartFunctor.map (homOfLE hUV))
        (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X V) n).obj
        (RelativeProjectiveSpace.twistOneCoordinate ((frameCover M n hM).X V) n i)) =
      linearChangeSections
        (RelativeProjectiveSpace.toBase ((frameCover M n hM).X U) n ≫ ((frameCover M n hM).X U).toSpecΓ)
        (RelativeProjectiveSpace.twistOneCoordinate ((frameCover M n hM).X U) n) a.toLinearMap i :=
    (frameCocycle M n hM).chartTwistIso_coordinate (homOfLE hUV) i
  exact (congrArg
    (fun t : GlobalSections (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X U) n).obj ↦
      (localIso p L ev hs U).hom.app ⊤
        (pullbackSection (localMap p L ev hs U)
          (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X U) n).obj t)) hc).trans
    ((localEvaluationTwistIso_linearChange p L ev (frame M n U) U.val le_rfl
      (hs U) a.toLinearMap i).trans
      (congrFun (localEvaluationSections_change p L ev
        (frame M n U) (frame M n V) le_rfl hUV) i).symm)

/-- Restricting the comparison on a larger frame evaluates that same frame
on the smaller inverse-image open. -/
lemma localIso_restrict_coordinate {U V : (frameCover M n hM).I₀} (hUV : U ≤ V)
    (i : Fin (n + 1)) :
    (openPullbackIso L.obj (p.preimage_mono hUV)).hom.app ⊤
        (pullbackSection (X.homOfLE (p.preimage_mono hUV))
          (evaluationLineBundle p L V.val).obj
          ((localIso p L ev hs V).hom.app ⊤
            (pullbackSection (localMap p L ev hs V)
              (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X V) n).obj
              (RelativeProjectiveSpace.twistOneCoordinate ((frameCover M n hM).X V) n i)))) =
      localEvaluationSections p L ev (frame M n V) U.val hUV i := by
  exact (congrArg
    (fun t : GlobalSections (evaluationLineBundle p L V.val).obj ↦
      (openPullbackIso L.obj (p.preimage_mono hUV)).hom.app ⊤
        (pullbackSection (X.homOfLE (p.preimage_mono hUV))
          (evaluationLineBundle p L V.val).obj t))
    (localEvaluationTwistIso_coordinate p L ev (frame M n V) V.val le_rfl
      (hs V) i)).trans
    (localEvaluationSections_restrict p L ev (frame M n V) hUV le_rfl i)

/-- The coordinate criterion on the actual evaluation restriction square. -/
lemma localSquare_criterion {U V : (frameCover M n hM).I₀} (hUV : U ≤ V)
    (δ : (Scheme.Modules.pullback (localMap p L ev hs V)).obj
      (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X V) n).obj ⟶
      (evaluationLineBundle p L V.val).obj)
    (α : (Scheme.Modules.pullback (localMap p L ev hs U)).obj
      (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X U) n).obj ⟶
      (evaluationLineBundle p L U.val).obj)
    (β : (Scheme.Modules.pullback ((frameCocycle M n hM).chartFunctor.map
      (homOfLE hUV))).obj
        (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X V) n).obj ⟶
      (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X U) n).obj)
    (γ : (Scheme.Modules.pullback (X.homOfLE (p.preimage_mono hUV))).obj
      (evaluationLineBundle p L V.val).obj ⟶ (evaluationLineBundle p L U.val).obj)
    (hc : ∀ i, α.app ⊤ (pullbackSection (localMap p L ev hs U)
      (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X U) n).obj
      (β.app ⊤ (pullbackSection ((frameCocycle M n hM).chartFunctor.map
        (homOfLE hUV))
        (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X V) n).obj
        (RelativeProjectiveSpace.twistOneCoordinate ((frameCover M n hM).X V) n i)))) =
      γ.app ⊤ (pullbackSection (X.homOfLE (p.preimage_mono hUV))
        (evaluationLineBundle p L V.val).obj
        (δ.app ⊤ (pullbackSection (localMap p L ev hs V)
          (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X V) n).obj
          (RelativeProjectiveSpace.twistOneCoordinate ((frameCover M n hM).X V) n i))))) :
    PullbackSquareCompatible
      (localMap p L ev hs V) (localMap p L ev hs U)
      (X.homOfLE (p.preimage_mono hUV))
      ((frameCocycle M n hM).chartFunctor.map (homOfLE hUV))
      (localMap_chartMap p L ev hM hs hUV) δ α β γ := by
  exact pullback_comparison_square_between
    (X := (p ⁻¹ᵁ V.val).toScheme)
    (X' := (p ⁻¹ᵁ U.val).toScheme)
    (Y := (frameCocycle M n hM).chartFunctor.obj V)
    (Y' := (frameCocycle M n hM).chartFunctor.obj U)
    (M := (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X V) n).obj)
    (M' := (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X U) n).obj)
    (N := (evaluationLineBundle p L V.val).obj)
    (N' := (evaluationLineBundle p L U.val).obj)
    (RelativeProjectiveSpace.twistOne ((frameCover M n hM).X V) n).property
    (RelativeProjectiveSpace.twistOneCoordinate ((frameCover M n hM).X V) n)
    (isOpenCover_trivializationOpen
      (relativeProjectiveCoordinates_generate ((frameCover M n hM).X V) n))
    (localMap p L ev hs V) (localMap p L ev hs U)
    (X.homOfLE (p.preimage_mono hUV))
    ((frameCocycle M n hM).chartFunctor.map (homOfLE hUV))
    (localMap_chartMap p L ev hM hs hUV) δ α β γ hc

/-- The actual local degree-one comparisons respect the full frame transition
and the canonical square and open-restriction comparisons. -/
lemma localIso_compatible {U V : (frameCover M n hM).I₀} (hUV : U ≤ V) :
    PullbackSquareCompatible
      (localMap p L ev hs V) (localMap p L ev hs U)
      (X.homOfLE (p.preimage_mono hUV))
      ((frameCocycle M n hM).chartFunctor.map (homOfLE hUV))
      (localMap_chartMap p L ev hM hs hUV)
      (localIso p L ev hs V).hom (localIso p L ev hs U).hom
      ((frameCocycle M n hM).chartTwistIso (homOfLE hUV)).hom
      (openPullbackIso L.obj (p.preimage_mono hUV)).hom := by
  exact localSquare_criterion p L ev hM hs hUV
    (localIso p L ev hs V).hom (localIso p L ev hs U).hom
    ((frameCocycle M n hM).chartTwistIso (homOfLE hUV)).hom
    (openPullbackIso L.obj (p.preimage_mono hUV)).hom
    (fun i ↦ (localIso_chartTwistIso_coordinate p L ev hM hs hUV i).trans
      (localIso_restrict_coordinate p L ev hM hs hUV i).symm)

end EvaluationTwist

end Langlands.AlgebraicGeometry.ProjectiveBundle
