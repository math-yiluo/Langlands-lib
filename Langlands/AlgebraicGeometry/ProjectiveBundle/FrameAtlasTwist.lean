import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameAtlas
import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameChoiceTwist

/-! # Degree-one bundles across genuine frame atlases -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule.RigidifiedModule
open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.FrameAtlas

variable {S : Scheme.{u}} {M : S.Modules} {n : ℕ}
variable (a : FrameAtlas M n)

/-- The comparison of two actual atlas constructions factors through the fixed bundle. -/
lemma comparisonIso_hom_toFrameBundle (hM : IsLocallyFreeOfRank M (n + 1))
    (b : FrameAtlas M n) :
    (a.comparisonIso hM b).hom ≫ (b.toFrameBundleIso hM).hom =
      (a.toFrameBundleIso hM).hom := by
  simp [comparisonIso]

/-- Composition of the actual atlas comparisons, in scheme-map form. -/
lemma comparisonIso_hom_comp (hM : IsLocallyFreeOfRank M (n + 1))
    (b c : FrameAtlas M n) :
    (a.comparisonIso hM b).hom ≫ (b.comparisonIso hM c).hom =
      (a.comparisonIso hM c).hom :=
  congrArg Iso.hom (a.comparisonIso_trans hM b c)

/-- The actual degree-one line bundle on a projective scheme from any frame basis. -/
def twistOne (hM : IsLocallyFreeOfRank M (n + 1)) : LineBundle a.bundle :=
  ⟨(Scheme.Modules.pullback (a.toFrameBundleIso hM).hom).obj
      (FrameBundle.twistOne hM).obj,
    (FrameBundle.twistOne hM).property.pullback (a.toFrameBundleIso hM).hom⟩

/-- Degree one is preserved by the constructed comparison between different frame bases. -/
def comparisonTwistIso (hM : IsLocallyFreeOfRank M (n + 1)) (b : FrameAtlas M n) :
    (Scheme.Modules.pullback (a.comparisonIso hM b).hom).obj (b.twistOne hM).obj ≅
      (a.twistOne hM).obj :=
  compIso (a.comparisonIso hM b).hom (b.toFrameBundleIso hM).hom
    (a.toFrameBundleIso hM).hom (a.comparisonIso_hom_toFrameBundle hM b)
    (FrameBundle.twistOne hM).obj

/-- The degree-one comparison as an isomorphism of line bundles. -/
def comparisonTwistLineIso (hM : IsLocallyFreeOfRank M (n + 1)) (b : FrameAtlas M n) :
    (LineBundle.pullback (a.comparisonIso hM b).hom).obj (b.twistOne hM) ≅
      a.twistOne hM :=
  ObjectProperty.isoMk _ (a.comparisonTwistIso hM b)

/-- The degree-one comparisons compose by the canonical pullback associativity map. -/
lemma comparisonTwistIso_comp (hM : IsLocallyFreeOfRank M (n + 1))
    (b c : FrameAtlas M n) :
    (Scheme.Modules.pullback (a.comparisonIso hM b).hom).map
        (compIso (b.comparisonIso hM c).hom (c.toFrameBundleIso hM).hom
          (b.toFrameBundleIso hM).hom (b.comparisonIso_hom_toFrameBundle hM c)
          (FrameBundle.twistOne hM).obj).hom ≫
      (compIso (a.comparisonIso hM b).hom (b.toFrameBundleIso hM).hom
        (a.toFrameBundleIso hM).hom (a.comparisonIso_hom_toFrameBundle hM b)
        (FrameBundle.twistOne hM).obj).hom =
      compHom (a.comparisonIso hM b).hom (b.comparisonIso hM c).hom
          (a.comparisonIso hM c).hom (a.comparisonIso_hom_comp hM b c)
          ((Scheme.Modules.pullback (c.toFrameBundleIso hM).hom).obj
            (FrameBundle.twistOne hM).obj) ≫
        (compIso (a.comparisonIso hM c).hom (c.toFrameBundleIso hM).hom
          (a.toFrameBundleIso hM).hom (a.comparisonIso_hom_toFrameBundle hM c)
          (FrameBundle.twistOne hM).obj).hom := by
  simpa only [compIso_hom] using (LineBundleFlatDescent.compIso_assoc
    (a.comparisonIso hM b).hom (b.comparisonIso hM c).hom
    (c.toFrameBundleIso hM).hom (a.comparisonIso hM c).hom
    (b.toFrameBundleIso hM).hom (a.toFrameBundleIso hM).hom
    (a.comparisonIso_hom_comp hM b c)
    (b.comparisonIso_hom_toFrameBundle hM c)
    (a.comparisonIso_hom_toFrameBundle hM b)
    (a.comparisonIso_hom_toFrameBundle hM c) (FrameBundle.twistOne hM).obj).symm

/-- For the same atlas the comparison is the canonical pullback along the identity. -/
lemma comparisonTwistIso_refl (hM : IsLocallyFreeOfRank M (n + 1)) :
    a.comparisonTwistIso hM a =
      (Scheme.Modules.pullbackCongr
          (congrArg Iso.hom (a.comparisonIso_refl hM))).app (a.twistOne hM).obj ≪≫
        (Scheme.Modules.pullbackId a.bundle).app (a.twistOne hM).obj :=
  compIso_id_left_congr (a.comparisonIso hM a).hom (a.toFrameBundleIso hM).hom
    (congrArg Iso.hom (a.comparisonIso_refl hM))
    (a.comparisonIso_hom_toFrameBundle hM a) (FrameBundle.twistOne hM).obj

/-- The standard degree-one module in each chart of a genuine frame basis. -/
def twistChartIso (hM : IsLocallyFreeOfRank M (n + 1)) (U : a.opens) :
    (Scheme.Modules.pullback (a.cocycle.chart U)).obj (a.twistOne hM).obj ≅
      (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj :=
  squarePullbackIso (FrameBundle.chart hM (a.toFrameOpen U)) (a.cocycle.chart U)
      (globalLinearAction n (a.comparisonCoordinate U)) (a.toFrameBundleIso hM).hom
      (a.chart_toFrameBundleIso_hom hM U) (FrameBundle.twistOne hM).obj ≪≫
    (Scheme.Modules.pullback (globalLinearAction n (a.comparisonCoordinate U))).mapIso
      (FrameBundle.twistOneModuleIso hM (a.toFrameOpen U)) ≪≫
    LinearSystem.globalLinearActionTwistIso U.val.toScheme n (a.comparisonCoordinate U)

/-- The actual dual-coordinate change on an open that belongs to two frame bases. -/
abbrev changeCoordinate (b : FrameAtlas M n) (U : S.Opens)
    (ha : U ∈ a.opens) (hb : U ∈ b.opens) :=
  coordinatesOnOpen n U
    ((a.frame ⟨U, ha⟩).dual.change (b.frame ⟨U, hb⟩).dual U le_rfl le_rfl)

/-- Changes between the two genuine frames factor their changes to the fixed frame. -/
lemma changeCoordinate_comparison (b : FrameAtlas M n) (U : S.Opens)
    (ha : U ∈ a.opens) (hb : U ∈ b.opens) :
    (a.changeCoordinate b U ha hb).trans (b.comparisonCoordinate ⟨U, hb⟩) =
      a.comparisonCoordinate ⟨U, ha⟩ := by
  dsimp only [changeCoordinate, comparisonCoordinate, coordinatesOnOpen]
  rw [← ProjectiveSpace.coordinateBaseChange_trans, LocalFrame.change_trans]

/-- The atlas comparison has the genuine dual-frame formula on every common basis open. -/
lemma chart_comparisonIso_hom (hM : IsLocallyFreeOfRank M (n + 1))
    (b : FrameAtlas M n) (U : S.Opens) (ha : U ∈ a.opens) (hb : U ∈ b.opens) :
    a.cocycle.chart ⟨U, ha⟩ ≫ (a.comparisonIso hM b).hom =
      globalLinearAction n (a.changeCoordinate b U ha hb) ≫
        b.cocycle.chart ⟨U, hb⟩ := by
  apply (cancel_mono (b.toFrameBundleIso hM).hom).mp
  rw [Category.assoc, a.comparisonIso_hom_toFrameBundle,
    a.chart_toFrameBundleIso_hom, Category.assoc, b.chart_toFrameBundleIso_hom]
  dsimp only [comparisonChart]
  rw [← Category.assoc, globalLinearAction_comp, a.changeCoordinate_comparison]

end Langlands.AlgebraicGeometry.ProjectiveBundle.FrameAtlas
