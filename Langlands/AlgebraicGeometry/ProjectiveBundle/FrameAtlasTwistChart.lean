import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameAtlasTwist
import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameChoiceTwistChart

/-! # Degree-one comparison in a common chart of genuine frame atlases -/

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
variable (a b : FrameAtlas M n) (U : S.Opens)
variable (ha : U ∈ a.opens) (hb : U ∈ b.opens)

/-- The actual relative actions on a common basis open compose through the fixed frame. -/
lemma changeCoordinate_relativeLinearAction_comp :
    linearAction U.toScheme.toSpecΓ (a.changeCoordinate b U ha hb) ≫
        linearAction U.toScheme.toSpecΓ (b.comparisonCoordinate ⟨U, hb⟩) =
      linearAction U.toScheme.toSpecΓ (a.comparisonCoordinate ⟨U, ha⟩) := by
  rw [linearAction_comp, a.changeCoordinate_comparison b U ha hb]

set_option linter.defProp false in
/-- The constructed degree-one comparison has the actual dual-frame formula on a common open. -/
def comparisonTwistIso_chart (hM : IsLocallyFreeOfRank M (n + 1)) :=
  @LinearSystem.relativeLinearActionTwistIso_chart
    (Γ(U.toScheme, ⊤)) (Γ(U.toScheme, ⊤)).commRing
    U.toScheme n U.toScheme.toSpecΓ
    (a.changeCoordinate b U ha hb) (b.comparisonCoordinate ⟨U, hb⟩)
    (a.comparisonCoordinate ⟨U, ha⟩)
    (a.changeCoordinate_comparison b U ha hb)
    (a.changeCoordinate_relativeLinearAction_comp b U ha hb)
    a.bundle b.bundle (frameBundle M n hM)
    (a.cocycle.chart ⟨U, ha⟩) (b.cocycle.chart ⟨U, hb⟩)
    (FrameBundle.chart hM (a.toFrameOpen ⟨U, ha⟩))
    (a.comparisonIso hM b).hom (a.toFrameBundleIso hM).hom
    (b.toFrameBundleIso hM).hom (a.comparisonIso_hom_toFrameBundle hM b)
    (a.chart_comparisonIso_hom hM b U ha hb)
    (a.chart_toFrameBundleIso_hom hM ⟨U, ha⟩)
    (b.chart_toFrameBundleIso_hom hM ⟨U, hb⟩)
    (FrameBundle.twistOne hM).obj
    (FrameBundle.twistOneModuleIso hM (a.toFrameOpen ⟨U, ha⟩))

end Langlands.AlgebraicGeometry.ProjectiveBundle.FrameAtlas
