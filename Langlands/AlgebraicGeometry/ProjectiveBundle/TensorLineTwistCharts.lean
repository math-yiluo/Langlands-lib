import Langlands.AlgebraicGeometry.ProjectiveBundle.TensorTwistTransition
import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameAtlasTwistRestriction
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.EqualCompositeTensor

/-! # Degree-one chart comparisons for tensor-line invariance -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule.RigidifiedModule
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Picard

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules

/-- Chart restriction for a composite pullback follows from associativity. -/
lemma compHom_local_restrict {X Y U V : Scheme.{u}}
    (F : X ⟶ Y) (jU : U ⟶ X) (jV : V ⟶ X) (r : U ⟶ V)
    (hr : r ≫ jV = jU) (kU : U ⟶ Y) (kV : V ⟶ Y)
    (hU : jU ≫ F = kU) (hV : jV ≫ F = kV) (hk : r ≫ kV = kU)
    (G : Y.Modules) {LU : U.Modules} {LV : V.Modules}
    (eU : (Scheme.Modules.pullback kU).obj G ⟶ LU)
    (eV : (Scheme.Modules.pullback kV).obj G ⟶ LV)
    (γ : (Scheme.Modules.pullback r).obj LV ⟶ LU)
    (he : (Scheme.Modules.pullback r).map eV ≫ γ =
      compHom r kV kU hk G ≫ eU) :
    (Scheme.Modules.pullback r).map (compHom jV F kV hV G ≫ eV) ≫ γ =
      compHom r jV jU hr ((Scheme.Modules.pullback F).obj G) ≫
        compHom jU F kU hU G ≫ eU := by
  simp only [Functor.map_comp, Category.assoc]
  rw [he, ← compHom_assoc_assoc r jV F jU kV kU hr hV hU hk G]

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames

variable {S : Scheme.{u}} {M N : S.Modules} {n : ℕ}
variable (hM : IsLocallyFreeOfRank M (n + 1)) (hN : IsLocallyFreeRankOne N)

/-- The chosen genuine line chart, expressed as a pullback trivialization. -/
def lineChartIso (U : (sourceAtlas hM hN).opens) :
    (Scheme.Modules.pullback U.val.ι).obj N ≅ structureSheaf U.val.toScheme :=
  ((Scheme.Modules.restrictFunctorIsoPullback U.val.ι).app N).symm ≪≫ U.property.2.some

/-- On a tensor chart, the pullback of the original line is actually trivial. -/
def baseLineChartIso (U : (sourceAtlas hM hN).opens) :
    (Scheme.Modules.pullback ((tensorAtlas hM hN).cocycle.chart U)).obj
      ((Scheme.Modules.pullback (tensorAtlas hM hN).toBase).obj N) ≅
        structureSheaf (RelativeProjectiveSpace U.val.toScheme n) :=
  squarePullbackIso U.val.ι ((tensorAtlas hM hN).cocycle.chart U)
      (RelativeProjectiveSpace.toBase U.val.toScheme n) (tensorAtlas hM hN).toBase
      ((tensorAtlas hM hN).cocycle.chart_toBase U) N ≪≫
    (Scheme.Modules.pullback (RelativeProjectiveSpace.toBase U.val.toScheme n)).mapIso
      (lineChartIso hM hN U) ≪≫
    pullbackUnitIso (RelativeProjectiveSpace.toBase U.val.toScheme n)

/-- The source degree-one bundle, pulled back along the actual tensor-atlas isomorphism. -/
def sourceTwistChartIso (U : (sourceAtlas hM hN).opens) :
    (Scheme.Modules.pullback ((tensorAtlas hM hN).cocycle.chart U)).obj
      ((Scheme.Modules.pullback (atlasIso hM hN).hom).obj
        ((sourceAtlas hM hN).twistOne hM).obj) ≅
      (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj :=
  compIso ((tensorAtlas hM hN).cocycle.chart U) (atlasIso hM hN).hom
      ((sourceAtlas hM hN).cocycle.chart U) (chart_atlasIso_hom hM hN U)
      ((sourceAtlas hM hN).twistOne hM).obj ≪≫
    (sourceAtlas hM hN).twistChartIso hM U

/-- The tensor degree-one bundle times the base line has the same local standard form. -/
def tensorTwistChartIso (U : (sourceAtlas hM hN).opens) :
    (Scheme.Modules.pullback ((tensorAtlas hM hN).cocycle.chart U)).obj
      (tensorObj ((tensorAtlas hM hN).twistOne (isLocallyFreeOfRank_tensor hM hN)).obj
        ((Scheme.Modules.pullback (tensorAtlas hM hN).toBase).obj N)) ≅
      (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj := by
  let j := (tensorAtlas hM hN).cocycle.chart U
  letI := pullbackTensorComparisonIsIso j
  exact (asIso (pullbackTensorComparison j)).app
      (((tensorAtlas hM hN).twistOne (isLocallyFreeOfRank_tensor hM hN)).obj,
        (Scheme.Modules.pullback (tensorAtlas hM hN).toBase).obj N) ≪≫
    (Langlands.Scheme.Modules.tensorFunctor _).mapIso
      (((tensorAtlas hM hN).twistChartIso (isLocallyFreeOfRank_tensor hM hN) U).prod
        (baseLineChartIso hM hN U)) ≪≫
    tensorRightUnitor (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj

/-- The actual local tensor-line degree-one comparison. -/
def twistChartIso (U : (sourceAtlas hM hN).opens) :
    (Scheme.Modules.pullback ((tensorAtlas hM hN).cocycle.chart U)).obj
      ((Scheme.Modules.pullback (atlasIso hM hN).hom).obj
        ((sourceAtlas hM hN).twistOne hM).obj) ≅
      (Scheme.Modules.pullback ((tensorAtlas hM hN).cocycle.chart U)).obj
        (tensorObj ((tensorAtlas hM hN).twistOne (isLocallyFreeOfRank_tensor hM hN)).obj
          ((Scheme.Modules.pullback (tensorAtlas hM hN).toBase).obj N)) :=
  sourceTwistChartIso hM hN U ≪≫ (tensorTwistChartIso hM hN U).symm

end Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames
