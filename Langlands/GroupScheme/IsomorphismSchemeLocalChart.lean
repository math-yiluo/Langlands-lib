import Langlands.GroupScheme.IsomorphismPresheaf
import Langlands.GroupScheme.IsomorphismSchemeBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationChart

/-! # Local representatives as charts of the full Isom presheaf -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.GroupScheme

namespace LocalGroupIso

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {G H : GroupScheme S}
    {U V : Over S'}

/-- Forgetting a change of base commutes with every parameter refinement. -/
theorem fromBaseChangeFamily_refine
    (e : LocalGroupIso ((baseChange b).obj G) ((baseChange b).obj H) U)
    (r : V ⟶ U) :
    (e.refine r).fromBaseChangeFamily b =
      (e.fromBaseChangeFamily b).refine ((Over.map b).map r) := by
  apply (baseChangeEquiv b).injective
  change ((e.refine r).fromBaseChangeFamily b).baseChangeFamily b =
    ((e.fromBaseChangeFamily b).refine ((Over.map b).map r)).baseChangeFamily b
  rw [baseChangeFamily_fromBaseChangeFamily, baseChangeFamily_refine,
    baseChangeFamily_fromBaseChangeFamily]

/-- The full family presheaf restricted to a new base is the new-base Isom presheaf. -/
def baseChangePresheafIso :
    (Over.map b).op ⋙ presheaf G H ≅
      presheaf ((baseChange b).obj G) ((baseChange b).obj H) :=
  NatIso.ofComponents (fun T => (baseChangeEquiv b).toIso) (fun r => by
    ext e
    exact baseChangeFamily_refine b e r.unop)

end LocalGroupIso

namespace GroupIsomorphismScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {G H : GroupScheme S}
    (I : GroupIsomorphismScheme
      ((GroupScheme.baseChange b).obj G) ((GroupScheme.baseChange b).obj H))

open Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The local parameter represents the restriction of the original Isom presheaf. -/
def localRepresentationIso :
    (schemeYoneda S').obj I.parameter ≅
      (Over.map b).op ⋙ LocalGroupIso.presheaf G H :=
  (Functor.RepresentableBy.equivUliftYonedaIso _ _ I.representableBy) ≪≫
    (LocalGroupIso.baseChangePresheafIso b).symm

/-- The local parameter, viewed as a scheme over the original base, maps to the new base. -/
def localChartProjection : (Over.map b).obj I.parameter ⟶ Over.mk b :=
  Over.homMk I.parameter.hom rfl

/-- The local universal family gives a chart into the full original-base Isom presheaf. -/
def localChart :
    (schemeYoneda S).obj ((Over.map b).obj I.parameter) ⟶ LocalGroupIso.presheaf G H :=
  LocalRepresentation.chart b I.parameter (I.localRepresentationIso b)

@[simp] theorem localChart_app {T : Over S} (p : T ⟶ (Over.map b).obj I.parameter) :
    (I.localChart b).app (op T) (ULift.up p) =
      (I.universalIso.fromBaseChangeFamily b).refine p := by
  change ((I.universalIso.refine (𝟙 I.parameter)).fromBaseChangeFamily b).refine p = _
  rw [LocalGroupIso.refine_id]

/-- Local parameter points classify the original-base families on new-base tests. -/
def localChartPointsEquiv (T : Over S') :
    (T ⟶ I.parameter) ≃ LocalGroupIso G H ((Over.map b).obj T) :=
  (I.pointsEquiv T).trans (LocalGroupIso.baseChangeEquiv b).symm

@[simp] theorem localChartPointsEquiv_apply (T : Over S') (p : T ⟶ I.parameter) :
    I.localChartPointsEquiv b T p =
      (I.universalIso.fromBaseChangeFamily b).refine ((Over.map b).map p) :=
  LocalGroupIso.fromBaseChangeFamily_refine b I.universalIso p

/-- A supplied local representative represents the product with the new-base scheme. -/
def localChartIso :
    (schemeYoneda S).obj ((Over.map b).obj I.parameter) ≅
      extProd (LocalGroupIso.presheaf G H) (Over.mk b) :=
  LocalRepresentation.chartProductIso b I.parameter (I.localRepresentationIso b)

@[reassoc (attr := simp)] theorem localChartIso_hom_fst :
    (I.localChartIso b).hom ≫ extProd.fst = I.localChart b := rfl

@[reassoc (attr := simp)] theorem localChartIso_hom_snd :
    (I.localChartIso b).hom ≫ extProd.snd =
      (schemeYoneda S).map (I.localChartProjection b) := rfl

end GroupIsomorphismScheme

end Langlands.GroupScheme
