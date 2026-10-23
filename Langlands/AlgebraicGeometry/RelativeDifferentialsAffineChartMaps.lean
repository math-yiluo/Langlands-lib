import Langlands.AlgebraicGeometry.RelativeDifferentialsSpecMap
import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChange
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Canonical affine-chart comparison maps for relative differentials

The actual restricted differential sheaf and its algebraic affine model map to
a common Spec differential sheaf. Invertibility of these maps is not asserted here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace Langlands.Scheme

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
  {U : S.Opens} {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (e : V ≤ f ⁻¹ᵁ U)

/-- The canonical square comparison on the spectra of the affine chart rings. -/
def relativeDifferentialsAffineChartSquareMap :
    (pullback hV.fromSpec).obj (relativeDifferentials f) ⟶
      relativeDifferentials (Spec.map (f.appLE U V e)) :=
  relativeDifferentialsSquareMap hV.fromSpec hU.fromSpec
    (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e).symm

/-- The square's adjoint sends every actual differential to its pulled-back differential. -/
lemma relativeDifferentialsAffineChartSquareMap_adjoint_app
    (W : X.Opens) (a : Γ(X, W)) :
    ((pullbackPushforwardAdjunction hV.fromSpec).homEquiv _ _
      (relativeDifferentialsAffineChartSquareMap f hU hV e)).app W
        ((relativeDifferentialsDerivation f).app W a) =
      (relativeDifferentialsDerivation (Spec.map (f.appLE U V e))).app
        (hV.fromSpec ⁻¹ᵁ W) (hV.fromSpec.app W a) :=
  relativeDifferentialsSquareMap_adjoint_app _ _ _ W a

/-- The differential formula uniquely determines the chart-square comparison. -/
lemma relativeDifferentialsAffineChartSquareMap_unique_of_app
    (α : (pullback hV.fromSpec).obj (relativeDifferentials f) ⟶
      relativeDifferentials (Spec.map (f.appLE U V e)))
    (h : ∀ (W : X.Opens) (a : Γ(X, W)),
      ((pullbackPushforwardAdjunction hV.fromSpec).homEquiv _ _ α).app W
        ((relativeDifferentialsDerivation f).app W a) =
      (relativeDifferentialsDerivation (Spec.map (f.appLE U V e))).app
        (hV.fromSpec ⁻¹ᵁ W) (hV.fromSpec.app W a)) :
    α = relativeDifferentialsAffineChartSquareMap f hU hV e :=
  relativeDifferentialsSquareMap_unique_of_app _ _ _ α h

/-- Restriction to a chart is pullback first to its spectrum and then along its chart isomorphism. -/
def relativeDifferentialsAffineChartPullbackIso :
    (relativeDifferentials f).restrict V.ι ≅
      (pullback hV.isoSpec.hom).obj
        ((pullback hV.fromSpec).obj (relativeDifferentials f)) :=
  (restrictFunctorIsoPullback V.ι).app _ ≪≫
    (pullbackCongr hV.isoSpec_hom_fromSpec.symm).app _ ≪≫
    (pullbackComp hV.isoSpec.hom hV.fromSpec).symm.app _

/-- The restriction-to-Spec comparison before using its invertibility. -/
def relativeDifferentialsAffineChartToSpecMap :
    (relativeDifferentials f).restrict V.ι ⟶
      (pullback hV.isoSpec.hom).obj
        (relativeDifferentials (Spec.map (f.appLE U V e))) :=
  (relativeDifferentialsAffineChartPullbackIso f hV).hom ≫
    (pullback hV.isoSpec.hom).map (relativeDifferentialsAffineChartSquareMap f hU hV e)

/-- The affine model of differentials, with the chart ring-map algebra structure. -/
def relativeDifferentialsAffineChartModel : V.toScheme.Modules :=
  letI := (f.appLE U V e).hom.toAlgebra
  (pullback hV.isoSpec.hom).obj
    (tilde (ModuleCat.of Γ(X, V) (KaehlerDifferential Γ(S, U) Γ(X, V))))

/-- The Spec comparison transported to the chart. -/
def relativeDifferentialsAffineChartFromModelMap :
    relativeDifferentialsAffineChartModel f hV e ⟶
      (pullback hV.isoSpec.hom).obj
        (relativeDifferentials (Spec.map (f.appLE U V e))) := by
  letI := (f.appLE U V e).hom.toAlgebra
  exact (pullback hV.isoSpec.hom).map (relativeDifferentialsSpecMap Γ(S, U) Γ(X, V))

/-- An algebraic basis gives a free-sheaf trivialization of the chart model. -/
def relativeDifferentialsAffineChartModelBasisIso (ι : Type u)
    (b : letI := (f.appLE U V e).hom.toAlgebra
      Module.Basis ι Γ(X, V) (KaehlerDifferential Γ(S, U) Γ(X, V))) :
    relativeDifferentialsAffineChartModel f hV e ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) ι := by
  letI := (f.appLE U V e).hom.toAlgebra
  exact (pullback hV.isoSpec.hom).mapIso
      ((tilde.functor Γ(X, V)).mapIso b.repr.toModuleIso ≪≫ tildeFinsupp ι) ≪≫
    SheafOfModules.pullbackObjFreeIso hV.isoSpec.hom.toRingCatSheafHom ι

end Langlands.Scheme
