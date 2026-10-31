import Langlands.AlgebraicGeometry.LocalSectionTrace
import Langlands.AlgebraicGeometry.LocalDeterminantTransport

/-! # Actual local trace transport under scheme pullback -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

namespace Langlands.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} {M : Y.Modules} {N : X.Modules}
    {U : Y.Opens} {I : Type u} [Fintype I]

/-- Traces of a global endomorphism agree on every common smaller chart open. -/
theorem localSectionTrace_overlap
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    {U' W : Y.Opens} {J : Type u} [Fintype J]
    (e' : SheafOfModules.free (R := Y.ringCatSheaf.over U') J ≅ M.over U')
    (a : End M) (i : W ⟶ U) (j : W ⟶ U') :
    localSectionTrace e (a.over U) (Over.mk i) =
      localSectionTrace e' (a.over U') (Over.mk j) := by
  rw [localSectionTrace_eq_trace, localSectionTrace_eq_trace]
  rfl

/-- In the actual transported pullback chart the trace is coefficient pullback. -/
theorem localSectionTrace_pullback_transport (f : X ⟶ Y)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (h : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U) ≅
      N.over (f ⁻¹ᵁ U))
    (a : End (M.over U)) (b : End (N.over (f ⁻¹ᵁ U)))
    (hab : localHomPullback f U a ≫ h.hom = h.hom ≫ b) (V : Over U) :
    f.app V.left (localSectionTrace e a V) =
      localSectionTrace (chartFreePullbackTransportIso f e h) b
        (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom)) := by
  unfold localSectionTrace
  rw [localSectionEndomorphism_toMatrix_pullback_transport f e h a b hab V]
  simp [Matrix.trace, Matrix.diag_apply]

/-- Every finite target chart computes the same actual pulled-back trace. -/
theorem localSectionTrace_pullback_transport_any_chart (f : X ⟶ Y)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (h : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U) ≅
      N.over (f ⁻¹ᵁ U))
    {J : Type u} [Fintype J]
    (e' : SheafOfModules.free (R := X.ringCatSheaf.over (f ⁻¹ᵁ U)) J ≅
      N.over (f ⁻¹ᵁ U))
    (a : End (M.over U)) (b : End (N.over (f ⁻¹ᵁ U)))
    (hab : localHomPullback f U a ≫ h.hom = h.hom ≫ b) (V : Over U) :
    f.app V.left (localSectionTrace e a V) =
      localSectionTrace e' b
        (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom)) := by
  rw [localSectionTrace_pullback_transport f e h a b hab V]
  exact localSectionTrace_trivialization_independent _ e' b _

end Langlands.Scheme.Modules
