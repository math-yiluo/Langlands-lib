import Langlands.AlgebraicGeometry.Picard.OpenImmersionIdealClosure
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Sections of the actual ideal closure -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.OpenImmersionIdeal

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  {D : Y.Modules} (s : D ⟶ SheafOfModules.unit Y.ringCatSheaf)

omit [IsOpenImmersion j] in
/-- A section belongs to the ideal closure precisely when its restriction belongs to the
original ideal. -/
lemma inclusion_range_iff (W : X.Opens) (c : Γ(X, W)) :
    (∃ m : Γ(closure j s, W), (inclusion j s).app W m = c) ↔
      ∃ d : Γ(D, j ⁻¹ᵁ W), s.app (j ⁻¹ᵁ W) d = j.app W c := by
  let F : X.Modules ⥤ Type u := Scheme.Modules.toPresheaf X ⋙
    (evaluation X.Opensᵒᵖ Ab).obj (.op W) ⋙ forget Ab
  have : PreservesFiniteLimits (Scheme.Modules.toPresheaf X) := inferInstance
  have : PreservesFiniteLimits ((evaluation X.Opensᵒᵖ Ab).obj (.op W)) := inferInstance
  have : PreservesFiniteLimits (forget Ab.{u}) := inferInstance
  have : PreservesFiniteLimits F := by
    dsimp only [F]
    infer_instance
  have hp := (IsPullback.of_hasPullback
    (Langlands.Scheme.Modules.unitToPushforwardUnit j)
    ((Scheme.Modules.pushforward j).map s)).map F
  exact Set.ext_iff.mp (Types.range_fst_of_isPullback hp) c

end Langlands.AlgebraicGeometry.Picard.OpenImmersionIdeal
