import Langlands.AlgebraicGeometry.Picard.LocalComparisonStatement
import Langlands.AlgebraicGeometry.Modules.PullbackTensorStatement
import Langlands.AlgebraicGeometry.Modules.PullbackUnit

/-! # Algebraic assembly of isomorphisms from pullback comparisons

This construction consumes an explicit triviality-detection principle and
explicit tensor prerequisites. It does not establish their geometric instances.
-/

universe u

open CategoryTheory MonoidalCategory BraidedCategory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

/-- A comparison after pullback trivializes the tensor with an inverse. -/
def pullbackTensorInverseTrivialization
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {S T : Scheme.{u}} (f : T ⟶ S) {L M N : S.Modules}
    (e : (Scheme.Modules.pullback f).obj L ≅ (Scheme.Modules.pullback f).obj M)
    (inverse : Langlands.Scheme.Modules.tensorObj M N ≅ structureSheaf S) :
    (Scheme.Modules.pullback f).obj (Langlands.Scheme.Modules.tensorObj L N) ≅
      structureSheaf T := by
  letI := preservation f
  exact (asIso (pullbackTensorComparison f)).app (L, N) ≪≫
    (tensorFunctor T).mapIso (e.prod (Iso.refl _)) ≪≫
    ((asIso (pullbackTensorComparison f)).app (M, N)).symm ≪≫
    (Scheme.Modules.pullback f).mapIso inverse ≪≫ pullbackUnitIso f

/-- If triviality is detected by three pullbacks, their comparisons detect
isomorphism of actual line bundles, under the explicit tensor prerequisites. -/
def lineBundleIsoOfThreePullbackComparisons
    {S T₁ T₂ T₃ : Scheme.{u}}
    (comparison : LocallyFreeRankOneIffTensorInvertibleStatement S)
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (f₁ : T₁ ⟶ S) (f₂ : T₂ ⟶ S) (f₃ : T₃ ⟶ S)
    (triviality : ∀ D : LineBundle S,
      Nonempty ((Scheme.Modules.pullback f₁).obj D.obj ≅ structureSheaf T₁) →
      Nonempty ((Scheme.Modules.pullback f₂).obj D.obj ≅ structureSheaf T₂) →
      Nonempty ((Scheme.Modules.pullback f₃).obj D.obj ≅ structureSheaf T₃) →
      Nonempty (D.obj ≅ structureSheaf S))
    (L M : LineBundle S)
    (e₁ : (Scheme.Modules.pullback f₁).obj L.obj ≅
      (Scheme.Modules.pullback f₁).obj M.obj)
    (e₂ : (Scheme.Modules.pullback f₂).obj L.obj ≅
      (Scheme.Modules.pullback f₂).obj M.obj)
    (e₃ : (Scheme.Modules.pullback f₃).obj L.obj ≅
      (Scheme.Modules.pullback f₃).obj M.obj) :
    L.obj ≅ M.obj := Classical.choice <| by
  have hL := (comparison L.obj).mpr L.property
  obtain ⟨N, ⟨inverse⟩⟩ := (comparison M.obj).mpr M.property
  have hN : Langlands.CategoryTheory.TensorInvertible N :=
    ⟨M.obj, ⟨(β_ N M.obj) ≪≫ inverse⟩⟩
  let difference : LineBundle S :=
    ⟨Langlands.Scheme.Modules.tensorObj L.obj N, (comparison _).mp
      (Langlands.CategoryTheory.TensorInvertible.of_iso
        (localizedTensorIso _ L.obj N) (hL.tensor hN))⟩
  let explicitInverse : Langlands.Scheme.Modules.tensorObj M.obj N ≅ structureSheaf S :=
    (localizedTensorIso _ M.obj N).symm ≪≫ inverse
  obtain ⟨trivialization⟩ := triviality difference
    ⟨pullbackTensorInverseTrivialization preservation f₁ e₁ explicitInverse⟩
    ⟨pullbackTensorInverseTrivialization preservation f₂ e₂ explicitInverse⟩
    ⟨pullbackTensorInverseTrivialization preservation f₃ e₃ explicitInverse⟩
  exact ⟨(ρ_ L.obj).symm ≪≫
    (Iso.refl L.obj ⊗ᵢ ((β_ N M.obj) ≪≫ inverse).symm) ≪≫
    (α_ L.obj N M.obj).symm ≪≫
    ((localizedTensorIso _ L.obj N ≪≫ trivialization) ⊗ᵢ Iso.refl M.obj) ≪≫
    (λ_ M.obj)⟩

end Langlands.AlgebraicGeometry.Picard
