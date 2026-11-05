import Langlands.GroupScheme.IntegralModel.LocalField
import Langlands.GroupScheme.Reductive.Basic
import Langlands.AlgebraicGeometry.DvrSmoothFibers

/-! # Smoothness of the supplied local model with reductive fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IntegralModel

/-- The reductive generic and full special fibres make the actual supplied
integral model smooth, with no further model hypothesis. -/
theorem isSmooth_of_reductive_localField
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} (M : IntegralModel ↥𝒪[F] F G)
    (hG : IsConnectedReductive G)
    (hSpecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group)) :
    M.IsSmooth := by
  have : Smooth G.X.hom := hG.smooth
  have : Smooth (pullback.snd M.group.X.hom (Spec.algebraMap ↥𝒪[F] F)) := by
    change Smooth M.genericFibre.X.hom
    have he : M.genericFibre.X.hom =
        M.genericIso.hom.hom.hom.left ≫ G.X.hom := by
      exact M.genericIso.hom.hom.hom.w.symm
    rw [he]
    infer_instance
  have : Smooth (pullback.snd M.group.X.hom (Spec.algebraMap ↥𝒪[F] 𝓀[F])) :=
    hSpecial.smooth
  exact Langlands.AlgebraicGeometry.smooth_of_generic_special_fibers
    ↥𝒪[F] F M.group.X.hom

end Langlands.GroupScheme.IntegralModel
