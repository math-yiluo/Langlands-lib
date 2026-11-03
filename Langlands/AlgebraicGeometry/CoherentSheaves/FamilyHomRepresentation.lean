import Langlands.AlgebraicGeometry.CoherentSheaves.IntrinsicModuleHomPresheaf
import Langlands.AlgebraicGeometry.FiniteLinearModelGluing

/-! # From intrinsic Hom models to actual family Hom representations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.CoherentSheaves.FamilyGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S) {T : Over S}
    (M N : FamilyGroupoid f T)

/-- The actual family Hom presheaf inherits local models from ordinary module Hom. -/
theorem homPresheaf_hasLocalModels_of_intrinsic
    (hModel : FiniteLinearEquations.HasLocalModels
      (intrinsicModuleHomPresheaf ((Picard.relativeProjection f).app T)
        M.of.obj N.of.obj)) :
    FiniteLinearEquations.HasLocalModels (homPresheaf f M N) :=
  hModel.of_iso (homPresheafIntrinsicIso f T M N).symm

/-- The full-slice natural comparison transfers fppf sheafness to actual family Hom. -/
theorem homPresheaf_isSheaf_of_intrinsic
    (hSheaf : Presheaf.IsSheaf (AlgebraicSpace.fppfTopology T.left)
      (intrinsicModuleHomPresheaf ((Picard.relativeProjection f).app T)
        M.of.obj N.of.obj)) :
    Presheaf.IsSheaf (AlgebraicSpace.fppfTopology T.left) (homPresheaf f M N) :=
  (Presheaf.isSheaf_of_iso_iff (homPresheafIntrinsicIso f T M N)).mpr hSheaf

/-- Intrinsic local models and sheafness give an actual affine locally finitely
presented scheme representing all coherent-family maps on the entire slice. -/
theorem exists_homRepresentation_of_intrinsic
    (hModel : FiniteLinearEquations.HasLocalModels
      (intrinsicModuleHomPresheaf ((Picard.relativeProjection f).app T)
        M.of.obj N.of.obj))
    (hSheaf : Presheaf.IsSheaf (AlgebraicSpace.fppfTopology T.left)
      (intrinsicModuleHomPresheaf ((Picard.relativeProjection f).app T)
        M.of.obj N.of.obj)) :
    ∃ H : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj H ≅ homPresheaf f M N) ∧
        IsAffineHom H.hom ∧ LocallyOfFinitePresentation H.hom := by
  obtain ⟨H, ⟨eH⟩, hAffine, hFP⟩ := hModel.exists_affine_representation hSheaf
  exact ⟨H, ⟨eH ≪≫ (homPresheafIntrinsicIso f T M N).symm⟩, hAffine, hFP⟩

/-- Chosen actual scheme, natural family Hom comparison, and the two properties
of the same structure map, from intrinsic local models and sheafness. -/
def homRepresentationOfIntrinsic
    (hModel : FiniteLinearEquations.HasLocalModels
      (intrinsicModuleHomPresheaf ((Picard.relativeProjection f).app T)
        M.of.obj N.of.obj))
    (hSheaf : Presheaf.IsSheaf (AlgebraicSpace.fppfTopology T.left)
      (intrinsicModuleHomPresheaf ((Picard.relativeProjection f).app T)
        M.of.obj N.of.obj)) :
    Σ H : Over T.left,
      { _e : (AlgebraicSpace.schemeYoneda T.left).obj H ≅ homPresheaf f M N //
        IsAffineHom H.hom ∧ LocallyOfFinitePresentation H.hom } :=
  let h := exists_homRepresentation_of_intrinsic f M N hModel hSheaf
  ⟨h.choose, h.choose_spec.1.some, h.choose_spec.2⟩

end Langlands.AlgebraicGeometry.CoherentSheaves.FamilyGroupoid
