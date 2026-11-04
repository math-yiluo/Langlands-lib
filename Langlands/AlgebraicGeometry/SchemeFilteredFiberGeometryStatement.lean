import Langlands.AlgebraicGeometry.SchemeFiberGeometry
import Langlands.AlgebraicGeometry.SchemeFilteredRingTail
import Langlands.AlgebraicGeometry.AffineLimitIsomorphismDescent

/-! # Descent of nonempty geometrically connected pure-dimensional fibres -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open AffineLimit SchemeFiberGeometry

/-- The last clause of Conrad's Theorem 3.4(2), retaining both finitely
presented models and the actual original ring maps. -/
def FinitePresentationInitialRingFiberGeometryDescent : Prop :=
  ∀ (d : ℕ) {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c) (j₀ : J)
    (X Y : Over (Spec (F.obj j₀))) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom],
      NonemptyGeometricallyConnectedPureDimensionFibers d
        (baseChangeMap X.hom Y.hom f.left (Over.w f)
          (Spec.map (c.ι.app j₀))) ↔
      ∃ j : Under j₀, NonemptyGeometricallyConnectedPureDimensionFibers d
        (baseChangeMap X.hom Y.hom f.left (Over.w f) (Spec.map (F.map j.hom)))

end Langlands.AlgebraicGeometry.SchemeLimitModel
