import Langlands.AlgebraicGeometry.SchemeLimitModelMaps

/-! # Open-immersion descent for finitely presented models -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineLimit

/-- Open immersion of the actual relative map is detected at one level. -/
def RelativeOpenImmersionDescent : Prop :=
  ∀ {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) {S X Y : Scheme.{u}} [IsAffine S]
    [∀ i, IsAffine (D.obj i)] (t : D ⟶ (Functor.const I).obj S)
    (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
    [LocallyOfFinitePresentation a] [QuasiCompact a] [QuasiSeparated a]
    [LocallyOfFinitePresentation b] [QuasiCompact b] [QuasiSeparated b]
    (c : Cone D) (_hc : IsLimit c) (p : c.pt ⟶ S)
    (_hp : ∀ i, c.π.app i ≫ t.app i = p),
      IsOpenImmersion (baseChangeMap a b f w p) ↔
      ∃ i : I, IsOpenImmersion (baseChangeMap a b f w (t.app i))

end Langlands.AlgebraicGeometry.AffineLimit
