import Langlands.AlgebraicGeometry.AffineLimitIsomorphismDescent

/-! # Relative affineness descent along affine scheme limits -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineLimit

/-- Relative affineness at an affine cofiltered limit is detected at one
level, for a qcqs morphism with quasi-compact target over the affine base. -/
def RelativeAffinenessDescent : Prop :=
  ∀ {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) {S X Y : Scheme.{u}}
    [IsAffine S] [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const I).obj S)
    (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact b]
    (c : Cone D) (_hc : IsLimit c) (p : c.pt ⟶ S)
    (_hp : ∀ i, c.π.app i ≫ t.app i = p),
      IsAffineHom (baseChangeMap a b f w p) ↔
        ∃ i, IsAffineHom (baseChangeMap a b f w (t.app i))

end Langlands.AlgebraicGeometry.AffineLimit
