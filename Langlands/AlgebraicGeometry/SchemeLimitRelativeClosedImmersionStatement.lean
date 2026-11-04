import Langlands.AlgebraicGeometry.SchemeLimitAffineStatement
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Relative closed-immersion descent along affine scheme limits -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineLimit

/-- A finite-type quasi-separated relative morphism with quasi-compact
relative target is a closed immersion at an affine limit if and only if
it is a closed immersion after base change to one level. -/
def RelativeClosedImmersionDescent : Prop :=
  ∀ {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) {S X Y : Scheme.{u}}
    [IsAffine S] [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const I).obj S)
    (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
    [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f] [QuasiCompact b]
    (c : Cone D) (_hc : IsLimit c) (p : c.pt ⟶ S)
    (_hp : ∀ i, c.π.app i ≫ t.app i = p),
      IsClosedImmersion (baseChangeMap a b f w p) ↔
        ∃ i, IsClosedImmersion (baseChangeMap a b f w (t.app i))

end Langlands.AlgebraicGeometry.AffineLimit
