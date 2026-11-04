import Langlands.AlgebraicGeometry.SchemeLimitRelativeClosedImmersionStatement
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Separatedness descent along actual affine-scheme limits -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineLimit

/-- Separatedness is detected at a stage for a qcqs relative morphism
whose source is quasi-compact over the affine base. -/
def RelativeSeparatednessDescent : Prop :=
  ∀ {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) {S X Y : Scheme.{u}}
    [IsAffine S] [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const I).obj S)
    (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact a]
    (c : Cone D) (_hc : IsLimit c) (p : c.pt ⟶ S)
    (_hp : ∀ i, c.π.app i ≫ t.app i = p),
      IsSeparated (baseChangeMap a b f w p) ↔
        ∃ i, IsSeparated (baseChangeMap a b f w (t.app i))

end Langlands.AlgebraicGeometry.AffineLimit
