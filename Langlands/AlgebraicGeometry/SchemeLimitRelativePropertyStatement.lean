import Langlands.AlgebraicGeometry.SchemeLimitAffineStatement
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Smoothness and flatness along affine scheme limits -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineLimit

/-- A relative property holds at the limit precisely when it holds at one
stage, for a finitely presented morphism and a quasi-compact relative target. -/
def RelativePropertyDescent (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) {S X Y : Scheme.{u}}
    [IsAffine S] [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const I).obj S)
    (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] [QuasiCompact b]
    (c : Cone D) (_hc : IsLimit c) (p : c.pt ⟶ S)
    (_hp : ∀ i, c.π.app i ≫ t.app i = p),
      P (baseChangeMap a b f w p) ↔
        ∃ i, P (baseChangeMap a b f w (t.app i))

/-- Smoothness is detected at one stage of the actual affine limit. -/
def RelativeSmoothDescent : Prop :=
  RelativePropertyDescent.{u} @Smooth

/-- Flatness is detected at one stage of the actual affine limit. -/
def RelativeFlatDescent : Prop :=
  RelativePropertyDescent.{u} @Flat

/-- Both properties descend for arbitrary relative source and target schemes. -/
def RelativeSmoothFlatDescent : Prop :=
  RelativeSmoothDescent.{u} ∧ RelativeFlatDescent.{u}

end Langlands.AlgebraicGeometry.AffineLimit
