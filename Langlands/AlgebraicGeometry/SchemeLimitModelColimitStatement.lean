import Langlands.AlgebraicGeometry.SchemeLimitModelColimit

/-! # Relative Hom colimit comparison over cofiltered affine bases -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

/-- The canonical actual Hom colimit comparison has the separate injectivity
and surjectivity hypotheses, and its actual base-change cocone is colimiting. -/
def ModelHomColimitComparison : Prop :=
  ∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (S X Y : Scheme.{u}) (t : D ⟶ (Functor.const I).obj S)
    (a : X ⟶ S) (b : Y ⟶ S) (c : Cone D) (_hc : IsLimit c)
    (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p),
    (QuasiCompact a → LocallyOfFiniteType b →
      Function.Injective (homColimitMap D t a b c p hp)) ∧
    (QuasiCompact a → QuasiSeparated a → LocallyOfFinitePresentation b →
      Function.Surjective (homColimitMap D t a b c p hp)) ∧
    (QuasiCompact a → QuasiSeparated a → LocallyOfFinitePresentation b →
      Function.Bijective (homColimitMap D t a b c p hp) ∧
        Nonempty (IsColimit (homCocone D t a b c p hp)))

end Langlands.AlgebraicGeometry.SchemeLimitModel
