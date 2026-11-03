import Langlands.AlgebraicGeometry.SchemeLimitModelMaps

/-! # Morphism and prescribed-isomorphism descent for nonaffine models -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

/-- Actual model morphisms factor at a level, equality is eventual, and a
prescribed limit isomorphism descends, with the separate finiteness hypotheses. -/
def ModelMorphismDescent : Prop :=
  ∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (S X Y : Scheme.{u}) (t : D ⟶ (Functor.const I).obj S)
    (a : X ⟶ S) (b : Y ⟶ S) (c : Cone D) (_hc : IsLimit c)
    (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p),
    (QuasiCompact a → QuasiSeparated a → LocallyOfFinitePresentation b →
      ∀ f : LimitHom a b p, ∃ (i : I) (fi : LevelHom D t a b i),
        toLimit D t a b c p hp i fi = f) ∧
    (QuasiCompact a → LocallyOfFiniteType b →
      ∀ (i j : I) (fi : LevelHom D t a b i) (fj : LevelHom D t a b j),
        toLimit D t a b c p hp i fi = toLimit D t a b c p hp j fj →
        ∃ (k : I) (r : k ⟶ i) (s : k ⟶ j),
          restrict D t a b r fi = restrict D t a b s fj) ∧
    (QuasiCompact a → QuasiSeparated a → LocallyOfFinitePresentation a →
      QuasiCompact b → QuasiSeparated b → LocallyOfFinitePresentation b →
      ∀ (e : pullback p a ≅ pullback p b)
        (he : e.hom ≫ pullback.fst p b = pullback.fst p a),
        ∃ (i : I) (ei : (EtaleEquivalenceRelation.Action.TargetLimit.diagram D t a).obj i ≅
            (EtaleEquivalenceRelation.Action.TargetLimit.diagram D t b).obj i)
          (hei : ei.hom ≫ pullback.fst (t.app i) b = pullback.fst (t.app i) a),
          toLimit D t a b c p hp i ⟨ei.hom, hei⟩ = ⟨e.hom, he⟩)

end Langlands.AlgebraicGeometry.SchemeLimitModel
