import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback

/-! # Actual equivariant line bundles on étale equivalence relations -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

namespace EtaleEquivalenceRelation

/-- Two scheme-valued points are related if they are the projections of a
point of the actual relation scheme. -/
def Related (E : EtaleEquivalenceRelation.{u}) {T : Scheme.{u}}
    (a b : T ⟶ E.U) : Prop := ∃ r : T ⟶ E.R, r ≫ E.t = a ∧ r ≫ E.s = b

end EtaleEquivalenceRelation

namespace Picard

/-- An actual line bundle on a chart, with coherent identifications on every
related pair of scheme-valued points. Naturality is expressed with the
canonical composition comparisons for actual line-bundle pullback. -/
structure EquivariantLineBundle (E : EtaleEquivalenceRelation.{u}) where
  bundle : LineBundle E.U
  transport {T : Scheme.{u}} (a b : T ⟶ E.U) (h : E.Related a b) :
    (LineBundle.pullback a).obj bundle ≅ (LineBundle.pullback b).obj bundle
  transport_self {T : Scheme.{u}} (a : T ⟶ E.U) (h : E.Related a a) :
    transport a a h = Iso.refl _
  transport_trans {T : Scheme.{u}} (a b c : T ⟶ E.U)
      (hab : E.Related a b) (hbc : E.Related b c) (hac : E.Related a c) :
    transport a b hab ≪≫ transport b c hbc = transport a c hac
  transport_precompose {T W : Scheme.{u}} (k : W ⟶ T) (a b : T ⟶ E.U)
      (h : E.Related a b) (h' : E.Related (k ≫ a) (k ≫ b)) :
    transport (k ≫ a) (k ≫ b) h' =
      ((LineBundle.pullbackComp k a).app bundle).symm ≪≫
        (LineBundle.pullback k).mapIso (transport a b h) ≪≫
          (LineBundle.pullbackComp k b).app bundle

end Picard
end Langlands.AlgebraicGeometry
