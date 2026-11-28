import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Rational.NumberFieldQuadraticOppositeBorelTorus
import Langlands.GroupScheme.Reductive.SimplyConnectedWeilPresentation
import Langlands.GroupScheme.SimplyConnected.TypeD4CubicLeafField

/-! # The central and leaf factors of a trialitarian opposite-Borel torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The central simple root and the three leaves give coefficient groups for
the two torus projections. The leaf group is a Weil restriction from the field
of one leaf and its torus acts by conjugation on the central group. -/
def TrialitarianOppositeBorelFactorsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b)) →
    (∀ a : d.Vertex, e a ≠ 1 →
      ∃ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a ≠ a) →
    ∀ (Q : IntermediateField F (SeparableClosure F)) [FiniteDimensional F Q] [IsGalois F Q],
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (t : T.toGrp ⟶ G),
        IsQuadraticOppositeBorelTorus (Q := Q) t →
        ∃ (a : d.Vertex) (_ : NumberField (d.starVertexField a))
          (_ : FiniteDimensional F (d.starVertexField a))
          (A : GroupScheme (Spec (CommRingCat.of (d.starVertexField a : Type u))))
          (_ : IsAffine A.X.left) (_ : IsAffineHom A.X.hom) (_ : LocallyOfFiniteType A.X.hom)
          (dA : TitsIndexData A) (H : GroupScheme (Spec (CommRingCat.of F)))
          (_ : IsAffineHom H.X.hom) (_ : LocallyOfFiniteType H.X.hom) (dH : TitsIndexData H)
          (T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of F)))
          (p₁ : T.toGrp ⟶ T₁.toGrp) (p₂ : T.toGrp ⟶ T₂.toGrp)
          (i : T₁.toGrp ⟶ H) (j : H ⟶ G)
          (r : T₂.toGrp ⟶ AffineWeil.groupScheme F (d.starVertexField a) A)
          (s : AffineWeil.groupScheme F (d.starVertexField a) A ⟶ G)
          (act : AutomorphicAction T₂.toGrp H),
          e a ≠ 1 ∧ IsSimplyConnected A ∧ IsAbsolutelyAlmostSimple A ∧
          Nonempty (dA.Vertex ≃ Fin 1) ∧ IsSimplyConnected H ∧ IsAbsolutelyAlmostSimple H ∧
          Nonempty (dH.Vertex ≃ Fin 1) ∧
          IsSimplyConnected (AffineWeil.groupScheme F (d.starVertexField a) A) ∧
          (∀ (Z : Over (Spec (CommRingCat.of F))) (x : Z ⟶ T₂.toGrp.X) (y : Z ⟶ H.X),
            act.act x y ≫ j.hom.hom =
              (x ≫ (r ≫ s).hom.hom) * (y ≫ j.hom.hom) * (x ≫ (r ≫ s).hom.hom)⁻¹) ∧
          (∀ (Z : Over (Spec (CommRingCat.of F))) (x : Z ⟶ T₂.toGrp.X) (z : Z ⟶ T₁.toGrp.X),
            act.act x (z ≫ i.hom.hom) = z ≫ i.hom.hom) ∧
          ∀ (Z : Over (Spec (CommRingCat.of F))) (z : Z ⟶ T.toGrp.X),
            z ≫ t.hom.hom = ((z ≫ p₁.hom.hom ≫ i.hom.hom) ≫ j.hom.hom) *
              ((z ≫ p₂.hom.hom) ≫ (r ≫ s).hom.hom)

end Langlands.GroupScheme
