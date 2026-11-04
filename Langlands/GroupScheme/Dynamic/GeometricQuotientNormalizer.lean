import Langlands.GroupScheme.HomogeneousQuotientProjective
import Langlands.GroupScheme.Dynamic.WeightSeparatedNormalizer
import Langlands.GroupScheme.Dynamic.MovingTestQuotientSection

/-! # Nonidentity normalizers from actual smooth proper quotient geometry -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G P : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- An actual nonfixed rational quotient lift gives a nonidentity normalizer
class using only smooth proper homogeneous quotient geometry. -/
def nonidentityNormalizerOfNonfixedSmoothProperQuotient
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (j : P ⟶ G) (hj : IsClosedSubgroup j)
    (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
    (hconj : MaximalToriAreConjugate P) (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : ¬ ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i).IsFixed
      (g ≫ q)) :
    {w : normalizerPoints i // (QuotientGroup.mk w : relativeWeylGroup i) ≠ 1} := by
  let D := HomogeneousQuotient.projectiveEmbeddingData j q hfib hj
  exact nonidentityNormalizerOfWeightSeparatedProperQuotient i hi j hj f hf hconj q hfib
    D.dimension D.representation D.coordinate D.line_stabilizer g hg

/-- A rational torus element moving one quotient section on any relative test
scheme gives a nonidentity normalizer class, without supplied matrix data. -/
def nonidentityNormalizerOfMovingSmoothProperQuotient
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (j : P ⟶ G) (hj : IsClosedSubgroup j)
    (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
    (hconj : MaximalToriAreConjugate P) (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V)
    (t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X)
    (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X)
    (hmove : (((toUnit V ≫ t) ≫ i.hom.hom) * x) ≫ q ≠ x ≫ q) :
    {w : normalizerPoints i // (QuotientGroup.mk w : relativeWeylGroup i) ≠ 1} := by
  let g := Dynamic.nonfixedQuotientLiftOfMovingTestPoint i j q hfib t V x hmove
  exact nonidentityNormalizerOfNonfixedSmoothProperQuotient i hi j hj f hf hconj q hfib
    g.val g.property

end Langlands.GroupScheme
