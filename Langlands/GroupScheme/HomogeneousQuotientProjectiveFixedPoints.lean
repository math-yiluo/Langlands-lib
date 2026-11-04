import Langlands.GroupScheme.ProjectiveTorusFixedPointDimensionStatement
import Langlands.GroupScheme.HomogeneousQuotientProjective
import Langlands.GroupScheme.HomogeneousQuotientRankOneFixedPoints
import Langlands.GroupScheme.HomogeneousQuotientCurveOrbit

/-! # Fixed-point dimension bounds for actual proper homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotient

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}
    (b : B ⟶ G) (q : G.X ⟶ Q)
    (hfib : ∀ (Y : Over (Spec (CommRingCat.of k))) (g h : Y ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier Y)
    [QuasiCompact q.left] [Smooth q.left] [Surjective q.left] [IsProper Q.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- Apply the geometric projective fixed-point statement to the actual
projective embedding of this quotient, rather than requiring a representation,
embedding or lower bound on its fixed points as additional data. -/
def projectiveFixedPointEmbedding
    (hfix : ProjectiveTorusFixedPointDimensionStatement.{u})
    (hb : IsClosedSubgroup b) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (d : ℕ) (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim Q.left) :
    Fin (d + 1) ↪
      {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q //
        ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict i).IsFixed x} :=
  Classical.choice (by
    obtain ⟨hsm, hred, hirr⟩ := smooth_reduced_irreducible_quotient q
    let := hsm
    let := hred
    let := hirr
    let D := projectiveEmbeddingData b q hfib hb
    obtain ⟨x, hx, hfixed⟩ :=
      hfix k T hT D.dimension Q
        ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict i)
        (D.representation.restrict i) D.embedding D.embedding_closed
        (ProjectiveEmbeddingData.restrict_equivariant b q hfib D i) d hd
    exact ⟨{
      toFun := fun j => ⟨x j, hfixed j⟩
      inj' := fun j l h => hx (congrArg Subtype.val h)
    }⟩)

include q hfib in
/-- The actual proper rank-one quotient has dimension at most one, conditional
on the projective linear fixed-point theorem and the explicit subgroup
conjugacy and rational-centralizer hypotheses. -/
theorem dimension_le_one_of_projectiveFixedPointDimension
    (hfix : ProjectiveTorusFixedPointDimensionStatement.{u})
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (hb : IsClosedSubgroup b) (t : T.toGrp ⟶ B) (ht : t ≫ b = i)
    (hconj : MaximalToriAreConjugate B)
    (hc : centralizerPoints i ≤
      (SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    topologicalKrullDim Q.left ≤ 1 := by
  apply dimension_le_one_of_three_fixedPoints hG i hi hT hdep b hb t ht hconj hc q hfib
  intro htwo
  exact ⟨projectiveFixedPointEmbedding b q hfib hfix hb i hT 2 htwo⟩

end Langlands.GroupScheme.HomogeneousQuotient
