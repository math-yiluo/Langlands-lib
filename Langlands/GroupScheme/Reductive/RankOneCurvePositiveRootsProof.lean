import Langlands.GroupScheme.Reductive.RankOneCurvePositiveRoots
import Langlands.GroupScheme.Dynamic.HomogeneousCurveUnipotentProof

/-! # Signed quotient-curve bounds from pseudo-reductivity -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace HomogeneousQuotient

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}
    (b : B ⟶ G) (q : G.X ⟶ Q)
    (hfib : ∀ (Y : Over (Spec (CommRingCat.of k))) (g h : Y ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier Y)
    [QuasiCompact q.left] [Smooth q.left] [Surjective q.left] [IsSeparated Q.hom]

/-- Select an actual noncontained signed dynamic direction and its small
unipotent representative using pseudo-reductivity and a prescribed quotient
curve of a proper solvable closed subgroup. -/
def signedCurveUnipotentDataOfPseudoReductive
    (hG : IsPseudoReductive G) (hb : IsClosedSubgroup b)
    (hB : IsSolvableGroupScheme B) (hproper : ¬ IsIso b)
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ B) (ν : cocharacterLattice T)
    (hdimQ : topologicalKrullDim Q.left ≤ 1)
    (hz : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t ≫ b) ≤
      SubgroupFunctor.range b) :
    SignedCurveUnipotentData (t ≫ b) ν b q
      (Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib) := by
  letI : Smooth G.X.hom := hG.smooth
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  letI : ConnectedSpace G.X.left := hG.connectedSpace
  letI : IsClosedImmersion b.hom.hom.left := hb
  letI : Mono b.hom.hom := Over.mono_of_mono_left _
  letI : Smooth B.X.hom := smooth_subgroup_of_smooth_quotient G B b q hfib
  letI : IsAffineHom B.X.hom := affine_subgroup_of_closed G B b hb
  let D := Dynamic.noncontainedSignedDirection hT (t ≫ b) ν b hb hproper hz
  exact ⟨D, curveUnipotentDataOfPseudoReductive b q hfib hG hb hB hT t
    D.cocharacter hdimQ D.noncontained⟩

include q hfib in
/-- A prescribed homogeneous quotient curve of a proper solvable closed
subgroup gives uniqueness of positive roots for the original cocharacter.
The symmetrized-centralizer containment and nonidentity normalizer class
remain explicit inputs. -/
theorem positive_roots_eq_of_rankOne_curve_quotient_of_isConnectedReductive
    (hG : IsConnectedReductive G) (hb : IsClosedSubgroup b)
    (hB : IsSolvableGroupScheme B) (hproper : ¬ IsIso b)
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ B)
    (hi : IsMaximalTorus (t ≫ b))
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots (t ≫ b), ∀ β ∈ roots (t ≫ b),
        ¬ LinearIndependent ℤ ![α, β])
    (n : normalizerPoints (t ≫ b))
    (hn : (QuotientGroup.mk n : relativeWeylGroup (t ≫ b)) ≠ 1)
    (ν : cocharacterLattice T)
    (hdimQ : topologicalKrullDim Q.left ≤ 1)
    (hz : Dynamic.centralizer (CommGroupScheme.groupHom
        (normalizerSymmetrizedCocharacter (t ≫ b) n ν) ≫ t ≫ b) ≤
      SubgroupFunctor.range b) :
    haveI := hG.isAffineHom
    ∀ {α β : characterLattice T}, α ∈ roots (t ≫ b) → β ∈ roots (t ≫ b) →
      0 < latticePairing T α ν → 0 < latticePairing T β ν → α = β := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  let D := signedCurveUnipotentDataOfPseudoReductive b q hfib hG.isPseudoReductive
    hb hB hproper hT t (normalizerSymmetrizedCocharacter (t ≫ b) n ν) hdimQ hz
  intro α β
  exact hG.positive_roots_eq_of_signed_normalizerSymmetrized_unipotent_finrank_le_one
    (t ≫ b) hi hT hdep n hn ν D.finrank_tangent_le_one_or_neg

end HomogeneousQuotient

end Langlands.GroupScheme
