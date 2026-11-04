import Langlands.GroupScheme.Reductive.RankOneCurvePositiveRoots
import Langlands.GroupScheme.Rational.RankOneRegularSymmetrization
import Langlands.GroupScheme.HomogeneousQuotientRankOneFixedPoints

/-! # Positive roots from a quotient curve and whole-torus centralizer containment -/

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
    [QuasiCompact q.left] [Smooth q.left] [Surjective q.left] [IsSeparated Q.hom]

variable (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
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
    (hc : torusCentralizer (t ≫ b) ≤ SubgroupFunctor.range b)

/-- Select actual signed unipotent curve data after regular refinement and
normalizer symmetrization. Whole-torus centralizer containment supplies the
required dynamic-centralizer containment on every relative test. -/
def regularSignedCurveUnipotentData
    (hdimQ : topologicalKrullDim Q.left ≤ 1) :
    haveI := hG.isAffineHom
    haveI := hG.smooth
    SignedCurveUnipotentData (t ≫ b)
      (regularNormalizerSymmetrizedCocharacter hT (t ≫ b) n ν) b q
      (Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib) := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  apply signedCurveUnipotentData b q hfib htorus hG.isPseudoReductive hb hB hproper
    hT t (regularNormalizerSymmetrizedCocharacter hT (t ≫ b) n ν) hdimQ
  rw [hG.centralizer_regularNormalizerSymmetrizedCocharacter
    (t ≫ b) hi hT hdep n hn ν]
  exact hc

include htorus hb hB hproper hT hi hdep n hn hc

include q hfib in
/-- A prescribed quotient curve and whole-torus centralizer containment imply
uniqueness for roots positive on the original, possibly nonregular cocharacter. -/
theorem positive_roots_eq_of_rankOne_curve_torusCentralizer
    (hdimQ : topologicalKrullDim Q.left ≤ 1) :
    haveI := hG.isAffineHom
    ∀ {α β : characterLattice T}, α ∈ roots (t ≫ b) → β ∈ roots (t ≫ b) →
      0 < latticePairing T α ν → 0 < latticePairing T β ν → α = β := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have hz : Dynamic.centralizer (CommGroupScheme.groupHom
      (normalizerSymmetrizedCocharacter (t ≫ b) n
        (regularRefinement hT (t ≫ b) ν)) ≫ t ≫ b) ≤
      SubgroupFunctor.range b := by
    change Dynamic.centralizer (CommGroupScheme.groupHom
      (regularNormalizerSymmetrizedCocharacter hT (t ≫ b) n ν) ≫ (t ≫ b)) ≤ _
    rw [hG.centralizer_regularNormalizerSymmetrizedCocharacter
      (t ≫ b) hi hT hdep n hn ν]
    exact hc
  intro α β hα hβ hαν hβν
  exact positive_roots_eq_of_rankOne_curve_quotient b q hfib htorus hG hb hB hproper
    hT t hi hdep n hn (regularRefinement hT (t ≫ b) ν) hdimQ hz hα hβ
      (regularRefinement_pos hT (t ≫ b) ν hα hαν)
      (regularRefinement_pos hT (t ≫ b) ν hβ hβν)

include q hfib in
/-- For a prescribed quotient, the rank-one fixed-point sign embedding turns
the explicit three-fixed-point implication into the curve bound needed above. -/
theorem positive_roots_eq_of_rankOne_quotient_three_fixedPoints
    (hconj : MaximalToriAreConjugate B)
    (hthree : (2 : WithBot ℕ∞) ≤ topologicalKrullDim Q.left →
      Nonempty (Fin 3 ↪
        {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q //
          ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict
            (t ≫ b)).IsFixed x})) :
    haveI := hG.isAffineHom
    ∀ {α β : characterLattice T}, α ∈ roots (t ≫ b) → β ∈ roots (t ≫ b) →
      0 < latticePairing T α ν → 0 < latticePairing T β ν → α = β := by
  have hcp : centralizerPoints (t ≫ b) ≤
      (SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    simpa only [torusCentralizer_carrier_base] using
      hc (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  have hdimQ := dimension_le_one_of_three_fixedPoints hG (t ≫ b) hi hT hdep
    b hb t rfl hconj hcp q hfib hthree
  intro α β
  exact positive_roots_eq_of_rankOne_curve_torusCentralizer b q hfib
    htorus hG hb hB hproper hT t hi hdep n hn ν hc hdimQ

end Langlands.GroupScheme.HomogeneousQuotient
