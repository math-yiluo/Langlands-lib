import Langlands.GroupScheme.Rational.RootFactorPairConsequences
import Langlands.GroupScheme.Rational.RelativeReflectionProperties
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Rational.BruhatPointReduction
import Mathlib.Tactic.Group

/-! # Dynamic translated cells from a prescribed opposite factor pair -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {a : characterLattice T} {x : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- The normalizer of the prescribed opposite pair differs from any
representative of its root reflection by a whole-torus centralizer point. -/
theorem IsOppositeFactorPair.normalizerRatio_mem_centralizerPoints
    (hT : IsSplitTorus T.toGrp) (hroot : HasRelativeRootSystem i)
    (ha : a ∈ relativeRoots i)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1)
    (hp : IsOppositeFactorPair i a x p)
    (n : normalizerPoints i)
    (hn : IsRelativeReflection i a (QuotientGroup.mk n)) :
    (p.1 * x * p.2) * n.val⁻¹ ∈ centralizerPoints i := by
  let n' : normalizerPoints i := ⟨p.1 * x * p.2, hp.2.2⟩
  have heq : (QuotientGroup.mk n' : relativeWeylGroup i) = QuotientGroup.mk n :=
    hroot.eq_of_isRelativeReflection (hp.isRelativeReflection i hT ha hx hx1) hn
  have hz : n' * n⁻¹ ∈ (centralizerPoints i).subgroupOf (normalizerPoints i) := by
    apply (QuotientGroup.eq_one_iff _).1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, heq, mul_inv_cancel]
  exact hz

/-- Actual dynamic opposite-unipotent and parabolic coordinates, preserving
the prescribed opposite pair and the fixed reflection normalizer. -/
def IsOppositeFactorPair.translatedCellFactorPair
    (hT : IsSplitTorus T.toGrp) (hroot : HasRelativeRootSystem i)
    (ha : a ∈ relativeRoots i)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1)
    (hp : IsOppositeFactorPair i a x p)
    (n : normalizerPoints i)
    (hn : IsRelativeReflection i a (QuotientGroup.mk n))
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T a ν) :
    {q : rationalPoints G × rationalPoints G //
      q.1 ∈ (Dynamic.unipotent
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))).carrier
          (Over.mk (𝟙 _)) ∧
      q.2 ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
        (Over.mk (𝟙 _)) ∧
      x * n.val⁻¹ = q.1 * q.2} := by
  refine ⟨(p.1⁻¹, ((p.1 * x * p.2) * n.val⁻¹) *
    (n.val * p.2⁻¹ * n.val⁻¹)), ?_, ?_, ?_⟩
  · have hpos' : 0 < latticePairing T (-a) (-ν) := by simpa using hpos
    have hy := subgroup_le_dynamicUnipotent i (-ν) hpos' _
      (Subgroup.inv_mem _ hp.1)
    rwa [groupHom_neg_comp_eq_oppositeCocharacter i ν] at hy
  · have hz := centralizerPoints_le_dynamicParabolic i (CommGroupScheme.groupHom ν)
      (hp.normalizerRatio_mem_centralizerPoints i hT hroot ha hx hx1 n hn)
    have hw := normalizer_conj_mem i (-a) n (Subgroup.inv_mem _ hp.2.1)
    simp only [GroupScheme.constantPoint_self, map_neg,
      hn.weylAction_apply_self i hT n, neg_neg] at hw
    exact Subgroup.mul_mem _ hz
      (Dynamic.unipotent_le_parabolic (CommGroupScheme.groupHom ν ≫ i) _
        (subgroup_le_dynamicUnipotent i ν hpos _ hw))
  · group

end Langlands.GroupScheme.RelativeRoot
