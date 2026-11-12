import Langlands.GroupScheme.Rational.SimpleRootSubgroupGenerationStatement
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.GroupScheme.Rational.StandardRelativeWeylGenerationReduction
import Langlands.GroupScheme.Rational.RootFactorPairConsequences
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.GroupScheme.Rational.RootSubgroupMultipleInclusion
import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.Representation.Aubert.General.RationalWeylRootAction

/-!
# Simple root subgroups and their opposites generate every root subgroup: proof
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily

/-- A subgroup functor containing the root subgroups of the simple relative roots and of their
negatives contains every relative root subgroup. -/
theorem simpleRootSubgroupGeneration : SimpleRootSubgroupGenerationStatement.{u} := by
  intro k _ G hG S i hi
  have : IsAffineHom G.X.hom := hG.isAffineHom
  intro ν hν F hF
  have : Smooth G.X.hom := hG.smooth
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hT : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  have hfac : RelativeRoot.HasRankOneFactorization i := rootRankOneFactorization k G hG S i hi
  obtain ⟨hWfin, -, Mx, cs, hcs⟩ := relativeWeylCoxeter k G hG S i hi ν hν
  -- conjugation by a normalizing point of `F(k)` transports containment in `F`
  have hconjF : ∀ n : normalizerPoints i, n.val ∈ F.carrier (Over.mk (𝟙 _)) →
      ∀ ch : characterLattice S, RelativeRoot.subgroup i ch ≤ F →
        RelativeRoot.subgroup i (weylAction i n ch) ≤ F := by
    intro n hn ch hch T g hg
    have h1 := RelativeRoot.normalizer_conj_mem i (weylAction i n ch) n⁻¹ hg
    have hback : weylAction i n⁻¹ (weylAction i n ch) = ch := by
      rw [map_inv]
      exact (weylAction i n).symm_apply_apply ch
    rw [hback] at h1
    have h2 := hch T h1
    have hnT : G.constantPoint n.val T ∈ F.carrier T := by
      unfold GroupScheme.constantPoint
      exact F.comp_mem _ hn
    have hc := mul_mem (mul_mem hnT h2) (inv_mem hnT)
    have hcinv : G.constantPoint (n⁻¹).val T = (G.constantPoint n.val T)⁻¹ := by
      rw [Subgroup.coe_inv, G.constantPoint_inv]
    rw [hcinv] at hc
    simpa [mul_assoc] using hc
  -- reflection representatives of the simple reflections lie in `F(k)`
  have hrep : ∀ a : SimpleRoot i ν, ∃ n : normalizerPoints i,
      n.val ∈ F.carrier (Over.mk (𝟙 _)) ∧
        (QuotientGroup.mk n : relativeWeylGroup i) = cs.simple a := by
    intro a
    have ha : a.1 ∈ relativeRoots i := a.2.1.1
    obtain ⟨x, hx, hx1⟩ := RelativeRoot.exists_rootPoint_actual hT i ha
    obtain ⟨⟨p, hp, -⟩, -⟩ := hfac a.1 ha x hx hx1
    refine ⟨⟨p.1 * x * p.2, hp.2.2⟩, ?_, ?_⟩
    · exact mul_mem (mul_mem ((hF a.1 a.2).2 _ hp.1) ((hF a.1 a.2).1 _ hx))
        ((hF a.1 a.2).2 _ hp.2.1)
    · have : Finite (relativeWeylGroup i) := hWfin
      exact hcs.eq_simple_of_isRelativeReflection hT a (hp.isRelativeReflection i hT ha hx hx1)
  choose nS hnSF hnS using hrep
  -- every relative Weyl element has a representative in `F(k)`
  have hW : ∀ w : relativeWeylGroup i, ∃ n : normalizerPoints i,
      n.val ∈ F.carrier (Over.mk (𝟙 _)) ∧ (QuotientGroup.mk n : relativeWeylGroup i) = w := by
    intro w
    induction w using cs.simple_induction_left with
    | one => exact ⟨1, (F.carrier _).one_mem, rfl⟩
    | mul_simple_left w a ih =>
      obtain ⟨n, hn, rfl⟩ := ih
      exact ⟨nS a * n, mul_mem (hnSF a) hn, by rw [QuotientGroup.mk_mul, hnS a]⟩
  -- the root subgroups of `a`, `2a`, `-a`, `-2a` lie in `F` for simple `a`
  have hsimple2 : ∀ a : SimpleRoot i ν, ∀ δ : characterLattice S, (δ = a.1 ∨ δ = 2 • a.1) →
      RelativeRoot.subgroup i δ ≤ F ∧ RelativeRoot.subgroup i (-δ) ≤ F := by
    intro a δ hδ
    rcases hδ with rfl | rfl
    · exact hF a.1 a.2
    · refine ⟨(RelativeRoot.subgroup_nsmul_le i a.1 two_pos).trans (hF a.1 a.2).1, ?_⟩
      rw [← smul_neg]
      exact (RelativeRoot.subgroup_nsmul_le i (-a.1) two_pos).trans (hF a.1 a.2).2
  -- a positive root sent to a non-positive one by a Weyl element is good
  have hclaim : ∀ w : relativeWeylGroup i, ∀ ch ∈ positiveRelativeRoots i ν,
      schemeWeylCharacterAction i w ch ∉ positiveRelativeRoots i ν →
        RelativeRoot.subgroup i ch ≤ F ∧ RelativeRoot.subgroup i (-ch) ≤ F := by
    intro w
    induction w using cs.simple_induction_left with
    | one =>
      intro ch hch hnot
      exact absurd (by simpa using hch) hnot
    | mul_simple_left w a ih =>
      intro ch hch hnot
      by_cases hδ : schemeWeylCharacterAction i w ch ∈ positiveRelativeRoots i ν
      · obtain ⟨n, hn, rfl⟩ := hW w
        rw [schemeWeylCharacterAction_mk] at hδ
        rw [map_mul, LinearEquiv.mul_apply, schemeWeylCharacterAction_mk] at hnot
        have hδa : weylAction i n ch = a.1 ∨ weylAction i n ch = 2 • a.1 := by
          by_contra hne
          push Not at hne
          exact hnot (hcs.2.1 a _ hδ hne.1 hne.2)
        have hgood := hsimple2 a _ hδa
        have hn' : (n⁻¹).val ∈ F.carrier (Over.mk (𝟙 _)) := by
          rw [Subgroup.coe_inv]
          exact inv_mem hn
        have hback : weylAction i n⁻¹ (weylAction i n ch) = ch := by
          rw [map_inv]
          exact (weylAction i n).symm_apply_apply ch
        refine ⟨?_, ?_⟩
        · simpa only [hback] using hconjF n⁻¹ hn' _ hgood.1
        · have := hconjF n⁻¹ hn' _ hgood.2
          rwa [map_neg, hback] at this
      · exact ih ch hch hδ
  intro β hβ
  -- a reflection representative for `β` sends it to `-β`
  obtain ⟨x, hx, hx1⟩ := RelativeRoot.exists_rootPoint_actual hT i hβ
  obtain ⟨⟨p, hp, -⟩, -⟩ := hfac β hβ x hx hx1
  let nβ : normalizerPoints i := ⟨p.1 * x * p.2, hp.2.2⟩
  have hnβ : weylAction i nβ β = -β := hp.weylAction_eq_neg i hT hβ.1 hx hx1
  have hnegβ : -β ∈ relativeRoots i := by
    rw [← hnβ]
    exact weylAction_mapsTo_relativeRoots i nβ hβ
  rcases lt_or_gt_of_ne (hν β hβ) with hlt | hgt
  · -- `β` is negative, so `-β` is positive and sent to `β` by `nβ`
    have hpos : -β ∈ positiveRelativeRoots i ν := ⟨hnegβ, by simpa using hlt⟩
    have hnot : schemeWeylCharacterAction i (QuotientGroup.mk nβ) (-β) ∉
        positiveRelativeRoots i ν := by
      rw [schemeWeylCharacterAction_mk, map_neg, hnβ, neg_neg]
      intro h
      exact absurd h.2 (not_lt.mpr hlt.le)
    simpa using (hclaim _ (-β) hpos hnot).2
  · have hpos : β ∈ positiveRelativeRoots i ν := ⟨hβ, hgt⟩
    have hnot : schemeWeylCharacterAction i (QuotientGroup.mk nβ) β ∉
        positiveRelativeRoots i ν := by
      rw [schemeWeylCharacterAction_mk, hnβ]
      intro h
      have := h.2
      simp only [map_neg, LinearMap.neg_apply, Left.neg_pos_iff] at this
      exact absurd this (not_lt.mpr hgt.le)
    exact (hclaim _ β hpos hnot).1

end Langlands.GroupScheme
