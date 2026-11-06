import Langlands.GroupScheme.Rational.RootGeneratedCoxeterKernel
import Langlands.GroupScheme.Rational.RootSpanSimpleConjugacy
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.Group.CoxeterLiftConjugacy

/-! # Coxeter relations for actual opposite-root lifts modulo rank-one centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Aubert.General.RationalPointFamily
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ν : cocharacterLattice T} {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : CoxeterSystem C (relativeWeylGroup i))

/-- Conjugacy between labelled simple reflections identifies their actual
root characters up to sign. -/
def SignedSimpleReflectionLaw : Prop :=
  ∀ (w : relativeWeylGroup i) (a b : SimpleRoot i ν),
    w * cs.simple a * w⁻¹ = cs.simple b →
      schemeWeylCharacterAction i w a.val = b.val ∨
        schemeWeylCharacterAction i w a.val = -b.val

/-- The descended character action of a root-span reflection negates its root. -/
theorem IsRelativeReflection.schemeWeylCharacterAction_apply_self
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T}
    {w : relativeWeylGroup i} (h : IsRelativeReflection i a w) :
    schemeWeylCharacterAction i w a = -a := by
  induction w using Quotient.inductionOn' with
  | h n => exact h.weylAction_apply_self i hT n

/-- The positive label theorem, applied after a simple reflection in the
negative case, gives the signed label theorem. -/
theorem HasRelativeRootSystem.signedSimpleReflectionLaw_of_reflections
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν)
    (hSimple : ∀ a : SimpleRoot i ν, IsRelativeReflection i a.val (cs.simple a)) :
    SignedSimpleReflectionLaw cs := by
  intro w a b heq
  have hrootwa : schemeWeylCharacterAction i w a.val ∈ relativeRoots i := by
    rw [← schemeWeylCharacterAction_image_relativeRoots i w]
    exact Set.mem_image_of_mem _ a.property.1.1
  by_cases hp : 0 < latticePairing T (schemeWeylCharacterAction i w a.val) ν
  · exact Or.inl (hroot.root_eq_of_conj_simple_reflections cs hT hν hSimple
      w a b ⟨hrootwa, hp⟩ heq)
  · have hn : latticePairing T (schemeWeylCharacterAction i w a.val) ν < 0 :=
      lt_of_le_of_ne (le_of_not_gt hp) (hν _ hrootwa)
    have hself := (hSimple a).schemeWeylCharacterAction_apply_self hT
    have hwa : schemeWeylCharacterAction i (w * cs.simple a) a.val =
        -(schemeWeylCharacterAction i w a.val) := by
      simp only [map_mul, LinearEquiv.mul_apply, hself, map_neg]
    have hp' : schemeWeylCharacterAction i (w * cs.simple a) a.val ∈
        positiveRelativeRoots i ν := by
      rw [hwa]
      exact ⟨hroot.neg_mem_relativeRoots i hT hrootwa, by simpa using hn⟩
    have heq' : (w * cs.simple a) * cs.simple a * (w * cs.simple a)⁻¹ =
        cs.simple b := by
      calc
        _ = w * cs.simple a * w⁻¹ := by group
        _ = _ := heq
    have hlabel := hroot.root_eq_of_conj_simple_reflections cs hT hν hSimple
      (w * cs.simple a) a b hp' heq'
    rw [hwa] at hlabel
    exact Or.inr (neg_eq_iff_eq_neg.mp hlabel)

namespace RelativeRoot

/-- Actual opposite-root lifts respect simple-reflection conjugacy after
quotienting by the rank-one centralizer generated subgroup. -/
theorem oppositeRootSimpleLifts_compatibleConjugacy
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν)
    (hSimple : ∀ a : SimpleRoot i ν, IsRelativeReflection i a.val (cs.simple a))
    (m : SimpleRoot i ν → normalizerPoints i)
    (hm : ∀ a, (QuotientGroup.mk (m a) : relativeWeylGroup i) = cs.simple a)
    (hmem : ∀ a, (m a).val ∈ oppositeGeneratedPoints i a.val) :
    Langlands.Group.CoxeterLift.CompatibleSimpleConjugacy cs
      (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)))
      (QuotientGroup.mk' (rankOneCentralizerNormalizerPoints i)) m := by
  intro n a b heq
  have hs := hroot.signedSimpleReflectionLaw_of_reflections cs hT hν hSimple
    (QuotientGroup.mk n) a b heq
  change weylAction i n a.val = b.val ∨ weylAction i n a.val = -b.val at hs
  have hn : (n * m a * n⁻¹).val ∈ oppositeGeneratedPoints i b.val := by
    have hc := conj_mem_oppositeGeneratedPoints i n (hmem a)
    rcases hs with hs | hs
    · simpa only [hs, Subgroup.coe_mul, Subgroup.coe_inv] using hc
    · simpa only [hs, oppositeGeneratedPoints_neg, Subgroup.coe_mul, Subgroup.coe_inv] using hc
  have heq' : (QuotientGroup.mk (n * m a * n⁻¹) : relativeWeylGroup i) =
      QuotientGroup.mk (m b) := by
    change QuotientGroup.mk' _ (n * m a * n⁻¹) = QuotientGroup.mk' _ (m b)
    simpa only [map_mul, map_inv, QuotientGroup.mk'_apply, hm] using heq
  have h := oppositeGenerated_lifts_eq_mod_rankOneCentralizer i
    b.property.1.1 hn (hmem b) heq'
  change QuotientGroup.mk' (rankOneCentralizerNormalizerPoints i) (n * m a * n⁻¹) =
    QuotientGroup.mk' (rankOneCentralizerNormalizerPoints i) (m b) at h
  simpa only [map_mul, map_inv] using h

/-- Every family of actual opposite-root simple lifts satisfies the full
Coxeter relations modulo rank-one centralizer intersections. -/
theorem oppositeRootSimpleLifts_isLiftable
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν)
    (hSimple : ∀ a : SimpleRoot i ν, IsRelativeReflection i a.val (cs.simple a))
    (m : SimpleRoot i ν → normalizerPoints i)
    (hm : ∀ a, (QuotientGroup.mk (m a) : relativeWeylGroup i) = cs.simple a)
    (hmem : ∀ a, (m a).val ∈ oppositeGeneratedPoints i a.val) :
    C.IsLiftable (fun a => (QuotientGroup.mk (m a) :
      normalizerPoints i ⧸ rankOneCentralizerNormalizerPoints i)) := by
  apply Langlands.Group.CoxeterLift.isLiftable_of_conjugacy cs
    (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)))
    (QuotientGroup.mk' (rankOneCentralizerNormalizerPoints i)) m hm
  · intro a
    have hs := oppositeGenerated_lift_sq_mem_rankOneCentralizer i a.property.1.1
      (hmem a) (by rw [hm]; exact cs.simple_sq a)
    rw [← map_mul]
    apply (QuotientGroup.eq_one_iff _).2
    change (m a).val * (m a).val ∈ rankOneCentralizerGeneratedPoints i
    simpa only [pow_two] using hs
  · exact oppositeRootSimpleLifts_compatibleConjugacy cs hroot hT hν hSimple m hm hmem

/-- The actual normalizer kernel inclusion requires no separate hypothesis
on relations for the chosen opposite-root lifts. -/
theorem centralizer_inf_rankOneLiftPoints_le_of_oppositeRootSimpleLifts
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν)
    (hSimple : ∀ a : SimpleRoot i ν, IsRelativeReflection i a.val (cs.simple a))
    (m : SimpleRoot i ν → normalizerPoints i)
    (hm : ∀ a, (QuotientGroup.mk (m a) : relativeWeylGroup i) = cs.simple a)
    (hmem : ∀ a, (m a).val ∈ oppositeGeneratedPoints i a.val) :
    centralizerPoints i ⊓ rankOneLiftPoints i m ≤ rankOneCentralizerGeneratedPoints i :=
  centralizer_inf_rankOneLiftPoints_le i cs m hm
    (oppositeRootSimpleLifts_isLiftable cs hroot hT hν hSimple m hm hmem)

end RelativeRoot

end Langlands.GroupScheme
