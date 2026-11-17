import Langlands.GroupScheme.AutomorphicAction.LocallyInnerTransport
import Langlands.GroupScheme.LocalGroupIsoBaseChangeEquivalence
import Langlands.GroupScheme.Rational.InnerDiscrepancyRefinement
import Langlands.GroupScheme.Rational.FiniteGaloisBaseChangeDiscrepancy

/-! # Inner equivalence of Galois pullbacks from all-test inner discrepancy -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IsAdjointQuotient

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G H A : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ A}
  (hq : IsAdjointQuotient q)

/-- An all-test inner discrepancy supplies an actual adjoint section comparing the
isomorphism with its pullback by any endomorphism of the field cover. -/
theorem exists_basePointIso_trans_eq_pullIso_of_innerDiscrepancy
    (E : (baseChange (algebraBaseMap k K)).obj G ≅
      (baseChange (algebraBaseMap k K)).obj H)
    (he : (LocalGroupIso.ofBaseChangeIso (U := ringTest k K) E).HasInnerDiscrepancy hq.innerAction)
    (r : ringTest k K ⟶ ringTest k K) :
    ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
        ((baseChange (algebraBaseMap k K)).obj A).X,
      (adjointQuotientBaseChangeStatement.isAdjointQuotient (K := K) hq).innerAction.basePointIso x
          ≪≫ E = Descent.pullIso r.left (Over.w r) (Over.w r) E := by
  obtain ⟨x, hx⟩ := he (𝟙 (ringTest k K)) r
  let xK := (LocalGroupIso.coverPointsEquiv A (𝟙 (ringTest k K))).symm x
  have hlocal : LocalGroupIso.ofBaseChangeIso (U := ringTest k K)
        ((adjointQuotientBaseChangeStatement.isAdjointQuotient (K := K)
          hq).innerAction.basePointIso xK ≪≫ E) =
      LocalGroupIso.ofBaseChangeIso (U := ringTest k K) (Descent.pullIso r.left (Over.w r) (Over.w r) E) := by
    apply LocalGroupIso.ext_toFun
    intro T a g
    rw [hq.ofBaseChangeIso_basePointIso_trans,
      ← LocalGroupIso.ofBaseChangeIso_comp_cover]
    have hxx : LocalGroupIso.coverBasePoint A xK = x := by
      exact (LocalGroupIso.coverPointsEquiv A (𝟙 (ringTest k K))).apply_symm_apply x
    rw [hxx]
    simpa only [Category.comp_id] using hx a g
  refine ⟨xK, ?_⟩
  have h := congrArg LocalGroupIso.toBaseChangeIso hlocal
  simpa only [LocalGroupIso.toBaseChangeIso_ofBaseChangeIso] using h

/-- The actual isomorphism of an inner local family is inner-equivalent to every
pullback along an endomorphism of its field cover. -/
theorem innerEquivalent_pullIso_of_innerDiscrepancy
    (E : (baseChange (algebraBaseMap k K)).obj G ≅
      (baseChange (algebraBaseMap k K)).obj H)
    (he : (LocalGroupIso.ofBaseChangeIso (U := ringTest k K) E).HasInnerDiscrepancy hq.innerAction)
    (r : ringTest k K ⟶ ringTest k K) :
    IsFppfInnerEquivalent E (Descent.pullIso r.left (Over.w r) (Over.w r) E) := by
  obtain ⟨x, hx⟩ := hq.exists_basePointIso_trans_eq_pullIso_of_innerDiscrepancy E he r
  have hqK := adjointQuotientBaseChangeStatement.isAdjointQuotient (K := K) hq
  have hrestrict : hqK.innerAction.restrict ((baseChange (algebraBaseMap k K)).map q) =
      AutomorphicAction.conjugation (𝟙 _) := by
    let := hqK.flat
    let := hqK.surjective
    let := hqK.isConnectedReductive.isAffineHom
    let := hqK.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
    let : IsAffine ((baseChange (algebraBaseMap k K)).obj G).X.left :=
      isAffine_of_isAffineHom ((baseChange (algebraBaseMap k K)).obj G).X.hom
    let : IsAffine ((baseChange (algebraBaseMap k K)).obj A).X.left :=
      isAffine_of_isAffineHom ((baseChange (algebraBaseMap k K)).obj A).X.hom
    exact AutomorphicAction.quotientAction_restrict _ _ _
  have hi := IsFppfLocallyInner.of_adjointPoint _
    ⟨hqK.flat, hqK.surjective, hqK.locallyOfFinitePresentation, hqK.kernel_range_eq_center⟩
    hqK.innerAction hrestrict x rfl
  have hh : IsFppfInnerEquivalent (Descent.pullIso r.left (Over.w r) (Over.w r) E) E := by
    rw [← hx]
    simpa only [IsFppfInnerEquivalent, Iso.trans_assoc, Iso.self_symm_id,
      Iso.trans_refl] using hi
  exact hh.symm

/-- Inner equivalence with every endomorphism pullback of a field-cover comparison. -/
def InnerPullComparisonStatement : Prop :=
  ∀ (E : (baseChange (algebraBaseMap k K)).obj G ≅
      (baseChange (algebraBaseMap k K)).obj H)
    (_he : (LocalGroupIso.ofBaseChangeIso (U := ringTest k K) E).HasInnerDiscrepancy hq.innerAction)
    (r : ringTest k K ⟶ ringTest k K),
    IsFppfInnerEquivalent E (Descent.pullIso r.left (Over.w r) (Over.w r) E)

/-- All-test discrepancy proves the field-cover inner comparison statement. -/
theorem innerPullComparison : hq.InnerPullComparisonStatement (K := K) (H := H) :=
  fun E he r => hq.innerEquivalent_pullIso_of_innerDiscrepancy E he r

end IsAdjointQuotient

namespace IsFppfInnerEquivalent

variable {B S T : Scheme.{u}} {G H : GroupScheme B}

/-- Pulling two inner-equivalent comparisons through the same canonical descent
comparisons preserves their inner equivalence. -/
theorem pullIso {b : S ⟶ B} {c : T ⟶ B} (a : T ⟶ S) (ha : a ≫ b = c)
    {E F : (GroupScheme.baseChange b).obj G ≅ (GroupScheme.baseChange b).obj H}
    (h : IsFppfInnerEquivalent E F) :
    IsFppfInnerEquivalent (Descent.pullIso a ha ha E) (Descent.pullIso a ha ha F) := by
  exact ((h.baseChange a).precomp
    (Descent.pullbackComparison b a c ha G).symm).postcomp
      (Descent.pullbackComparison b a c ha H)

end IsFppfInnerEquivalent

/-- A rational inner automorphism is fppf-locally inner, witnessed by the identity cover. -/
theorem isFppfLocallyInner_innerIso {S : Scheme.{u}} (G : GroupScheme S)
    (x : Over.mk (𝟙 S) ⟶ G.X) : IsFppfLocallyInner (G.innerIso x) := by
  refine ⟨Over.mk (𝟙 S), ?_, ?_, ?_, x, ?_⟩
  · change Flat (𝟙 S)
    infer_instance
  · change Surjective (𝟙 S)
    infer_instance
  · change LocallyOfFinitePresentation (𝟙 S)
    infer_instance
  · intro W t g
    have ht : t = Over.homMk W.hom (by simp) := by
      apply Over.OverMorphism.ext
      simpa using t.w
    rw [ht]
    simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id,
      comp_innerIso_hom, constantPoint]

end Langlands.GroupScheme
