import Langlands.GroupScheme.Rational.QuasiSplitInnerForm
import Langlands.GroupScheme.IsomorphismSchemeBaseChange
import Langlands.GroupScheme.AutomorphicAction.BaseChange
import Langlands.GroupScheme.CocycleBaseChangeTriviality
import Langlands.GroupScheme.LocalGroupIsoRefinement
import Langlands.GroupScheme.Absolute.GeometricBorelBaseChange
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # Quasi-split inner forms after a change of base field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace LocalGroupIso

variable {S S' : Scheme.{u}} {G H A : GroupScheme S} {U : Over S}

/-- A discrepancy cocycle of a local isomorphism family remains a discrepancy cocycle after
change of base, for the base-changed family and action. -/
theorem HasDiscrepancy.baseChange {e : LocalGroupIso G H U} {a : AutomorphicAction A G}
    {ξ : Cocycle A U} (h : e.HasDiscrepancy a ξ) (b : S' ⟶ S) (V : Over S')
    (r : (Over.map b).obj V ⟶ U) :
    ((e.refine r).baseChangeFamily b).HasDiscrepancy (a.baseChange b) (ξ.baseChange b V r) := by
  intro Z x y g
  apply (baseChangePointsEquiv b H Z).injective
  rw [baseChangeFamily_toFun, baseChangeFamily_toFun, AutomorphicAction.baseChangePointsEquiv_act,
    Cocycle.baseChange_toFun]
  exact h _ _ _

end LocalGroupIso

section QuasiSplit

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Quasi-splitness persists along an algebraic extension of fields. -/
theorem IsQuasiSplit.baseChange_of_algebraicExtension (hG : IsQuasiSplit G) :
    IsQuasiSplit ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) := by
  obtain ⟨B, i, hi⟩ := hG.exists_isGeometricBorelSubgroup
  exact ⟨hG.isConnectedReductive.baseChange_of_algebraicExtension, _, _,
    hi.baseChange hG.isConnectedReductive (algebraBaseMap k K)⟩

end QuasiSplit

namespace QuasiSplitInnerForm

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  (qf : QuasiSplitInnerForm G)

/-- If the discrepancy cocycle of a quasi-split inner form becomes trivial on the pulled-back
cover after extending the base field to `E`, the local isomorphisms descend to an isomorphism
over `E` of the base-changed model and group. -/
def baseChangeIsoOfTrivial (E : Type u) [Field E] [Algebra k E]
    (h : (qf.cocycle.baseChangePullback (algebraBaseMap k E)).IsTrivial) :
    (GroupScheme.baseChange (algebraBaseMap k E)).obj qf.model ≅
      (GroupScheme.baseChange (algebraBaseMap k E)).obj G := by
  let b := algebraBaseMap k E
  let U : Over (Spec (CommRingCat.of k)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k qf.carrier)))
  obtain ⟨hs, hfl, hqc⟩ := fieldExtension_fpqc k qf.carrier
  have : Surjective U.hom := hs
  have : Flat U.hom := hfl
  have : QuasiCompact U.hom := hqc
  let U' := (Over.pullback b).obj U
  have : Surjective U'.hom := by change Surjective (pullback.snd U.hom b); infer_instance
  have : Flat U'.hom := by change Flat (pullback.snd U.hom b); infer_instance
  have : QuasiCompact U'.hom := by change QuasiCompact (pullback.snd U.hom b); infer_instance
  exact ((qf.localIso.refine ((Over.mapPullbackAdj b).counit.app U)).baseChangeFamily b).descendOfTrivial
    (qf.isAdjointQuotient.innerAction.baseChange b) (qf.cocycle.baseChangePullback b)
    (LocalGroupIso.HasDiscrepancy.baseChange qf.hasDiscrepancy b U' _) h

/-- If the discrepancy cocycle becomes trivial on the pulled-back cover over an algebraic
extension `E`, the group is quasi-split over `E`. -/
theorem isQuasiSplit_baseChange_of_trivial (E : Type u) [Field E] [Algebra k E]
    [Algebra.IsAlgebraic k E]
    (h : (qf.cocycle.baseChangePullback (algebraBaseMap k E)).IsTrivial) :
    IsQuasiSplit ((GroupScheme.baseChange (algebraBaseMap k E)).obj G) :=
  (qf.isQuasiSplit.baseChange_of_algebraicExtension (K := E)).of_iso
    (qf.baseChangeIsoOfTrivial E h).symm

end QuasiSplitInnerForm

end Langlands.GroupScheme
