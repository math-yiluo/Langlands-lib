import Langlands.Representation.Exponents.SplitComponentComparison
import Langlands.Representation.Induction.CentralEvaluation
import Langlands.Representation.Aubert.General.InductionCentralCharacter

/-! # Restricting exponents through actual normalized induction -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

universe u v

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

local instance comparisonAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A AG : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ M} {aG : AG.toGrp ⟶ G}

/-- Every central split-component weight of actual normalized induction
restricts from a Levi exponent of the inducing representation. -/
def InducedExponentRestrictionStatement (ha : IsSplitComponent a)
    (haG : IsSplitComponent aG)
    (e : rationalPoints AG.toGrp →* rationalPoints A.toGrp) : Prop :=
  ∀ (W : SmoothRep.{0, u, v} ℂ (pointImage (l ≫ p)))
    (χ : rationalPoints AG.toGrp →* ℂˣ), W.IsAdmissible →
    groupWeightSpace haG ((inductionFunctor p l r hp hr hl hmul).obj W) χ ≠ ⊥ →
    ∃ ψ : rationalPoints A.toGrp →* ℂˣ,
      IsLeviExponent (l ≫ p) ha W ψ ∧ ψ.comp e = χ

set_option maxHeartbeats 800000 in
/-- Renard VII.1.1, lemma (i), with the point homomorphism and its actual
compatibility retained explicitly. -/
theorem inducedExponent_restrict (ha : IsSplitComponent a) (haG : IsSplitComponent aG)
    (e : rationalPoints AG.toGrp →* rationalPoints A.toGrp)
    (he : ∀ t : rationalPoints AG.toGrp,
      ((splitComponentPointsMap (l ≫ p) a (e t) : pointImage (l ≫ p)) :
        rationalPoints G) = rationalPoints.map aG t) :
    InducedExponentRestrictionStatement.{u, v} p l r hp hl hr hmul ha haG e := by
  intro W χ hW hχ
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  let := RationalPointFamily.splitComponentPointTopology ha
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hU := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  let centralMap := splitComponentPointsMap (l ≫ p) a
  let j := (Subgroup.inclusion h.levi_le).comp (centralMap.comp e)
  have hc : ∀ t, (j t : rationalPoints G) ∈ Subgroup.center (rationalPoints G) := by
    intro t
    change (centralMap (e t) : rationalPoints G) ∈ _
    rw [he t]
    exact haG.isCentralSplitTorus.isCentral.map_mem_center t
  have hj : (pointImage p).subtype.comp j = rationalPoints.map aG := by
    apply MonoidHom.ext
    intro t
    exact he t
  have hg := (generalizedWeightSpace_ne_bot_iff (rationalPoints.map aG) χ
    haG.isCentralSplitTorus.isCentral.map_mem_center
    ((inductionFunctor p l r hp hr hl hmul).obj W).isSmooth).mp hχ
  change IsGeneralizedEigencharacter
    ((Induction.smoothInduced (pointImage p) (inducingRepresentation h hU W)).comp
      (rationalPoints.map aG)) χ at hg
  rw [← hj] at hg
  have hw := Induction.smoothInduced_isGeneralizedEigencharacter_reflects
    (pointImage p) (inducingRepresentation h hU W) j
    (fun t g => (Subgroup.mem_center_iff.mp (hc t) g).symm) χ hg
  have hact : (inducingRepresentation h hU W).comp j = W.representation.comp (centralMap.comp e) := by
    apply MonoidHom.ext
    intro t
    apply LinearMap.ext
    intro v
    change ((HaarModulus.closedHalfCharacter (pointImage (r ≫ p)) hU (pointImage p)
      h.le_normalizer (j t) : ℂˣ) : ℂ) •
      W.representation (h.projection (j t)) v = W.representation (centralMap (e t)) v
    rw [closedHalfCharacter_eq_one_of_mem_center _ _ hU h.le_normalizer (j t) (hc t),
      Units.val_one, one_smul]
    exact congrArg (fun m => W.representation m v) (h.projection_levi (centralMap (e t)))
  rw [hact] at hw
  exact exists_generalizedWeight_comp W.representation centralMap
    (splitComponentPointsMap_mem_center (l ≫ p) ha)
    (continuous_splitComponentPointsMap (l ≫ p) ha) hW e χ hw

end Langlands.Aubert.General.RepresentedParabolic
