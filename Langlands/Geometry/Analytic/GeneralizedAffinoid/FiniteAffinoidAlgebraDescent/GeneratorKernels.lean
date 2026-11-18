import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.GeneratorEvaluation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushoutLiftBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AdmissiblePushoutKernel
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteDomainIdealDescentProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainComparison

/-! # Compatibility and effectiveness of the local generator evaluation kernels -/

noncomputable section

universe u

namespace Langlands.Analytic

namespace BoundedAlgEquiv

variable {K A B : Type*} [NormedField K] [NormedCommRing A] [NormedCommRing B]
  [NormedAlgebra K A] [NormedAlgebra K B]

/-- Bounded equivalences reflect equality of closed ideals through their
actual closed extension maps. -/
theorem closedIdealMap_injective (e : BoundedAlgEquiv K A B)
    {I J : Ideal A} (hI : IsClosed (I : Set A)) (hJ : IsClosed (J : Set A))
    (h : e.toBoundedAlgHom.closedIdealMap I = e.toBoundedAlgHom.closedIdealMap J) : I = J := by
  have hinv (N : Ideal A) (hN : IsClosed (N : Set A)) :
      e.symm.toBoundedAlgHom.closedIdealMap (e.toBoundedAlgHom.closedIdealMap N) = N := by
    rw [BoundedAlgHom.closedIdealMap_comp]
    apply le_antisymm
    · apply (BoundedAlgHom.closedIdealMap_le_iff _ _ _ hN).mpr
      intro a ha
      change e.symm (e a) ∈ N
      simpa only [BoundedAlgEquiv.symm_apply_apply] using ha
    · intro a ha
      simpa only [BoundedAlgHom.comp_apply, BoundedAlgEquiv.toBoundedAlgHom_apply,
        BoundedAlgEquiv.symm_apply_apply] using
          (e.symm.toBoundedAlgHom.comp e.toBoundedAlgHom).mem_closedIdealMap ha
  exact (hinv I hI).symm.trans ((congrArg e.symm.toBoundedAlgHom.closedIdealMap h).trans
    (hinv J hJ))

end BoundedAlgEquiv

namespace PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.GeneratorEvaluation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}
  {c : Domain.FiniteCover (Domain.whole K R)} {F : LocalAlgebras c}
  (t : PairTransitions F) {n : ℕ} (s : Fin n → t.MatchingAlgebra)

/-- The same weighted presentation over any original full subdomain. -/
def restrictedDomain (E : Domain K R) : Domain K (algebra t s) :=
  Domain.pullback (baseMap t s) E

/-- The original domain inclusion induces the actual restriction of
weighted presentations. -/
def sourceRestriction (i : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) :
    BoundedAlgHom K ((cover t s).obj i).algebra (restrictedDomain t s E).algebra :=
  (Domain.pullbackRestriction (baseMap t s) (Domain.inclusionOfSubset E (c.obj i) hi)).restriction

private theorem evaluation_condition (i : Fin c.size) :
    ((t.projection i).comp (globalEvaluation t s)).comp (baseMap t s) =
      (F.map i).comp (c.obj i).baseMap := by
  rw [BoundedAlgHom.comp_assoc, globalEvaluation_baseMap, t.projection_structuralMap]
  exact F.structuralMap_eq i

/-- The entire further restricted evaluation into the actual original local
base change. -/
def restrictedEvaluation (i : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) :
    BoundedAlgHom K (restrictedDomain t s E).algebra (F.baseChange i E hi) :=
  AffinoidPushout.LiftBaseChange.targetMap (baseMap t s) (c.obj i).baseMap E.baseMap
    (restriction hi) (restriction_baseMap hi)
    ((t.projection i).comp (globalEvaluation t s)) (F.map i) (evaluation_condition t s i)

theorem restrictedEvaluation_left (i : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) :
    (restrictedEvaluation t s i E hi).comp (restrictedDomain t s E).baseMap =
      (F.localMap i E hi).comp ((t.projection i).comp (globalEvaluation t s)) :=
  AffinoidPushout.LiftBaseChange.targetMap_left _ _ _ _ _ _ _ _

theorem restrictedEvaluation_right (i : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) :
    (restrictedEvaluation t s i E hi).comp (Domain.pullbackMap (baseMap t s) E) =
      F.baseMap i E hi :=
  AffinoidPushout.LiftBaseChange.targetMap_right _ _ _ _ _ _ _ _

/-- Further base change of the actual local evaluation is boundedly equivalent
to the actual original local algebra base change. -/
def restrictedPushoutEquiv (i : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) :
    BoundedAlgEquiv K
      (AffinoidPushout.algebra (localEvaluation t s i) (sourceRestriction t s i E hi))
      (F.baseChange i E hi) :=
  AffinoidPushout.LiftBaseChange.equiv (baseMap t s) (c.obj i).baseMap E.baseMap
    (restriction hi) (restriction_baseMap hi)
    ((t.projection i).comp (globalEvaluation t s)) (F.map i) (evaluation_condition t s i)

theorem restrictedPushoutEquiv_right (i : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) :
    (restrictedPushoutEquiv t s i E hi).toBoundedAlgHom.comp
      (AffinoidPushout.rightMap (localEvaluation t s i) (sourceRestriction t s i E hi)) =
        restrictedEvaluation t s i E hi :=
  AffinoidPushout.LiftBaseChange.equiv_comp_right _ _ _ _ _ _ _ _

/-- The exact further evaluation kernel is the closed extension of the
original local kernel along the original weighted restriction. -/
theorem kernel_restrictedEvaluation
    (hs : ∀ i, Function.Surjective
      ((F.map i).coefficientMap fun k => t.projection i (s k)))
    (i : Fin c.size) (E : Domain K R) (hi : E.locus ⊆ (c.obj i).locus) :
    RingHom.ker (restrictedEvaluation t s i E hi).toAlgHom.toRingHom =
      (sourceRestriction t s i E hi).closedIdealMap (kernel t s i) := by
  calc
    RingHom.ker (restrictedEvaluation t s i E hi).toAlgHom.toRingHom =
        RingHom.ker (AffinoidPushout.rightMap (localEvaluation t s i)
          (sourceRestriction t s i E hi)).toAlgHom.toRingHom := by
      ext a
      change restrictedEvaluation t s i E hi a = 0 ↔
        AffinoidPushout.rightMap (localEvaluation t s i) (sourceRestriction t s i E hi) a = 0
      have H := congrArg (fun f => f a) (restrictedPushoutEquiv_right t s i E hi)
      constructor
      · intro ha
        apply (restrictedPushoutEquiv t s i E hi).toAlgEquiv.injective
        exact (H.trans ha).trans (map_zero (restrictedPushoutEquiv t s i E hi).toAlgEquiv).symm
      · intro ha
        exact H.symm.trans ((congrArg (restrictedPushoutEquiv t s i E hi) ha).trans
          (map_zero (restrictedPushoutEquiv t s i E hi).toAlgEquiv))
    _ = _ := AffinoidPushout.ker_rightMap (localEvaluation t s i)
      (sourceRestriction t s i E hi) (localEvaluation_isAdmissibleEpi t s hs i)

/-- Whole-map equality of the two original restricted evaluations through the
supplied ordinary intersection transition. -/
theorem restrictedEvaluation_overlap (i j : Fin c.size) :
    (t.equiv i j).toBoundedAlgHom.comp
      (restrictedEvaluation t s i (F.overlap i j) (F.overlapLeft i j)) =
        restrictedEvaluation t s j (F.overlap i j) (F.overlapRight i j) := by
  apply AffinoidPushout.hom_ext (baseMap t s) (F.overlap i j).baseMap
  · apply BoundedAlgHom.ext
    intro a
    calc
      _ = (t.equiv i j) (F.localMap i (F.overlap i j) (F.overlapLeft i j)
          (t.projection i (globalEvaluation t s a))) :=
        congrArg (t.equiv i j) (congrArg (fun f => f a)
          (restrictedEvaluation_left t s i (F.overlap i j) (F.overlapLeft i j)))
      _ = F.localMap j (F.overlap i j) (F.overlapRight i j)
          (t.projection j (globalEvaluation t s a)) :=
        congrArg (fun f => f (globalEvaluation t s a)) (t.projection_overlap i j)
      _ = _ := (congrArg (fun f => f a)
        (restrictedEvaluation_left t s j (F.overlap i j) (F.overlapRight i j))).symm
  · apply BoundedAlgHom.ext
    intro a
    calc
      _ = (t.equiv i j) (F.baseMap i (F.overlap i j) (F.overlapLeft i j) a) :=
        congrArg (t.equiv i j) (congrArg (fun f => f a)
          (restrictedEvaluation_right t s i (F.overlap i j) (F.overlapLeft i j)))
      _ = F.baseMap j (F.overlap i j) (F.overlapRight i j) a :=
        congrArg (fun f => f a) (t.over_base i j)
      _ = _ := (congrArg (fun f => f a)
        (restrictedEvaluation_right t s j (F.overlap i j) (F.overlapRight i j))).symm

/-- On the actual pullback of every original intersection, the closed local
kernels have equal extensions. -/
theorem kernels_overlap
    (hs : ∀ i, Function.Surjective
      ((F.map i).coefficientMap fun k => t.projection i (s k))) (i j : Fin c.size) :
    (sourceRestriction t s i (F.overlap i j) (F.overlapLeft i j)).closedIdealMap (kernel t s i) =
      (sourceRestriction t s j (F.overlap i j) (F.overlapRight i j)).closedIdealMap (kernel t s j) := by
  rw [← kernel_restrictedEvaluation t s hs, ← kernel_restrictedEvaluation t s hs]
  ext a
  change restrictedEvaluation t s i (F.overlap i j) (F.overlapLeft i j) a = 0 ↔
    restrictedEvaluation t s j (F.overlap i j) (F.overlapRight i j) a = 0
  have H := congrArg (fun f => f a) (restrictedEvaluation_overlap t s i j)
  constructor
  · intro ha
    exact H.symm.trans ((congrArg (t.equiv i j) ha).trans
      (map_zero (t.equiv i j).toAlgEquiv))
  · intro ha
    apply (t.equiv i j).toAlgEquiv.injective
    exact (H.trans ha).trans (map_zero (t.equiv i j).toAlgEquiv).symm

/-- The literal intersection of weighted pullback domains and the weighted
pullback of the original literal intersection represent the same locus. -/
def overlapDomainEquiv (i j : Fin c.size) : BoundedAlgEquiv K
    (((cover t s).obj i).inter ((cover t s).obj j)).algebra
    (restrictedDomain t s (F.overlap i j)).algebra :=
  Domain.boundedEquivOfLocusEq _ _ (by ext x; rfl)

private theorem overlapDomainEquiv_over_base (i j : Fin c.size) :
    (overlapDomainEquiv t s i j).toBoundedAlgHom.comp
      (((cover t s).obj i).inter ((cover t s).obj j)).baseMap =
        (restrictedDomain t s (F.overlap i j)).baseMap :=
  Domain.boundedEquivOfLocusEq_comp_baseMap _ _ _

theorem overlapDomainEquiv_left (i j : Fin c.size) :
    (overlapDomainEquiv t s i j).toBoundedAlgHom.comp
      (((cover t s).obj i).interLeft ((cover t s).obj j)).restriction =
        sourceRestriction t s i (F.overlap i j) (F.overlapLeft i j) := by
  apply Domain.boundedHom_eq_of_over_base ((cover t s).obj i)
    (restrictedDomain t s (F.overlap i j))
  · calc
      _ = (overlapDomainEquiv t s i j).toBoundedAlgHom.comp
          ((((cover t s).obj i).interLeft ((cover t s).obj j)).restriction.comp
            ((cover t s).obj i).baseMap) := rfl
      _ = _ := congrArg (fun f => (overlapDomainEquiv t s i j).toBoundedAlgHom.comp f)
        (((cover t s).obj i).interLeft ((cover t s).obj j)).comp_baseMap
      _ = _ := overlapDomainEquiv_over_base t s i j
  · exact (Domain.pullbackRestriction (baseMap t s)
      (Domain.inclusionOfSubset (F.overlap i j) (c.obj i) (F.overlapLeft i j))).comp_baseMap

theorem overlapDomainEquiv_right (i j : Fin c.size) :
    (overlapDomainEquiv t s i j).toBoundedAlgHom.comp
      (((cover t s).obj i).interRight ((cover t s).obj j)).restriction =
        sourceRestriction t s j (F.overlap i j) (F.overlapRight i j) := by
  apply Domain.boundedHom_eq_of_over_base ((cover t s).obj j)
    (restrictedDomain t s (F.overlap i j))
  · calc
      _ = (overlapDomainEquiv t s i j).toBoundedAlgHom.comp
          ((((cover t s).obj i).interRight ((cover t s).obj j)).restriction.comp
            ((cover t s).obj j).baseMap) := rfl
      _ = _ := congrArg (fun f => (overlapDomainEquiv t s i j).toBoundedAlgHom.comp f)
        (((cover t s).obj i).interRight ((cover t s).obj j)).comp_baseMap
      _ = _ := overlapDomainEquiv_over_base t s i j
  · exact (Domain.pullbackRestriction (baseMap t s)
      (Domain.inclusionOfSubset (F.overlap i j) (c.obj j) (F.overlapRight i j))).comp_baseMap

/-- The actual closed local kernel ideals satisfy the published literal
intersection compatibility condition on the original weighted pullback cover. -/
theorem kernelCompatible
    (hs : ∀ i, Function.Surjective
      ((F.map i).coefficientMap fun k => t.projection i (s k))) :
    (cover t s).IdealCompatible (kernel t s) := by
  intro i j
  apply (overlapDomainEquiv t s i j).closedIdealMap_injective
    ((((cover t s).obj i).interLeft ((cover t s).obj j)).restriction.isClosed_closedIdealMap
      (kernel t s i))
    ((((cover t s).obj i).interRight ((cover t s).obj j)).restriction.isClosed_closedIdealMap
      (kernel t s j))
  calc
    _ = ((overlapDomainEquiv t s i j).toBoundedAlgHom.comp
        (((cover t s).obj i).interLeft ((cover t s).obj j)).restriction).closedIdealMap
          (kernel t s i) := BoundedAlgHom.closedIdealMap_comp _ _ _
    _ = (sourceRestriction t s i (F.overlap i j) (F.overlapLeft i j)).closedIdealMap
        (kernel t s i) := congrArg (fun f => f.closedIdealMap (kernel t s i))
      (overlapDomainEquiv_left t s i j)
    _ = (sourceRestriction t s j (F.overlap i j) (F.overlapRight i j)).closedIdealMap
        (kernel t s j) := kernels_overlap t s hs i j
    _ = ((overlapDomainEquiv t s i j).toBoundedAlgHom.comp
        (((cover t s).obj i).interRight ((cover t s).obj j)).restriction).closedIdealMap
          (kernel t s j) := congrArg (fun f => f.closedIdealMap (kernel t s j))
      (overlapDomainEquiv_right t s i j).symm
    _ = _ := (BoundedAlgHom.closedIdealMap_comp _ _ _).symm

/-- The actual global contraction of the local evaluation kernels. -/
def globalKernel : Ideal (algebra t s) := (cover t s).idealContraction (kernel t s)

theorem isClosed_globalKernel : IsClosed (globalKernel t s : Set (algebra t s)) :=
  (cover t s).isClosed_idealContraction (kernel t s)
    (fun i => isClosed_eq (localEvaluation t s i).continuous continuous_const)

/-- This contraction is exactly the entire bounded matching-valued evaluation
kernel; equality is tested on the original matching projections. -/
theorem globalKernel_eq : globalKernel t s = RingHom.ker (globalEvaluation t s).toAlgHom.toRingHom := by
  ext a
  refine ((cover t s).mem_idealContraction (kernel t s) a).trans ?_
  change (∀ i, localEvaluation t s i (((cover t s).map i).restriction a) = 0) ↔
    globalEvaluation t s a = 0
  constructor
  · intro ha
    apply t.matching_ext
    intro i
    exact ((congrArg (fun f => f a) (localEvaluation_left t s i)).symm.trans (ha i)).trans
      (map_zero (t.projection i).toAlgHom).symm
  · intro ha i
    exact (congrArg (fun f => f a) (localEvaluation_left t s i)).trans
      ((congrArg (t.projection i) ha).trans (map_zero (t.projection i).toAlgHom))

/-- Closed-ideal effectiveness identifies each original local kernel with
the closed extension of this exact global evaluation kernel. -/
theorem globalKernel_local
    (hs : ∀ i, Function.Surjective
      ((F.map i).coefficientMap fun k => t.projection i (s k))) (i : Fin c.size) :
    ((cover t s).map i).restriction.closedIdealMap (globalKernel t s) = kernel t s i :=
  Domain.FiniteCover.idealEffectiveness K (algebra t s) (Domain.whole K (algebra t s))
    (cover t s) (kernel t s)
    (fun i => isClosed_eq (localEvaluation t s i).continuous continuous_const)
    (kernelCompatible t s hs) i

end PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.GeneratorEvaluation
end Langlands.Analytic
