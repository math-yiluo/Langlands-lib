import Langlands.Geometry.Analytic.SpecialCoverIntersectionQuotient
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FiniteBanachPresentation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FiniteBanachBounds
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange

/-! # Local admissible evaluation quotients from global matching generators -/

noncomputable section

universe u v w

namespace Langlands.Analytic

namespace BoundedAlgHom

variable {K : Type u} {A : Type v} {B : Type w}
  [NormedField K] [NormedCommRing A] [NormedCommRing B]
  [NormedAlgebra K A] [NormedAlgebra K B]

/-- Every actual finite coefficient map has a positive global norm bound,
proved directly from its bounded coefficient homomorphism. -/
theorem exists_coefficientMap_bound (f : BoundedAlgHom K A B) {n : ℕ} (b : Fin n → B) :
    ∃ D > 0, ∀ c : Fin n → A, ‖f.coefficientMap b c‖ ≤ D * ‖c‖ := by
  obtain ⟨M, hM, hf⟩ := f.bounded
  let S := (∑ i, ‖b i‖) + 1
  have hsum : 0 ≤ ∑ i, ‖b i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hS : 0 < S := by dsimp [S]; linarith
  refine ⟨M * S, mul_pos hM hS, fun c => ?_⟩
  calc
    ‖f.coefficientMap b c‖ ≤ ∑ i, ‖f (c i) * b i‖ := by
      simpa only [BoundedAlgHom.coefficientMap_apply] using
        norm_sum_le Finset.univ (fun i => f (c i) * b i)
    _ ≤ ∑ i, (M * ‖c‖) * ‖b i‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((hf (c i)).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm c i) hM.le))
          (norm_nonneg _))
    _ = (M * ‖c‖) * (∑ i, ‖b i‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ (M * ‖c‖) * S := mul_le_mul_of_nonneg_left
      (by dsimp [S]; linarith) (mul_nonneg hM.le (norm_nonneg c))
    _ = (M * S) * ‖c‖ := by ring

end BoundedAlgHom

namespace PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.GeneratorEvaluation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}
  {c : Domain.FiniteCover (Domain.whole K R)} {F : LocalAlgebras c}
  (t : PairTransitions F) {n : ℕ} (s : Fin n → t.MatchingAlgebra)

/-- The same single weighted polynomial presentation is used on every
original cover member. -/
abbrev algebra : PresentedAffinoidAlgebra K :=
  FiniteBanachPresentation.freeAlgebra (A := R) s

def baseMap : BoundedAlgHom K R (algebra t s) :=
  Adjoin.baseMap K R (FiniteBanachPresentation.radii s) ∅

/-- The entire matching-valued evaluation is constructed before any claim
that it is surjective or admissible. -/
def globalEvaluation : BoundedAlgHom K (algebra t s) t.MatchingAlgebra :=
  FiniteBanachPresentation.evaluation t.structuralMap t.norm_one_matching_le s

theorem globalEvaluation_baseMap :
    (globalEvaluation t s).comp (baseMap t s) = t.structuralMap :=
  BoundedAlgHom.ext (FiniteBanachPresentation.evaluation_baseMap
    t.structuralMap t.norm_one_matching_le s)

/-- Pull back each original base domain to the actual weighted presentation. -/
def cover : Domain.FiniteCover (Domain.whole K (algebra t s)) :=
  c.pullbackWhole (baseMap t s)

/-- The original cover algebra acts through the second actual pushout leg. -/
def coefficientMap (i : Fin c.size) :
    BoundedAlgHom K (c.obj i).algebra ((cover t s).obj i).algebra :=
  AffinoidPushout.rightMap (baseMap t s) (c.obj i).baseMap

private theorem localEvaluation_condition (i : Fin c.size) :
    ((t.projection i).comp (globalEvaluation t s)).comp (baseMap t s) =
      (F.map i).comp (c.obj i).baseMap := by
  rw [BoundedAlgHom.comp_assoc, globalEvaluation_baseMap, t.projection_structuralMap]
  exact F.structuralMap_eq i

/-- Evaluate the actual original base-changed presentation in the original
local finite Banach algebra, preserving both entire bounded legs. -/
def localEvaluation (i : Fin c.size) :
    BoundedAlgHom K ((cover t s).obj i).algebra (F.algebra i) :=
  AffinoidPushout.lift (baseMap t s) (c.obj i).baseMap _
    ((t.projection i).comp (globalEvaluation t s)) (F.map i)
    (localEvaluation_condition t s i)

theorem localEvaluation_left (i : Fin c.size) :
    (localEvaluation t s i).comp ((cover t s).map i).restriction =
      (t.projection i).comp (globalEvaluation t s) :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _

theorem localEvaluation_right (i : Fin c.size) :
    (localEvaluation t s i).comp (coefficientMap t s i) = F.map i :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _

/-- The actual new coordinates in each base-changed weighted presentation. -/
def coordinate (i : Fin c.size) (k : Fin n) : ((cover t s).obj i).algebra :=
  ((cover t s).map i).restriction
    (Adjoin.newCoordinate K R (FiniteBanachPresentation.radii s) ∅ k)

@[simp] theorem localEvaluation_coordinate (i : Fin c.size) (k : Fin n) :
    localEvaluation t s i (coordinate t s i k) = t.projection i (s k) := by
  calc
    _ = t.projection i (globalEvaluation t s
        (Adjoin.newCoordinate K R (FiniteBanachPresentation.radii s) ∅ k)) :=
      congrArg (fun f : BoundedAlgHom K (algebra t s) (F.algebra i) =>
        f (Adjoin.newCoordinate K R (FiniteBanachPresentation.radii s) ∅ k))
          (localEvaluation_left t s i)
    _ = _ := congrArg (t.projection i)
      (FiniteBanachPresentation.evaluation_newCoordinate t.structuralMap
        t.norm_one_matching_le s k)

theorem localEvaluation_coefficientMap (i : Fin c.size) (a : Fin n → (c.obj i).algebra) :
    localEvaluation t s i ((coefficientMap t s i).coefficientMap (coordinate t s i) a) =
      (F.map i).coefficientMap (fun k => t.projection i (s k)) a := by
  change (localEvaluation t s i).toAlgHom
    (∑ k : Fin n, coefficientMap t s i (a k) * coordinate t s i k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul]
  have h := congrArg (fun f : BoundedAlgHom K (c.obj i).algebra (F.algebra i) => f (a k))
    (localEvaluation_right t s i)
  exact congrArg₂ (fun a b : F.algebra i => a * b) h
    (localEvaluation_coordinate t s i k)

/-- Global matching generators yield actual admissible local evaluation maps
with the original supplied Banach norms and original full-domain cover. -/
theorem localEvaluation_isAdmissibleEpi
    (hs : ∀ i, Function.Surjective
      ((F.map i).coefficientMap fun k => t.projection i (s k))) (i : Fin c.size) :
    (localEvaluation t s i).IsAdmissibleEpi := by
  obtain ⟨M, hM, hb⟩ := (F.finite i).exists_coefficient_lifts
    (fun k => t.projection i (s k)) (hs i)
  obtain ⟨D, hD, hbound⟩ := (coefficientMap t s i).exists_coefficientMap_bound
    (coordinate t s i)
  apply (localEvaluation t s i).isAdmissibleEpi_iff_normControlledLifts.mpr
  refine ⟨D * M, mul_pos hD hM, fun y => ?_⟩
  obtain ⟨a, ha, han⟩ := hb y
  refine ⟨(coefficientMap t s i).coefficientMap (coordinate t s i) a,
    (localEvaluation_coefficientMap t s i a).trans ha, ?_⟩
  exact (hbound a).trans ((mul_le_mul_of_nonneg_left han hD.le).trans_eq
    (mul_assoc D M ‖y‖).symm)

/-- The actual local evaluation kernel in the original base-changed
weighted quotient presentation. -/
def kernel (i : Fin c.size) : Ideal ((cover t s).obj i).algebra :=
  RingHom.ker (localEvaluation t s i).toAlgHom.toRingHom

local instance (i : Fin c.size) : IsClosed (kernel t s i : Set ((cover t s).obj i).algebra) :=
  isClosed_eq (localEvaluation t s i).continuous continuous_const

/-- The exact presented local quotient, with its quotient norm. -/
def localQuotient (i : Fin c.size) : PresentedAffinoidAlgebra K :=
  ClosedQuotient.algebra ((cover t s).obj i).algebra (kernel t s i)

/-- The local admissibility estimate supplies both bounds of the canonical
local quotient equivalence. -/
def localQuotientEquiv
    (hs : ∀ i, Function.Surjective
      ((F.map i).coefficientMap fun k => t.projection i (s k))) (i : Fin c.size) :
    BoundedAlgEquiv K (localQuotient t s i) (F.algebra i) :=
  ClosedQuotient.equivOfAdmissibleEpi ((cover t s).obj i).algebra (kernel t s i)
    (localEvaluation t s i) rfl (localEvaluation_isAdmissibleEpi t s hs i)

end PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.GeneratorEvaluation
end Langlands.Analytic
