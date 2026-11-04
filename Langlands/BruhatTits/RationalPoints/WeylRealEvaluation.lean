import Langlands.GroupScheme.Rational.WeylPositiveCocharacter
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Mathlib.Basic.Real.Basic

/-! # Real evaluation of actual cocharacters and their integral Weyl sums -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.BruhatTits.RationalPoints

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (f : rationalPoints G →* Multiplicative ℝ)
    (z : rationalPoints (Gm (Spec (CommRingCat.of k))).toGrp)

/-- Evaluate an integral cocharacter at an actual multiplicative-group point,
then apply the ambient real homomorphism. -/
def cocharacterRealEvaluation : cocharacterLattice T →+ ℝ :=
  (f.comp (rationalPoints.map i)).toAdditiveLeft.comp (evalPoint z)

@[simp] theorem cocharacterRealEvaluation_apply (ν : cocharacterLattice T) :
    cocharacterRealEvaluation i f z ν =
      (f (rationalPoints.map (CommGroupScheme.groupHom ν ≫ i) z)).toAdd := rfl

/-- Actual normalizing points preserve real evaluation, since their action on
cocharacters induces conjugation in the ambient point group. -/
theorem cocharacterRealEvaluation_normalizingAut
    (n : normalizerPoints i) (ν : cocharacterLattice T) :
    cocharacterRealEvaluation i f z (cocharacterAut (normalizingAut i n) ν) =
      cocharacterRealEvaluation i f z ν := by
  simp only [cocharacterRealEvaluation_apply, groupHom_cocharacterAut_comp]
  change (f (rationalPoints.map (G.innerIso (n : rationalPoints G)).hom
    (rationalPoints.map (CommGroupScheme.groupHom ν ≫ i) z))).toAdd = _
  rw [rationalPoints_map_innerIso]
  simp [MulAut.conj_apply, mul_comm]

variable [Mono i.hom.hom.left]

/-- The actual quotient `N(k)/Z(k)` preserves real evaluation. -/
theorem cocharacterRealEvaluation_relativeWeyl
    (w : relativeWeylGroup i) (ν : cocharacterLattice T) :
    cocharacterRealEvaluation i f z (relativeWeylCocharacterAction i w ν) =
      cocharacterRealEvaluation i f z ν := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  exact cocharacterRealEvaluation_normalizingAut i f z n ν

variable [Fintype (relativeWeylGroup i)]

/-- The integral Weyl sum evaluates to the group order times the original
value. There is no division in the cocharacter lattice. -/
theorem cocharacterRealEvaluation_relativeWeylCocharacterSum
    (ν : cocharacterLattice T) :
    cocharacterRealEvaluation i f z (relativeWeylCocharacterSum i ν) =
      (Fintype.card (relativeWeylGroup i) : ℝ) * cocharacterRealEvaluation i f z ν := by
  rw [relativeWeylCocharacterSum_apply, map_sum]
  simp only [cocharacterRealEvaluation_relativeWeyl]
  simp [nsmul_eq_mul]

/-- An integral Weyl sum with zero real evaluation forces the original
cocharacter to have zero real evaluation. -/
theorem cocharacterRealEvaluation_eq_zero_of_weylSum_eval_eq_zero
    (ν : cocharacterLattice T)
    (h : cocharacterRealEvaluation i f z (relativeWeylCocharacterSum i ν) = 0) :
    cocharacterRealEvaluation i f z ν = 0 := by
  rw [cocharacterRealEvaluation_relativeWeylCocharacterSum] at h
  exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- A zero integral Weyl sum forces zero real evaluation. -/
theorem cocharacterRealEvaluation_eq_zero_of_weylSum_eq_zero
    (ν : cocharacterLattice T) (h : relativeWeylCocharacterSum i ν = 0) :
    cocharacterRealEvaluation i f z ν = 0 :=
  cocharacterRealEvaluation_eq_zero_of_weylSum_eval_eq_zero i f z ν (by rw [h, map_zero])

/-- It suffices that the actual point obtained by evaluating the integral
Weyl sum has finite order. -/
theorem cocharacterRealEvaluation_eq_zero_of_weylSum_point_pow_eq_one
    (ν : cocharacterLattice T) {m : ℕ} (hm : 0 < m)
    (h : rationalPoints.map
      (CommGroupScheme.groupHom (relativeWeylCocharacterSum i ν) ≫ i) z ^ m = 1) :
    cocharacterRealEvaluation i f z ν = 0 := by
  apply cocharacterRealEvaluation_eq_zero_of_weylSum_eval_eq_zero i f z ν
  have hf := congrArg (fun x => (f x).toAdd) h
  simp only [map_pow, toAdd_pow, map_one, toAdd_one,
    nsmul_eq_mul] at hf
  exact (mul_eq_zero.mp hf).resolve_left (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))

end Langlands.BruhatTits.RationalPoints
