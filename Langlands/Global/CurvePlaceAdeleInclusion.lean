import Langlands.Global.AdelicTensorBaseChange
import Langlands.Global.ArithmeticSIntegerExtension
import Langlands.Global.CurvePlaceCompletedIntegersExtension

/-! # Inclusion of full actual curve-place adele rings -/

noncomputable section

universe u

open Filter Topology
open scoped RestrictedProduct

namespace Langlands.Global

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional K L]

/-- The original completion map at the actual restriction of an upper place. -/
def curvePlaceCompletionInclusion (q : AlgebraicCurve.Place k L) :
    curvePlaceCompletion (curvePlaceRestriction (K := K) q) →+*
      curvePlaceCompletion q :=
  CurvePlaceCompletionExtension.completionMap (curvePlaceRestriction q) ⟨q, rfl⟩

@[simp]
theorem curvePlaceCompletionInclusion_algebraMap (q : AlgebraicCurve.Place k L) (x : K) :
    curvePlaceCompletionInclusion (K := K) q
        (algebraMap K (curvePlaceCompletion (curvePlaceRestriction q)) x) =
      algebraMap L (curvePlaceCompletion q) (algebraMap K L x) :=
  CurvePlaceCompletionExtension.completionMap_algebraMap _ _ x

theorem continuous_curvePlaceCompletionInclusion (q : AlgebraicCurve.Place k L) :
    Continuous (curvePlaceCompletionInclusion (K := K) q) :=
  CurvePlaceCompletionExtension.continuous_completionMap _ _

@[simp]
theorem curvePlaceCompletionInclusion_mem_integers_iff
    (q : AlgebraicCurve.Place k L) (x : curvePlaceCompletion (curvePlaceRestriction (K := K) q)) :
    curvePlaceCompletionInclusion q x ∈ curvePlaceCompletionIntegers q ↔
      x ∈ curvePlaceCompletionIntegers (curvePlaceRestriction q) :=
  CurvePlaceCompletedIntegersExtension.completionMap_mem_integers_iff
    (curvePlaceRestriction (K := K) q) ⟨q, rfl⟩ x

/-- The coordinate formula also retains any specified original lower place and upper place above it. -/
theorem curvePlaceAdeleInclusion_apply_above (a : CurvePlaceAdeleRing k K)
    (p : AlgebraicCurve.Place k K) (q : CurvePlacesAbove k L p) :
    curvePlaceAdeleInclusion k K L a q.1 =
      CurvePlaceCompletionExtension.completionMap p q (a p) := by
  rcases q with ⟨q, hq⟩
  have hp := (curvePlaceRestriction_eq_iff q p).mpr hq
  subst p
  rfl

/-- No lower adelic coordinate is lost, since every lower place has an upper extension. -/
theorem curvePlaceAdeleInclusion_injective :
    Function.Injective (curvePlaceAdeleInclusion (k := k) (K := K) (L := L)) := by
  intro a b hab
  apply RestrictedProduct.ext
  intro p
  let q : CurvePlacesAbove k L p := ⟨curvePlaceExtension p, curvePlaceExtension_comap p⟩
  apply (CurvePlaceCompletionExtension.completionMap p q).injective
  exact (curvePlaceAdeleInclusion_apply_above a p q).symm.trans
    ((congrArg (fun x : CurvePlaceAdeleRing k L => x q.1) hab).trans
      (curvePlaceAdeleInclusion_apply_above b p q))

/-- Integrality outside the full upper exceptional preimage is exactly lower-level integrality. -/
theorem curvePlaceAdeleInclusion_mem_level_iff
    (S : Finset (AlgebraicCurve.Place k K)) (a : CurvePlaceAdeleRing k K) :
    curvePlaceAdeleInclusion k K L a ∈
        curvePlaceAdeleLevel k L (curvePlaceExceptionalPreimage (L := L) S) ↔
      a ∈ curvePlaceAdeleLevel k K S := by
  constructor
  · intro ha p hp
    obtain ⟨q, rfl⟩ := curvePlaceRestriction_surjective (L := L) p
    exact (curvePlaceCompletionInclusion_mem_integers_iff q _).mp
      (ha q (by simpa using hp))
  · intro ha q hq
    exact (curvePlaceCompletionInclusion_mem_integers_iff q _).mpr
      (ha _ (by simpa using hq))

/-- The literal inclusion restricted to a lower level and its full upper preimage. -/
def curvePlaceAdeleLevelInclusion (S : Finset (AlgebraicCurve.Place k K)) :
    curvePlaceAdeleLevel k K S →+*
      curvePlaceAdeleLevel k L (curvePlaceExceptionalPreimage (L := L) S) :=
  (curvePlaceAdeleInclusion (k := k) (K := K) (L := L)).restrict
    (curvePlaceAdeleLevel k K S)
    (curvePlaceAdeleLevel k L (curvePlaceExceptionalPreimage (L := L) S))
    (fun a ha => (curvePlaceAdeleInclusion_mem_level_iff S a).mpr ha)

@[simp]
theorem curvePlaceAdeleLevelInclusion_coe (S : Finset (AlgebraicCurve.Place k K))
    (a : curvePlaceAdeleLevel k K S) :
    (curvePlaceAdeleLevelInclusion (L := L) S a : CurvePlaceAdeleRing k L) =
      curvePlaceAdeleInclusion k K L (a : CurvePlaceAdeleRing k K) := rfl

theorem continuous_curvePlaceAdeleLevelInclusion
    (S : Finset (AlgebraicCurve.Place k K)) :
    Continuous (curvePlaceAdeleLevelInclusion (L := L) S) :=
  (continuous_curvePlaceAdeleInclusion.comp continuous_subtype_val).subtype_mk _

/-- The level inclusion commutes with the two original outside-S diagonal maps. -/
theorem curvePlaceAdeleLevelInclusion_diagonal
    (S : Finset (AlgebraicCurve.Place k K)) (a : curvePlaceSIntegers k K S) :
    curvePlaceAdeleLevelInclusion (L := L) S (curvePlaceAdeleLevelDiagonal k K S a) =
      curvePlaceAdeleLevelDiagonal k L (curvePlaceExceptionalPreimage (L := L) S)
        (curvePlaceSIntegersExtension (L := L) S a) := by
  apply Subtype.ext
  apply RestrictedProduct.ext
  intro q
  exact curvePlaceCompletionInclusion_algebraMap q a.val

end Langlands.Global
