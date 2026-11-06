import Langlands.Global.Arithmetic.CMHalfWeightInfinity
import Langlands.Global.Arithmetic.CMInfinityExtension
import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.Global.AdelicFunctoriality.NormReduction
import Mathlib.FieldTheory.Galois.Basic

/-! # Archimedean triviality on included CM idele norms -/

noncomputable section

universe u

namespace Langlands.Global.CMHalfWeight

open NumberField AdelicFunctoriality Algebra
open scoped NumberField

variable {K : Type u} [Field K] [NumberField K] [IsCMField K]

/-- Pull the normalized infinity character back to the whole idele group. -/
def ideleInfinityCharacter (t : InfinityType K) : Ideles K →ₜ* ℂˣ :=
  (normalizedCharacter t).comp CMUnramifiedInfinity.infinityProjection

private theorem algebraMap_real_norm (a : K) :
    algebraMap (maximalRealSubfield K) K (Algebra.norm (maximalRealSubfield K) a) =
      a * IsCMField.complexConj K a := by
  classical
  have hcard : Fintype.card (K ≃ₐ[maximalRealSubfield K] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      IsQuadraticExtension.finrank_eq_two]
  have hset : Finset.univ =
      {1, IsCMField.complexConj K} := by
    apply (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
    rw [Finset.card_univ, hcard, Finset.card_pair
      (IsCMField.complexConj_ne_one K).symm]
  rw [Algebra.norm_eq_prod_automorphisms, hset,
    Finset.prod_pair (IsCMField.complexConj_ne_one K).symm]
  rfl

/-- On infinite adeles, the included norm for the CM quadratic extension is
the product with the arithmetic conjugate. -/
theorem infiniteAdeleNorm_cm_mul_conj (x : InfiniteAdeles K) :
    infiniteAdeleMap (algebraMap (maximalRealSubfield K) K)
      (infiniteAdeleNorm (K := maximalRealSubfield K) x) =
      x * infiniteAdeleEquiv (IsCMField.complexConj K).toRingEquiv x := by
  have h := (InfiniteAdeleRing.denseRange_algebraMap K).equalizer
    ((continuous_infiniteAdeleMap (algebraMap (maximalRealSubfield K) K)).comp
      (continuous_infiniteAdeleNorm (K := maximalRealSubfield K) (L := K)))
    (continuous_id.mul (continuous_infiniteAdeleEquiv
      (IsCMField.complexConj K).toRingEquiv)) (by
      funext a
      have hn : infiniteAdeleNorm (K := maximalRealSubfield K)
          (algebraMap K (InfiniteAdeles K) a) =
          algebraMap (maximalRealSubfield K) (InfiniteAdeles (maximalRealSubfield K))
            (Algebra.norm (maximalRealSubfield K) a) := by
        funext p
        exact infiniteNorm_principal p a
      dsimp only [Function.comp_apply]
      change infiniteAdeleMap (algebraMap (maximalRealSubfield K) K)
          (infiniteAdeleNorm (K := maximalRealSubfield K)
            (algebraMap K (InfiniteAdeles K) a)) =
        algebraMap K (InfiniteAdeles K) a *
          infiniteAdeleEquiv (IsCMField.complexConj K).toRingEquiv
            (algebraMap K (InfiniteAdeles K) a)
      rw [hn, infiniteAdeleMap_diagonal, algebraMap_real_norm, map_mul,
        infiniteAdeleEquiv_diagonal]
      rfl)
  exact congrFun h x

/-- Arithmetic conjugation inverts the pulled-back normalized weight-one
infinity character on every actual idele. -/
theorem ideleInfinityCharacter_complexConj {t : InfinityType K}
    (ht : t.IsPureOfWeight 1) (x : Ideles K) :
    ideleInfinityCharacter t
      (ideleEquiv (IsCMField.complexConj K).toRingEquiv x) =
        (ideleInfinityCharacter t x)⁻¹ := by
  apply normalizedCharacter_of_coordinates_star ht
  intro v
  apply Units.ext
  rw [Units.coe_star]
  exact ideleComplexConj_infinite_coordinate x v

/-- The pulled-back normalized infinity character kills the norm of every
idele after inclusion from the maximal real subfield. -/
theorem ideleInfinityCharacter_included_norm {t : InfinityType K}
    (ht : t.IsPureOfWeight 1) (x : Ideles K) :
    ideleInfinityCharacter t
      (ideleInclusion (K := maximalRealSubfield K)
        (ideleNorm (K := maximalRealSubfield K) x)) = 1 := by
  have hprod :
      CMUnramifiedInfinity.infinityProjection
        (ideleInclusion (K := maximalRealSubfield K)
          (ideleNorm (K := maximalRealSubfield K) x)) =
      CMUnramifiedInfinity.infinityProjection x *
        CMUnramifiedInfinity.infinityProjection
          (ideleEquiv (IsCMField.complexConj K).toRingEquiv x) := by
    apply Units.ext
    exact infiniteAdeleNorm_cm_mul_conj (x : Adeles K).1
  change normalizedCharacter t (CMUnramifiedInfinity.infinityProjection
    (ideleInclusion (K := maximalRealSubfield K)
      (ideleNorm (K := maximalRealSubfield K) x))) = 1
  rw [hprod, map_mul]
  change ideleInfinityCharacter t x *
    ideleInfinityCharacter t
      (ideleEquiv (IsCMField.complexConj K).toRingEquiv x) = 1
  rw [ideleInfinityCharacter_complexConj ht, mul_inv_cancel]

/-- Finite ideles have trivial normalized infinity value. -/
theorem ideleInfinityCharacter_finite (t : InfinityType K) (x : FiniteIdeles K) :
    ideleInfinityCharacter t (finiteIdelesInclusion K x) = 1 := by
  have h : CMUnramifiedInfinity.infinityProjection (finiteIdelesInclusion K x) = 1 := by
    apply Units.ext
    rfl
  change normalizedCharacter t (CMUnramifiedInfinity.infinityProjection
    (finiteIdelesInclusion K x)) = 1
  rw [h, map_one]

end Langlands.Global.CMHalfWeight
