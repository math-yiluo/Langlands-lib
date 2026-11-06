import Langlands.Global.Arithmetic.CMHalfWeightInfinity
import Langlands.Global.Arithmetic.CMInfinityExtension
import Langlands.ClassField.Global.CyclicReciprocityParts

/-! # Real norm signs for the normalized CM infinity character -/

noncomputable section

universe u

namespace Langlands.Global.CMHalfWeight

open NumberField
open scoped NumberField

variable {K : Type u} [Field K] [NumberField K] [IsCMField K]

/-- Restriction of the normalized infinity character to the nonzero elements
of the maximal real subfield. -/
def realInfinityRestriction (t : InfinityType K) :
    (maximalRealSubfield K)ˣ →* ℂˣ :=
  (normalizedCharacter t).toMonoidHom.comp
    (CMUnramifiedInfinity.infinityDiagonal.comp
      (Units.map (algebraMap (maximalRealSubfield K) K).toMonoidHom))

private theorem embedding_real_restriction (v : InfinitePlace K)
    (a : maximalRealSubfield K) :
    v.embedding (algebraMap (maximalRealSubfield K) K a) =
      (IsCMField.equivInfinitePlace K v).embedding a := by
  exact (DFunLike.congr_fun
    (v.comap_embedding_of_isReal (algebraMap (maximalRealSubfield K) K)
      (IsTotallyReal.isReal _)) a).symm

private theorem prod_coordinates_real_diagonal (a : (maximalRealSubfield K)ˣ) :
    ∏ v : InfinitePlace K, InfinityType.coordinate v
      (CMUnramifiedInfinity.infinityDiagonal
        (Units.map (algebraMap (maximalRealSubfield K) K).toMonoidHom a)) =
      Units.map (Rat.castHom ℂ).toMonoidHom (Units.map (Algebra.norm ℚ) a) := by
  apply Units.ext
  rw [Units.coe_prod]
  simp only [CMUnramifiedInfinity.coordinate_diagonal_units, Units.coe_map]
  have hp := Langlands.ClassField.Global.CyclicReciprocity.algebraMap_norm_eq_prod
    (a : maximalRealSubfield K)
  have hreal (v : InfinitePlace (maximalRealSubfield K)) :
      (Langlands.ClassField.Global.CyclicReciprocity.placeFactor v a : ℂ) =
        v.embedding a := by
    simp only [Langlands.ClassField.Global.CyclicReciprocity.placeFactor,
      IsTotallyReal.isReal, ↓reduceIte]
    exact (Complex.conj_eq_iff_re.mp
      (congrArg (fun f : maximalRealSubfield K →+* ℂ => f a)
        (InfinitePlace.conjugate_embedding_eq_of_isReal (IsTotallyReal.isReal v))))
  calc
    _ = ∏ v : InfinitePlace K,
        (IsCMField.equivInfinitePlace K v).embedding a :=
      Finset.prod_congr rfl fun v _ => embedding_real_restriction v a
    _ = ∏ v : InfinitePlace (maximalRealSubfield K), v.embedding a :=
      Fintype.prod_equiv (IsCMField.equivInfinitePlace K) _ _ (fun _ => rfl)
    _ = ((Algebra.norm ℚ (a : maximalRealSubfield K) : ℚ) : ℂ) := by
      rw [← Complex.ofReal_ratCast, hp, Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun v _ => (hreal v).symm
    _ = _ := rfl

/-- The restriction to the real subfield depends only on its rational norm. -/
theorem realInfinityRestriction_eq_norm_sign {t : InfinityType K}
    (ht : t.IsPureOfWeight 1) (a : (maximalRealSubfield K)ˣ) :
    realInfinityRestriction t a =
      (Units.map (Rat.castHom ℂ).toMonoidHom (Units.map (Algebra.norm ℚ) a)) /
        absoluteValue
          (Units.map (Rat.castHom ℂ).toMonoidHom (Units.map (Algebra.norm ℚ) a)) := by
  change normalizedCharacter t (CMUnramifiedInfinity.infinityDiagonal
    (Units.map (algebraMap (maximalRealSubfield K) K).toMonoidHom a)) = _
  rw [normalizedCharacter_of_coordinates_real ht]
  · rw [Finset.prod_div_distrib, ← map_prod, prod_coordinates_real_diagonal]
  · intro v
    apply Units.ext
    simp only [Units.coe_star, CMUnramifiedInfinity.coordinate_diagonal_units,
      Units.coe_map]
    change star (v.embedding (algebraMap (maximalRealSubfield K) K
      (a : maximalRealSubfield K))) = v.embedding
        (algebraMap (maximalRealSubfield K) K (a : maximalRealSubfield K))
    rw [embedding_real_restriction]
    exact congrArg (fun f : maximalRealSubfield K →+* ℂ => f a)
      (InfinitePlace.conjugate_embedding_eq_of_isReal (IsTotallyReal.isReal _))

/-- Positive rational norm makes the normalized infinity character trivial on
the corresponding real principal element. -/
theorem normalizedCharacter_real_diagonal_of_norm_pos {t : InfinityType K}
    (ht : t.IsPureOfWeight 1) (a : (maximalRealSubfield K)ˣ)
    (ha : 0 < Algebra.norm ℚ (a : maximalRealSubfield K)) :
    normalizedCharacter t
      (CMUnramifiedInfinity.infinityDiagonal
        (Units.map (algebraMap (maximalRealSubfield K) K).toMonoidHom a)) = 1 := by
  change realInfinityRestriction t a = 1
  rw [realInfinityRestriction_eq_norm_sign ht]
  have habs : absoluteValue
      (Units.map (Rat.castHom ℂ).toMonoidHom (Units.map (Algebra.norm ℚ) a)) =
      Units.map (Rat.castHom ℂ).toMonoidHom (Units.map (Algebra.norm ℚ) a) := by
    apply Units.ext
    change (‖((Algebra.norm ℚ (a : maximalRealSubfield K) : ℚ) : ℂ)‖ : ℂ) = _
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Rat.cast_pos.mpr ha)]
    rfl
  rw [habs, div_self']

end Langlands.Global.CMHalfWeight
