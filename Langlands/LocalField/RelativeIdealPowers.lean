import Langlands.LocalField.RelativeIntegers

/-! Relative powers of the actual maximal ideals. -/

namespace Langlands.PadicField.TopologicalData

open IsLocalRing IsDiscreteValuationRing

universe u v

variable {p : ℕ} [Fact p.Prime]
  {F : PadicField.{u} p} {E : PadicField.{v} p}
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  (T : F.TopologicalData) (S : E.TopologicalData)

/-- The absolute ramification indices determine the extended maximal ideal. -/
theorem map_maximalIdeal_of_ramificationIndex_eq_mul (e : ℕ)
    (he : S.ramificationIndex = e * T.ramificationIndex) :
    (maximalIdeal T.Integers).map (relativeIntegerMap T S) =
      maximalIdeal S.Integers ^ e := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  have hinj : Function.Injective (relativeIntegerMap T S) := by
    intro x y h
    apply Subtype.ext
    exact (algebraMap F.Carrier E.Carrier).injective (congrArg Subtype.val h)
  obtain ⟨π, hπ⟩ := exists_irreducible T.Integers
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible S.Integers
  have hI : (maximalIdeal T.Integers).map (relativeIntegerMap T S) ≠ ⊥ := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    apply Ideal.span_singleton_eq_bot.not.mpr
    exact fun h => hπ.ne_zero (hinj (by simpa only [map_zero] using h))
  obtain ⟨k, hk⟩ := ideal_eq_span_pow_irreducible hI hϖ
  have hk' : (maximalIdeal T.Integers).map (relativeIntegerMap T S) =
      maximalIdeal S.Integers ^ k := by
    rw [hk, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hp : ((maximalIdeal T.Integers).map (relativeIntegerMap T S)) ^
      T.ramificationIndex = maximalIdeal S.Integers ^ S.ramificationIndex := by
    rw [← Ideal.map_pow, ← T.span_prime_eq_maximalIdeal_pow,
      Ideal.map_span, Set.image_singleton, map_natCast,
      S.span_prime_eq_maximalIdeal_pow]
  rw [hk', ← pow_mul] at hp
  have hke : k * T.ramificationIndex = S.ramificationIndex := by
    have h := congrArg Order.coheight hp
    simpa only [coheight_pow_maximalIdeal, Nat.cast_inj] using h
  have hk_eq : k = e :=
    Nat.eq_of_mul_eq_mul_right T.ramificationIndex_pos (hke.trans he)
  simpa only [hk_eq] using hk'

/-- Extension of any maximal ideal power scales its exponent by the relative index. -/
theorem map_maximalIdeal_pow_of_ramificationIndex_eq_mul (e : ℕ)
    (he : S.ramificationIndex = e * T.ramificationIndex) (n : ℕ) :
    (maximalIdeal T.Integers ^ n).map (relativeIntegerMap T S) =
      maximalIdeal S.Integers ^ (e * n) := by
  rw [Ideal.map_pow, map_maximalIdeal_of_ramificationIndex_eq_mul T S e he, pow_mul]

/-- The maximal ideal formula for exactly the published relative integer scalars. -/
theorem map_maximalIdeal_algebraMap_of_ramificationIndex_eq_mul (e : ℕ)
    (he : S.ramificationIndex = e * T.ramificationIndex) :
    letI := relativeIntegerAlgebra T S
    (maximalIdeal T.Integers).map (algebraMap T.Integers S.Integers) =
      maximalIdeal S.Integers ^ e := by
  let := relativeIntegerAlgebra T S
  exact map_maximalIdeal_of_ramificationIndex_eq_mul T S e he

end Langlands.PadicField.TopologicalData
