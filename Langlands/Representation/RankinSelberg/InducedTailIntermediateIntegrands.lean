import Langlands.Representation.RankinSelberg.InducedTailIntermediateCoefficientAdapters
import Langlands.Representation.RankinSelberg.InducedTailIntermediateLocalization

/-! # Actual zero-row integrands in the intermediate lower-block chart -/

noncomputable section

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear Whittaker HarmonicAnalysis

universe uF

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
variable (n d c₀ : ℕ)

omit [IsTopologicalRing F] in
/-- On an identity extension, an inverse coefficient transported along equality
of numerical ranks has the value of the original coefficient. -/
theorem inverseWhittakerRankCast_appendIdentity
    (e : ℕ) (he : n + d = n + e)
    (Wtest : InverseWhittakerFunctions ψ (n + d))
    (g : Langlands.GeneralLinear (n + 1) F) :
    (inverseWhittakerRankCast ψ he Wtest).val (appendIdentity n e g) =
      Wtest.val (appendIdentity n d g) := by
  rw [inverseWhittakerRankCast_apply]
  apply congrArg Wtest.val
  apply Units.ext
  ext i j
  change appendIdentity n e g (Fin.cast (by omega) i)
    (Fin.cast (by omega) j) = _
  simp only [appendIdentity_entry, Fin.val_cast, Fin.cast_inj]

omit [IsTopologicalRing F] in
/-- Evaluating the actual full zero-row JPSS function on the lower-block
matrix gives precisely the coefficient product used by localization. The
Whittaker coefficient is transported only along equality of numerical ranks. -/
theorem full_unequalRankFunction_lowerBlockPair
    (W₀ : WhittakerFunctions ψ (n + 1 + d + c₀))
    (Wtest : InverseWhittakerFunctions ψ (n + d)) (s : ℂ)
    (r : Matrix (Fin 0) (Fin (n + d + 1)) F)
    (g : Langlands.GeneralLinear (n + 1) F)
    (x : Matrix (Fin d) (Fin (n + 1)) F)
    (h : lowerTriangularSubgroup d F) :
    unequalRankFunction ψ abv 0 c₀
      (whittakerRankCast ψ (by omega) W₀) Wtest s r
      (reindex (finCongr (by omega : (n + 1) + d = n + d + 1))
        (lowerBlockPair g x h)) =
      W₀.val (lowerBlockLocalization (c₀ + 1) g x h) *
        Wtest.val (reindex (finCongr (by omega : (n + 1) + d = n + d + 1))
          (lowerBlockPair g x h)) *
        determinantWeight abv
          (reindex (finCongr (by omega : (n + 1) + d = n + d + 1))
            (lowerBlockPair g x h))
          (s - ((c₀ + 1 : ℕ) : ℂ) / 2) := by
  rw [unequalRankFunction, unequalRankMatrix_zero_rows, whittakerRankCast_apply]
  simp only [Nat.zero_add]
  have hmatrix :
      reindex (finCongr (by omega :
        (n + d) + (0 + c₀ + 1) + 1 = (n + 1 + d + c₀) + 1))
        (appendIdentity (n + d) (0 + c₀ + 1)
          (reindex (finCongr (by omega : (n + 1) + d = n + d + 1))
            (lowerBlockPair g x h))) =
        lowerBlockLocalization (c₀ + 1) g x h := by
    have he := lowerBlockLocalization_eq_outer_appendIdentity
      (n + d) (c₀ + 1) (by omega : (n + 1) + d = n + d + 1) g x h
    apply Units.ext
    ext i j
    have hij := congrArg (fun M =>
      M (Fin.cast (by omega : (n + 1 + d + c₀) + 1 = (n + d) + (c₀ + 1) + 1) i)
        (Fin.cast (by omega) j)) he
    change lowerBlockLocalization (c₀ + 1) g x h i j =
      appendIdentity (n + d) (c₀ + 1)
        (reindex (finCongr (by omega)) (lowerBlockPair g x h))
        (Fin.cast (by omega) i) (Fin.cast (by omega) j) at hij
    change appendIdentity (n + d) (0 + c₀ + 1)
        (reindex (finCongr (by omega)) (lowerBlockPair g x h))
        (Fin.cast (by omega) i) (Fin.cast (by omega) j) = _
    rw [hij]
    simp only [appendIdentity_entry, Fin.val_cast, Fin.cast_inj]
  rw [hmatrix]

omit [IsTopologicalRing F] in
/-- The same identity holds for the descended full integrand on the actual
left-unipotent quotient, evaluated at the lower-block representative. -/
theorem full_unequalRankIntegrand_lowerBlockPair
    (W₀ : WhittakerFunctions ψ (n + 1 + d + c₀))
    (Wtest : InverseWhittakerFunctions ψ (n + d)) (s : ℂ)
    (r : Matrix (Fin 0) (Fin (n + d + 1)) F)
    (g : Langlands.GeneralLinear (n + 1) F)
    (x : Matrix (Fin d) (Fin (n + 1)) F)
    (h : lowerTriangularSubgroup d F) :
    unequalRankIntegrand ψ abv 0 c₀
      (whittakerRankCast ψ (by omega) W₀) Wtest s r
      (Quotient.mk _
        (reindex (finCongr (by omega : (n + 1) + d = n + d + 1))
          (lowerBlockPair g x h))) =
      W₀.val (lowerBlockLocalization (c₀ + 1) g x h) *
        Wtest.val (reindex (finCongr (by omega : (n + 1) + d = n + d + 1))
          (lowerBlockPair g x h)) *
        determinantWeight abv
          (reindex (finCongr (by omega : (n + 1) + d = n + d + 1))
            (lowerBlockPair g x h))
          (s - ((c₀ + 1 : ℕ) : ℂ) / 2) :=
  full_unequalRankFunction_lowerBlockPair ψ abv n d c₀ W₀ Wtest s r g x h

/-- Recasting the two tail coefficients at the inverse character also
identifies the actual descended zero-row tail integrand. -/
theorem reversedTail_unequalRankIntegrand
    (Wtest : InverseWhittakerFunctions ψ (n + (0 + d + 1)))
    (Wtail : WhittakerFunctions ψ n) (s : ℂ)
    (r : Matrix (Fin 0) (Fin (n + 1)) F)
    (g : Langlands.GeneralLinear (n + 1) F) :
    unequalRankIntegrand (ψ.scale (-1)) abv 0 d
      (inverseAsScaledStandard ψ Wtest) (standardAsScaledInverse ψ Wtail)
      s r (Quotient.mk _ g) =
      Wtail.val g * Wtest.val (appendIdentity n (0 + d + 1) g) *
        determinantWeight abv g (s - ((d + 1 : ℕ) : ℂ) / 2) := by
  simpa only [unequalRankIntegrand_mk, unequalRankFunction, Nat.zero_add] using
    reversedTail_unequalRankFunction ψ abv n d Wtest Wtail s r g

/-- When the positive test-to-tail gap is written as `k + 1`, the actual
reversed-character tail integrand uses the same test coefficient as the full
comparison. Its explicit numerical rank cast changes no coefficient values. -/
theorem reversedTail_unequalRankIntegrand_of_gap_eq
    (k : ℕ) (hd : d = k + 1)
    (Wtest : InverseWhittakerFunctions ψ (n + d))
    (Wtail : WhittakerFunctions ψ n) (s : ℂ)
    (r : Matrix (Fin 0) (Fin (n + 1)) F)
    (g : Langlands.GeneralLinear (n + 1) F) :
    unequalRankIntegrand (ψ.scale (-1)) abv 0 k
      (inverseAsScaledStandard ψ
        (inverseWhittakerRankCast ψ (by omega : n + d = n + (0 + k + 1)) Wtest))
      (standardAsScaledInverse ψ Wtail) s r (Quotient.mk _ g) =
      Wtail.val g * Wtest.val (appendIdentity n d g) *
        determinantWeight abv g (s - (d : ℂ) / 2) := by
  rw [unequalRankIntegrand_mk, unequalRankMatrix_zero_rows]
  change (inverseWhittakerRankCast ψ (by omega) Wtest).val
      (appendIdentity n (0 + k + 1) g) * Wtail.val g * _ = _
  rw [inverseWhittakerRankCast_appendIdentity,
    show 0 + k + 1 = d by omega, mul_comm _ (Wtail.val g)]

end Langlands.RankinSelberg.InducedTailIntermediate
