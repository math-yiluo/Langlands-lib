import Langlands.Representation.RankinSelberg.SphericalTorusRecursion
import Langlands.Representation.RankinSelberg.UnramifiedSphericalVectorProof
import Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof

/-! # Spherical Whittaker values on nonnegative dominant torus elements -/

noncomputable section

namespace Langlands.RankinSelberg.UnramifiedWhittaker

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa Langlands.GeneralLinear.Spherical
open Langlands.Conductor Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.Unramified Langlands.Unramified.MinusculeCosets Langlands.Correspondence
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit)

universe uF uV

/-- The error between a torus sequence and its identity value times the normalized
dominant polynomial. -/
def torusRecursionError {r : ℕ} (q : ℕ) (z : Fin (r + 1) → ℂˣ)
    (d : (Fin (r + 1) → ℤ) → ℂ) (α : Fin (r + 1) → ℤ) : ℂ :=
  d α - d 0 * sphericalTorusPolynomial q z α

/-- The minuscule relations determine the normalized polynomial values on partitions. -/
theorem eq_sphericalTorusPolynomial_of_recursion {r : ℕ} (q : ℕ) (hq : 0 < q)
    (z : Fin (r + 1) → ℂˣ) (d : (Fin (r + 1) → ℤ) → ℂ)
    (hoff : ∀ α, ¬ Antitone α → d α = 0)
    (hrec : ∀ α, IsPartitionExponent α → ∀ k : ℕ, 1 ≤ k → k ≤ r + 1 →
      ((Real.sqrt (q : ℝ) : ℂ) ^ (k * (r + 1 - k)) *
        elementaryCoefficient (Eigenvalues.ofTuple z) k) * d α =
      ∑ S : {S : Finset (Fin (r + 1)) // S.card = k},
        (q : ℂ) ^ Fintype.card (RadicalPairs S.val) * d (α + subsetExponent S.val)) :
    ∀ α, IsPartitionExponent α → d α = d 0 * sphericalTorusPolynomial q z α := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hw : ∀ k, k ≤ r + 1 →
      (q : ℂ) ^ Fintype.card (RadicalPairs (initialSegment (r + 1) k)) ≠ 0 :=
    fun _ _ => pow_ne_zero _ hq0
  have herr : SatisfiesHeckeRecursion
      (fun S => (q : ℂ) ^ Fintype.card (RadicalPairs S)) (torusRecursionError q z d) := by
    intro α hα k hk1 hkm
    let c : ℂ := (Real.sqrt (q : ℝ) : ℂ) ^ (k * (r + 1 - k)) *
      elementaryCoefficient (Eigenvalues.ofTuple z) k
    refine ⟨c, ?_⟩
    have hp := sphericalTorusPolynomial_recursion q hq z α hα.1 hα.2 k
    change c * sphericalTorusPolynomial q z α = _ at hp
    calc
      c * torusRecursionError q z d α =
          c * d α - d 0 * (c * sphericalTorusPolynomial q z α) := by
        unfold torusRecursionError
        ring
      _ = _ := by
        rw [hrec α hα k hk1 hkm, hp, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro S _
        unfold torusRecursionError
        ring
  have hoff' : ∀ α, ¬ Antitone α → torusRecursionError q z d α = 0 := by
    intro α hα
    rw [torusRecursionError, hoff α hα, sphericalTorusPolynomial_eq_zero q z α hα]
    ring
  have hzero : torusRecursionError q z d 0 = 0 := by
    rw [torusRecursionError, sphericalTorusPolynomial_zero]
    ring
  intro α hα
  exact sub_eq_zero.mp (eq_zero_of_satisfiesHeckeRecursion hw herr hoff' hzero α hα)

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

section Model

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
variable {θ : upperUnipotent (r + 1) F.Carrier →* ℂˣ}

/-- Every supplied normalized spherical test in a constituent has the prescribed torus
values, for either character satisfying the explicit conductor conditions. -/
theorem sphericalTest_torus_eq_polynomial (hπ : IsSmooth π)
    [Representation.IsIrreducible π] (z : Fin (r + 1) → ℂˣ)
    (hsub : IsSubquotientOf (principalSeriesOfTuple F z) π)
    (hθK : IsIntegrallyTrivial (ValuativeRel.valuation F.Carrier) θ)
    (hθ : ∀ i : Fin r, ∃ x : F.Carrier,
      ValuativeRel.valuation F.Carrier x *
        ValuativeRel.valuation F.Carrier (F.canonicalTopologicalData.uniformizerUnit : F.Carrier)
          ≤ 1 ∧ θ (adjacentUnit i x) ≠ 1)
    (ℓ : functionals (upperUnipotent (r + 1) F.Carrier) θ π) (hℓ : ℓ.val ≠ 0)
    (w : SphericalTest π ℓ) (α : Fin (r + 1) → ℤ) (hα : IsPartitionExponent α) :
    sphericalTestFunction π ℓ w (torus F.canonicalTopologicalData.uniformizerUnit α) =
      sphericalTorusPolynomial F.canonicalTopologicalData.residueCardinality z α := by
  classical
  obtain ⟨v, hv⟩ := modelMap_surjective π ℓ w.val.val
  have hval (g : Langlands.GeneralLinear (r + 1) F.Carrier) :
      sphericalTestFunction π ℓ w g = ℓ.val (π g v) := by
    exact (congrArg (fun u : (coefficientModel π ℓ).toSubmodule => u.val.val g) hv).symm
  have hvK : v ∈ fixedVectors π (sphericalSubgroup F r) :=
    mem_fixedVectors_of_model F π ℓ (modelEquiv π ℓ hℓ).injective v
      (by rw [hv]; exact (mem_sphericalModelSpace π ℓ w.val.val).mp w.val.property)
  let vK : fixedVectors π (sphericalSubgroup F r) := ⟨v, hvK⟩
  have hcoset (i : Fin (r + 2)) (g : Langlands.GeneralLinear (r + 1) F.Carrier) :
      (∑ a : CosetIndex F.canonicalTopologicalData.ResidueField (r + 1) i.val,
        sphericalTestFunction π ℓ w
          (g * labelledRep F.canonicalTopologicalData.uniformizerUnit (residueLift F) a)) =
        standardHeckeScalar F (Eigenvalues.ofTuple z) i * sphericalTestFunction π ℓ w g := by
    have hvec := cornerAction_of_isSubquotientOf F π hπ hsub i vK
    rw [standardHecke_cornerAction_eq_sum F π hπ i vK] at hvec
    calc
      _ = ∑ a : CosetIndex F.canonicalTopologicalData.ResidueField (r + 1) i.val,
          ℓ.val (π g (π (labelledRep F.canonicalTopologicalData.uniformizerUnit
            (residueLift F) a) v)) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [hval, map_mul, Module.End.mul_apply]
      _ = ℓ.val (π g (∑ a : CosetIndex F.canonicalTopologicalData.ResidueField (r + 1) i.val,
          π (labelledRep F.canonicalTopologicalData.uniformizerUnit (residueLift F) a) vK)) := by
        simp only [map_sum]
        rfl
      _ = _ := by
        rw [hvec, map_smul, map_smul, smul_eq_mul, ← hval]
  have hK : ∀ g, ∀ k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer r,
      sphericalTestFunction π ℓ w (g * k) = sphericalTestFunction π ℓ w g :=
    fun g k hk => sphericalTestFunction_right_invariant π ℓ w ⟨k, hk⟩ g
  let d : (Fin (r + 1) → ℤ) → ℂ :=
    fun β => sphericalTestFunction π ℓ w (torus F.canonicalTopologicalData.uniformizerUnit β)
  have hoff : ∀ β, ¬ Antitone β → d β = 0 :=
    fun β hβ => eval_torus_eq_zero_of_not_antitone (uniformizerUnit_isUniformizingElement F)
      (sphericalTestFunction_equivariance π ℓ w) hK hθ hβ
  have hrec : ∀ β, IsPartitionExponent β → ∀ k : ℕ, 1 ≤ k → k ≤ r + 1 →
      ((Real.sqrt (F.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) ^ (k * (r + 1 - k)) *
        elementaryCoefficient (Eigenvalues.ofTuple z) k) * d β =
      ∑ S : {S : Finset (Fin (r + 1)) // S.card = k},
        (F.canonicalTopologicalData.residueCardinality : ℂ) ^
          Fintype.card (RadicalPairs S.val) * d (β + subsetExponent S.val) := by
    intro β hβ k _ hkm
    have hc := hcoset ⟨k, by omega⟩ (torus F.canonicalTopologicalData.uniformizerUnit β)
    rw [sum_eval_torus_mul_labelledRep (uniformizerUnit_isUniformizingElement F).1.le
      hθK (sphericalTestFunction_equivariance π ℓ w) (residueLift_mem F) hβ.1 k] at hc
    simpa only [d, standardHeckeScalar, PadicField.TopologicalData.residueCardinality,
      Nat.card_eq_fintype_card] using hc.symm
  have hd0 : d 0 = 1 := by
    dsimp [d]
    have h0 : torus F.canonicalTopologicalData.uniformizerUnit
        (0 : Fin (r + 1) → ℤ) = 1 := by
      rw [torus]
      simp only [Pi.zero_apply, zpow_zero]
      exact map_one diagonalUnits
    rw [h0, sphericalTestFunction_one]
  have hq : 0 < F.canonicalTopologicalData.residueCardinality :=
    Nat.zero_lt_of_lt F.canonicalTopologicalData.residueCardinality_gt_one
  have hresult := eq_sphericalTorusPolynomial_of_recursion
    F.canonicalTopologicalData.residueCardinality hq z d hoff hrec α hα
  simpa only [hd0, one_mul] using hresult

end Model

/-- The formula for the original additive character and every supplied normalized test. -/
theorem sphericalTest_torus_schur {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (hψ : HasIntegerConductor ψ)
    (χ : Fin (r + 1) → QuasiCharacter F)
    (hgen : IsUnramifiedGenericConstituent F ψ π χ)
    (ℓ : glFunctionals ψ r π) (hℓ : ℓ.val ≠ 0) (w : SphericalTest π ℓ)
    (α : Fin (r + 1) → ℤ) (hα : IsPartitionExponent α) :
    sphericalTestFunction π ℓ w (torus F.canonicalTopologicalData.uniformizerUnit α) =
      halfModulus F.canonicalTopologicalData.residueCardinality α *
        satakeSchur (characterValues F χ) α := by
  have : Representation.IsIrreducible π := hgen.1.1
  have hsub : IsSubquotientOf (principalSeriesOfTuple F (characterValues F χ)) π := by
    rw [principalSeriesOfTuple, characterTuple_characterValues F χ hgen.2.2.1]
    exact hgen.2.2.2
  rw [sphericalTest_torus_eq_polynomial F π hgen.1.2.1.1 (characterValues F χ) hsub
    (isIntegrallyTrivial_standardCharacter hψ.1 r) (standardCharacter_nondegenerate F ψ hψ)
    ℓ hℓ w α hα, sphericalTorusPolynomial_eq_schur _ _ α hα.1 hα.2]

/-- The same formula for the inverse character, with its supplied functional and test. -/
theorem inverseSphericalTest_torus_schur {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (hψ : HasIntegerConductor ψ)
    (χ : Fin (r + 1) → QuasiCharacter F)
    (hgen : IsUnramifiedGenericConstituent F ψ π χ)
    (ℓ : glInverseFunctionals ψ r π) (hℓ : ℓ.val ≠ 0) (w : SphericalTest π ℓ)
    (α : Fin (r + 1) → ℤ) (hα : IsPartitionExponent α) :
    sphericalTestFunction π ℓ w (torus F.canonicalTopologicalData.uniformizerUnit α) =
      halfModulus F.canonicalTopologicalData.residueCardinality α *
        satakeSchur (characterValues F χ) α := by
  have : Representation.IsIrreducible π := hgen.1.1
  have hsub : IsSubquotientOf (principalSeriesOfTuple F (characterValues F χ)) π := by
    rw [principalSeriesOfTuple, characterTuple_characterValues F χ hgen.2.2.1]
    exact hgen.2.2.2
  rw [sphericalTest_torus_eq_polynomial F π hgen.1.2.1.1 (characterValues F χ) hsub
    (isIntegrallyTrivial_inverseStandardCharacter hψ.1 r)
    (inverseStandardCharacter_nondegenerate F ψ hψ) ℓ hℓ w α hα,
    sphericalTorusPolynomial_eq_schur _ _ α hα.1 hα.2]

end Langlands.RankinSelberg.UnramifiedWhittaker
