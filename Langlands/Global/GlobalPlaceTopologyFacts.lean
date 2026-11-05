import Langlands.Global.AdeleProductSubspaceTopology
import Langlands.Global.CurvePlaceExtension
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.RingTheory.Ideal.Int

/-! # Arithmetic place facts for the adelic product subspace topology -/

noncomputable section

universe u

open IsDedekindDomain
open scoped Polynomial

namespace Langlands.Global

/-- A nonfield Jacobson domain of dimension at most one has infinitely many
nonzero prime ideals. -/
theorem infinite_heightOneSpectrum_of_jacobson (R : Type*) [CommRing R]
    [IsDedekindDomain R] [IsJacobsonRing R] (hR : ¬ IsField R) :
    Infinite (HeightOneSpectrum R) := by
  classical
  by_contra h
  let : Finite (HeightOneSpectrum R) := not_infinite_iff_finite.mp h
  let := Fintype.ofFinite (HeightOneSpectrum R)
  have hx (p : HeightOneSpectrum R) : ∃ x : R, x ∈ p.asIdeal ∧ x ≠ 0 := by
    by_contra! hn
    apply p.ne_bot
    apply le_antisymm _ bot_le
    intro y hy
    exact (Ideal.mem_bot).mpr (hn y hy)
  choose x hxm hx0 using hx
  have hn : (∏ p : HeightOneSpectrum R, x p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p _ => hx0 p)
  have hm : (∏ p : HeightOneSpectrum R, x p) ∈ (⊥ : Ideal R).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    intro M hM
    let p : HeightOneSpectrum R :=
      ⟨M, hM.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM.2 hR⟩
    exact Ideal.mem_of_dvd M (Finset.dvd_prod_of_mem x (Finset.mem_univ p)) (hxm p)
  rw [(inferInstance : IsJacobsonRing R).out (Ideal.isRadical_bot), Ideal.mem_bot] at hm
  exact hn hm

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- Extending a rational-function place gives an embedding into the places of
an arbitrary finite extension, including inseparable extensions. -/
def functionFieldPlaceExtensionEmbedding :
    AlgebraicCurve.Place k (RatFunc k) ↪ AlgebraicCurve.Place k F where
  toFun := curvePlaceExtension
  inj' := by
    intro p q h
    apply AlgebraicCurve.Place.ext
    have he := congrArg (fun r : AlgebraicCurve.Place k F =>
      r.toValuationSubring.comap (algebraMap (RatFunc k) F)) h
    simpa only [curvePlaceExtension_comap] using he

theorem functionField_places_infinite : Infinite (AlgebraicCurve.Place k F) := by
  let : Infinite (HeightOneSpectrum k[X]) :=
    infinite_heightOneSpectrum_of_jacobson k[X] (Polynomial.not_isField k)
  let : Infinite (AlgebraicCurve.Place k (RatFunc k)) :=
    Infinite.of_injective
      (AlgebraicCurve.Place.ofHeightOneSpectrum (K := k) (F := RatFunc k) (R := k[X]))
      AlgebraicCurve.Place.ofHeightOneSpectrum_injective
  exact Infinite.of_injective (functionFieldPlaceExtensionEmbedding k F)
    (functionFieldPlaceExtensionEmbedding k F).injective

omit [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- Each actual curve-place completion is noncompact in its original topology. -/
theorem curvePlaceCompletion_noncompact (v : AlgebraicCurve.Place k F) :
    NoncompactSpace (curvePlaceCompletion v) := by
  let : Infinite (RatFunc k) := Infinite.of_injective
    (algebraMap k[X] (RatFunc k)) (IsFractionRing.injective k[X] (RatFunc k))
  let : Infinite F := Infinite.of_injective
    (algebraMap (RatFunc k) F) (algebraMap (RatFunc k) F).injective
  let : Infinite (curvePlaceCompletion v) := Infinite.of_injective
    (algebraMap F (curvePlaceCompletion v)) (algebraMap F (curvePlaceCompletion v)).injective
  let : (Valued.v : Valuation (curvePlaceCompletion v) (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
  let := Valued.toNormedField (curvePlaceCompletion v) (WithZero (Multiplicative ℤ))
  infer_instance

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]

theorem numberField_finitePlaces_infinite : Infinite (FinitePlace K) := by
  let g (p : Nat.Primes) : HeightOneSpectrum ℤ := by
    let : Fact p.val.Prime := ⟨p.property⟩
    exact ⟨Ideal.span {(p.val : ℤ)}, inferInstance, by
      intro h
      exact p.property.ne_zero (Int.natCast_eq_zero.mp (Ideal.span_singleton_eq_bot.mp h))⟩
  have hg : Function.Injective g := by
    intro p q h
    have he := congrArg (fun r : HeightOneSpectrum ℤ => Ideal.absNorm r.asIdeal) h
    apply Subtype.ext
    simpa [g] using he
  let : Infinite (HeightOneSpectrum ℤ) := Infinite.of_injective g hg
  let f (p : FinitePlace K) : HeightOneSpectrum ℤ := p.under ℤ
  have hs : Function.Surjective f := by
    intro p
    obtain ⟨P, hP, hPe⟩ :=
      p.asIdeal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := NumberField.RingOfIntegers K) (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ _)]
        exact bot_le)
    have hn : P ≠ ⊥ := by
      intro he
      have := hPe
      rw [he, Ideal.under_bot] at this
      exact p.ne_bot this.symm
    exact ⟨⟨P, hP, hn⟩, by apply HeightOneSpectrum.ext; exact hPe⟩
  exact Infinite.of_surjective f hs

theorem finiteCompletion_noncompact (v : FinitePlace K) :
    NoncompactSpace (FiniteCompletion K v) := by
  let : Infinite (FiniteCompletion K v) := Infinite.of_injective
    (algebraMap K (FiniteCompletion K v)) (algebraMap K (FiniteCompletion K v)).injective
  infer_instance

end NumberField

end Langlands.Global
