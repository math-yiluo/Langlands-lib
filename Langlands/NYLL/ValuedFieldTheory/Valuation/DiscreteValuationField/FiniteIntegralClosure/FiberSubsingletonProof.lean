/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 122 (2026-10-29): adapt M245.005 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 to its published closed target,
with independent universe parameters u, v, w and the Langlands.NYLL prefix.
Use the accepted mapped-base-ideal Henselianity theorem and Mathlib's actual
valuation-ring instances. Keep the needed M192 and M104 arguments private:
combine the fiber-map facts through the quotient equivalence, and inline the
idempotent polynomial calculations in the nontrivial-ring lifting argument.
Replace upstream imports by published dependencies and focused Mathlib imports.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.LocalnessStatements
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.CompletenessProofs
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Uniqueness of the finite integral-closure residue fiber

The only public theorem proves NYLL M245.005 as its exact published closed
proposition. The auxiliary fiber and idempotent arguments are private.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The Artinian spectrum is discrete, so a singleton is represented by an
idempotent; trivial idempotents force all its points to agree (M192.001). -/
private theorem spectrum_subsingleton_of_trivial_idempotents
    {R : Type*} [CommRing R] [IsArtinianRing R]
    (hidempotent : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Subsingleton (PrimeSpectrum R) := by
  constructor
  intro P Q
  by_contra hPQ
  have hclopen : IsClopen ({P} : Set (PrimeSpectrum R)) :=
    isClopen_discrete {P}
  obtain ⟨e, he, hopen⟩ :=
    PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hclopen
  rcases hidempotent e he with rfl | rfl
  · have hPmem : P ∈ (PrimeSpectrum.basicOpen (0 : R) : Set (PrimeSpectrum R)) := by
      rw [← hopen]
      exact Set.mem_singleton P
    rw [PrimeSpectrum.basicOpen_zero] at hPmem
    exact Set.notMem_empty P hPmem
  · have hQmem : Q ∈ ({P} : Set (PrimeSpectrum R)) := by
      rw [hopen, PrimeSpectrum.basicOpen_one]
      trivial
    exact hPQ hQmem.symm

/-- Identify the actual maximal-ideal fiber with the quotient by the extended
ideal, and compute the canonical map's surjectivity and kernel (M192.002/.003). -/
private theorem fiber_includeRight_facts
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S] :
    let f : S →+* (IsLocalRing.maximalIdeal R).Fiber S :=
      (Algebra.TensorProduct.includeRight :
        S →ₐ[R] (IsLocalRing.maximalIdeal R).Fiber S)
    Function.Surjective f ∧
      RingHom.ker f = (IsLocalRing.maximalIdeal R).map (algebraMap R S) := by
  intro f
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let e : (IsLocalRing.maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ I :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField
        (IsLocalRing.maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
      (IsLocalRing.maximalIdeal R)).symm.restrictScalars _)
  have he_apply (s : S) : e (f s) = Ideal.Quotient.mk I s := by
    simpa [e, I, f, Algebra.TensorProduct.includeRight_apply] using
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul
        (B := S) (I := IsLocalRing.maximalIdeal R) s (1 : R))
  constructor
  · intro x
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (e x)
    exact ⟨s, e.injective ((he_apply s).trans hs)⟩
  · ext s
    constructor
    · intro hs
      have hq : e (f s) = 0 := by
        simpa using congrArg e hs
      rw [he_apply s] at hq
      simpa [I, Ideal.Quotient.eq_zero_iff_mem] using hq
    · intro hs
      change f s = 0
      apply e.injective
      rw [he_apply s, map_zero]
      simpa [I, Ideal.Quotient.eq_zero_iff_mem] using hs

/-- Apply Hensel to `X^2-X`: at an idempotent the derivative is its own
inverse. This is the nontrivial-ring specialization of M104.001–.004. -/
private theorem lift_idempotent
    {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    [HenselianRing R (RingHom.ker f)] (e : S) (he : IsIdempotentElem e) :
    ∃ a : R, IsIdempotentElem a ∧ f a = e := by
  obtain ⟨a₀, ha₀⟩ := hf e
  let p : Polynomial R := Polynomial.X ^ 2 - Polynomial.X
  have hp : p.Monic := by
    exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num)
  have hq : IsIdempotentElem (Ideal.Quotient.mk (RingHom.ker f) a₀) := by
    rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq, RingHom.mem_ker]
    simp [ha₀, he.eq]
  have hroot : p.eval a₀ ∈ RingHom.ker f := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [p, pow_two] using sub_eq_zero.mpr hq.eq
  have hsimple : IsUnit
      (Ideal.Quotient.mk (RingHom.ker f) (p.derivative.eval a₀)) := by
    have hinv :
        Ideal.Quotient.mk (RingHom.ker f) (p.derivative.eval a₀) *
          Ideal.Quotient.mk (RingHom.ker f) (p.derivative.eval a₀) = 1 := by
      simp only [p, pow_two, Polynomial.derivative_mul, Polynomial.derivative_X,
        one_mul, mul_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_one, map_sub, map_add, map_one]
      calc
        (Ideal.Quotient.mk (RingHom.ker f) a₀ +
            Ideal.Quotient.mk (RingHom.ker f) a₀ - 1) *
          (Ideal.Quotient.mk (RingHom.ker f) a₀ +
            Ideal.Quotient.mk (RingHom.ker f) a₀ - 1) =
          1 + (4 * (Ideal.Quotient.mk (RingHom.ker f) a₀ *
            Ideal.Quotient.mk (RingHom.ker f) a₀) -
            4 * Ideal.Quotient.mk (RingHom.ker f) a₀) := by ring
        _ = 1 := by rw [hq.eq]; ring
    exact isUnit_iff_exists.mpr ⟨_, hinv, hinv⟩
  obtain ⟨a, ha, hcongr⟩ := HenselianRing.is_henselian p hp a₀ hroot hsimple
  refine ⟨a, ?_, ?_⟩
  · change a * a = a
    exact sub_eq_zero.mp (by simpa [p, pow_two] using ha)
  · have hsub : f (a - a₀) = 0 := RingHom.mem_ker.mp hcongr
    rw [map_sub, ha₀, sub_eq_zero] at hsub
    exact hsub

/-- The actual integral closure in a finite separable extension of a complete
DVF has at most one prime in its fiber over the base maximal ideal (M245.005). -/
theorem integralClosure_base_maximal_fiber_subsingleton_of_finite_separable.{u, v, w} :
    IntegralClosureBaseMaximalFiberSubsingletonOfFiniteSeparableStatement.{u, v, w} := by
  intro K L _ _ _ _ base _
  let A := base.valuation.valuationSubring
  let B := integralClosure A L
  have : IsNoetherianRing A := inferInstance
  have : IsFractionRing A K := inferInstance
  have : IsIntegrallyClosed A := inferInstance
  have : Module.Finite A B := IsIntegralClosure.finite A K L B
  have : Algebra.QuasiFinite A B := inferInstance
  have : IsArtinianRing ((IsLocalRing.maximalIdeal A).Fiber B) := inferInstance
  refine spectrum_subsingleton_of_trivial_idempotents ?_
  intro e he
  have : HenselianRing B ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) :=
    integralClosure_henselianRing_of_finite_separable.{u, v, w} K L base
  let f : B →+* (IsLocalRing.maximalIdeal A).Fiber B :=
    (Algebra.TensorProduct.includeRight :
      B →ₐ[A] (IsLocalRing.maximalIdeal A).Fiber B)
  obtain ⟨hsurj, hker⟩ := fiber_includeRight_facts (R := A) (S := B)
  have : HenselianRing B (RingHom.ker f) := by
    rw [hker]
    infer_instance
  obtain ⟨b, hb, hbmap⟩ := lift_idempotent f hsurj e he
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hb with rfl | rfl
  · exact Or.inl (hbmap.symm.trans f.map_zero)
  · exact Or.inr (hbmap.symm.trans f.map_one)

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
