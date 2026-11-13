/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: prove the published closed target of M161.035,
the theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation
at lines 780–792 of upstream commit fbd320cd8b1b06487c58227e92eb135794267709,
under the same name prefixed with Langlands.NYLL. The source proof, which
combines the source's M161.033 injectivity and M161.034 surjectivity theorems, is
replaced by a new proof through Mathlib's ramification theory: injectivity from
the published kernel characterization and Mathlib's equality of the inertia
group's cardinality with the ramification index, surjectivity from Mathlib's
`Ideal.Quotient.stabilizerHom_surjective`. The source imports are replaced by
three Mathlib modules and two published modules. The retained license and
notices are in licenses/NYLL/.
-/

import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.IsGaloisGroup.Basic
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueBijectiveStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.KernelProofs

/-!
# Bijectivity of the residue action of an unramified extension: proof

This module proves the published closed target for NYLL M161.035.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- For a finite Galois extension of nonarchimedean local fields that is unramified
at the maximal ideals, the residue action `Gal(L/K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])` is
bijective. This proves the closed target for NYLL M161.035. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation :
    galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuationStatement.{u} := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have happly := galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L
  let φ : Gal(L/K) →* (𝒪[L] ≃+* 𝒪[L]) :=
    { toFun := galoisGroupIntegerRingEquivOfIsIntegralClosure K L
      map_one' := RingEquiv.ext fun x => Subtype.ext (by
        rw [happly]; rfl)
      map_mul' := fun σ τ => RingEquiv.ext fun x => Subtype.ext (by
        change ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L (σ * τ) x : 𝒪[L]) : L) =
          ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
            (galoisGroupIntegerRingEquivOfIsIntegralClosure K L τ x) : 𝒪[L]) : L)
        rw [happly, happly, happly]
        rfl) }
  let _ : MulSemiringAction Gal(L/K) 𝒪[L] := MulSemiringAction.compHom 𝒪[L] φ
  have hsmul : ∀ (σ : Gal(L/K)) (x : 𝒪[L]), ((σ • x : 𝒪[L]) : L) = σ (x : L) :=
    fun σ x => happly σ x
  have : SMulCommClass Gal(L/K) 𝒪[K] 𝒪[L] := ⟨fun σ a x => Subtype.ext (by
    rw [hsmul, Algebra.smul_def, Algebra.smul_def]
    change σ ((algebraMap K L a) * (x : L)) = algebraMap K L a * ((σ • x : 𝒪[L]) : L)
    rw [map_mul, AlgEquiv.commutes, hsmul])⟩
  have : SMulDistribClass Gal(L/K) 𝒪[L] L := ⟨fun σ r s => by
    change σ ((r : L) * s) = ((σ • r : 𝒪[L]) : L) * σ s
    rw [map_mul, hsmul]⟩
  have : Algebra.IsIntegral 𝒪[K] 𝒪[L] := IsIntegralClosure.isIntegral_algebra 𝒪[K] L
  have hG : IsGaloisGroup Gal(L/K) 𝒪[K] 𝒪[L] :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) 𝒪[K] 𝒪[L] K L
  have : Finite (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K])) := (inferInstance : Finite 𝓀[K])
  have : Finite (IsLocalRing.maximalIdeal 𝒪[K]).ResidueField :=
    Finite.of_surjective _
      (IsLocalRing.maximalIdeal 𝒪[K]).bijective_algebraMap_quotient_residueField.2
  refine ⟨?_, ?_⟩
  · -- injectivity: the kernel lies in the inertia group of `𝓂[L]`, which is trivial
    refine (injective_iff_map_eq_one _).2 fun σ hσ => ?_
    have hmem : σ ∈ (𝓂[L] : Ideal 𝒪[L]).inertia Gal(L/K) := fun x =>
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal
        K L σ).1 hσ x
    have hcard : Nat.card ((𝓂[L] : Ideal 𝒪[L]).inertia Gal(L/K)) = 1 := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K))
          (IsLocalRing.maximalIdeal 𝒪[K]) (IsLocalRing.maximalIdeal 𝒪[L]),
        Ideal.ramificationIdxIn_eq_ramificationIdx (IsLocalRing.maximalIdeal 𝒪[K])
          (IsLocalRing.maximalIdeal 𝒪[L]) Gal(L/K)]
      exact IsNonarchimedeanLocalField.IsUnramifiedValuedExtension.maximalIdeal_ramificationIdx_eq_one
    have hbot := Subgroup.card_eq_one.mp hcard
    rw [hbot] at hmem
    exact (Subgroup.mem_bot.mp hmem)
  · -- surjectivity: Mathlib's surjectivity of the decomposition-group action
    intro τ
    let τ' : (𝒪[L] ⧸ (𝓂[L] : Ideal 𝒪[L])) ≃ₐ[𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K])]
        (𝒪[L] ⧸ (𝓂[L] : Ideal 𝒪[L])) :=
      { (τ.toRingEquiv : (𝒪[L] ⧸ (𝓂[L] : Ideal 𝒪[L])) ≃+* (𝒪[L] ⧸ (𝓂[L] : Ideal 𝒪[L]))) with
        commutes' := fun r => by
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
          exact τ.commutes (IsLocalRing.residue 𝒪[K] a) }
    obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective Gal(L/K)
      (IsLocalRing.maximalIdeal 𝒪[K]) (IsLocalRing.maximalIdeal 𝒪[L]) τ'
    refine ⟨g, AlgEquiv.ext fun y => ?_⟩
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    have h1 := congrArg (fun f => f (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[L]) a)) hg
    simp only [Ideal.Quotient.stabilizerHom_apply] at h1
    change galoisGroupResidueFieldEquivOfIsIntegralClosure K L g (IsLocalRing.residue 𝒪[L] a) =
      τ (IsLocalRing.residue 𝒪[L] a)
    rw [galoisGroupResidueFieldEquivOfIsIntegralClosure_residue]
    exact h1

end Langlands.NYLL.LocalFieldTheory
