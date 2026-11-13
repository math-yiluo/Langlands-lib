import Langlands.Algebra.UnitaryInvolutionNorm
import Langlands.Algebra.LocalDivisionConjugationResidue
import Mathlib.FieldTheory.Finite.Basic

/-!
# Unitary involutions on local division algebras: residue action and degree bound
-/

noncomputable section

namespace Langlands.UnitaryInvolution

universe u

/-- Any two ring endomorphisms of a finite field commute: its automorphism group is cyclic. -/
theorem finiteField_ringHom_comm {F : Type*} [Field F] [Finite F] (f g : F →+* F) (x : F) :
    f (g x) = g (f x) := by
  obtain ⟨p, hp⟩ := CharP.exists F
  have hprime : p.Prime := CharP.char_is_prime F p
  have := Fact.mk hprime
  let := ZMod.algebra F p
  have hbij : ∀ h : F →+* F, Function.Bijective h :=
    fun h => Finite.injective_iff_bijective.mp h.injective
  let toAlg : (F →+* F) → (F ≃ₐ[ZMod p] F) := fun h =>
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective h (hbij h)) (fun c => by
      change h (algebraMap (ZMod p) F c) = algebraMap (ZMod p) F c
      exact congrFun (congrArg DFunLike.coe
        (RingHom.ext_zmod (h.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F))) c)
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := F ≃ₐ[ZMod p] F)
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hγ (toAlg f))
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hγ (toAlg g))
  have hc : toAlg f * toAlg g = toAlg g * toAlg f := by
    rw [← ha, ← hb]
    exact Commute.zpow_zpow_self γ a b
  exact congrArg (fun e : F ≃ₐ[ZMod p] F => e x) hc

/-- In a finite field, an involutive ring endomorphism is the identity or equals any given
nontrivial involutive ring endomorphism: the automorphism group is cyclic. -/
theorem finiteField_involution_eq {F : Type*} [Field F] [Finite F] (ψ t : F →+* F)
    (hψ : ∀ x, ψ (ψ x) = x) (ht : ∀ x, t (t x) = x) (hψ1 : ∃ x, ψ x ≠ x) :
    (∀ x, t x = x) ∨ (∀ x, t x = ψ x) := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists F
  have hprime : p.Prime := CharP.char_is_prime F p
  have := Fact.mk hprime
  let := ZMod.algebra F p
  have hbij : ∀ h : F →+* F, Function.Bijective h :=
    fun h => Finite.injective_iff_bijective.mp h.injective
  let toAlg : (F →+* F) → (F ≃ₐ[ZMod p] F) := fun h =>
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective h (hbij h)) (fun c => by
      change h (algebraMap (ZMod p) F c) = algebraMap (ZMod p) F c
      exact congrFun (congrArg DFunLike.coe
        (RingHom.ext_zmod (h.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F))) c)
  have htoAlg : ∀ h x, toAlg h x = h x := fun _ _ => rfl
  have : Finite (F ≃ₐ[ZMod p] F) :=
    Finite.of_injective (fun e : F ≃ₐ[ZMod p] F => (e : F → F)) DFunLike.coe_injective
  let := Fintype.ofFinite (F ≃ₐ[ZMod p] F)
  have hsq : ∀ h : F →+* F, (∀ x, h (h x) = x) → toAlg h ^ 2 = 1 := by
    intro h hh
    ext x
    rw [pow_two, AlgEquiv.mul_apply, htoAlg, htoAlg, hh, AlgEquiv.one_apply]
  have hcard := IsCyclic.card_pow_eq_one_le (α := F ≃ₐ[ZMod p] F) (n := 2) (by norm_num)
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hcon
  obtain ⟨c, hc⟩ := hψ1
  have h1 : toAlg ψ ≠ 1 := fun h => hc (by rw [← htoAlg, h, AlgEquiv.one_apply])
  have h2 : toAlg t ≠ 1 := fun h => ha (by rw [← htoAlg, h, AlgEquiv.one_apply])
  have h3 : toAlg t ≠ toAlg ψ := fun h => hb (by rw [← htoAlg, h, htoAlg])
  have hsub : ({1, toAlg ψ, toAlg t} : Finset (F ≃ₐ[ZMod p] F)) ⊆
      Finset.univ.filter (fun g => g ^ 2 = 1) := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hg with rfl | rfl | rfl
    · exact one_pow 2
    · exact hsq ψ hψ
    · exact hsq t ht
  have h3card : ({1, toAlg ψ, toAlg t} : Finset (F ≃ₐ[ZMod p] F)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair h3.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1.symm, h2.symm⟩
  have := Finset.card_le_card hsub
  omega

section Local

open Langlands.CentralDivision Langlands.DivisionValuation ValuativeRel

variable {L D : Type u} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [DivisionRing D] [Algebra L D] [FiniteDimensional L D]
  [Algebra.IsCentral L D] {σ : L →+* L} {τ : D → D}

local instance : Field (Residue (localReducedNormValuation L D)) :=
  localDivisionResidueField L D

variable (hσ : ∀ c, valuation L (σ c) = valuation L c) (hτ : IsUnitaryInvolution (⇑σ) τ)
include hσ hτ

/-- A unitary involution preserves the canonical valuation. -/
theorem valuation_tau (x : D) :
    localReducedNormValuation L D (τ x) = localReducedNormValuation L D x := by
  have h1 := valuation_regularNorm_eq_localReducedNormValuation_pow L D (τ x)
  have h2 := valuation_regularNorm_eq_localReducedNormValuation_pow L D x
  rw [norm_tau hτ, hσ, h2] at h1
  exact ((pow_left_inj₀ zero_le zero_le (CentralSimple.reducedDegree_pos L D).ne').mp h1).symm

/-- The involution on the integer subring. -/
def tauInteger (x : (localReducedNormValuation L D).integer) :
    (localReducedNormValuation L D).integer :=
  ⟨τ x, by
    change localReducedNormValuation L D (τ x) ≤ 1
    rw [valuation_tau hσ hτ]
    exact x.prop⟩

@[simp] theorem tauInteger_coe (x : (localReducedNormValuation L D).integer) :
    (tauInteger hσ hτ x : D) = τ x := rfl

/-- Reduction after the involution, a ring map since the residue ring is commutative. -/
def tauReductionHom :
    (localReducedNormValuation L D).integer →+* Residue (localReducedNormValuation L D) where
  toFun x := reduction _ (tauInteger hσ hτ x)
  map_one' := by
    rw [← map_one (reduction (localReducedNormValuation L D))]
    congr 1
    exact Subtype.ext (tau_one hτ)
  map_mul' x y := by
    have h : tauInteger hσ hτ (x * y) = tauInteger hσ hτ y * tauInteger hσ hτ x :=
      Subtype.ext (tau_mul hτ x y)
    rw [h, map_mul, mul_comm]
  map_zero' := by
    rw [← map_zero (reduction (localReducedNormValuation L D))]
    congr 1
    exact Subtype.ext (tau_zero hτ)
  map_add' x y := by
    have h : tauInteger hσ hτ (x + y) = tauInteger hσ hτ x + tauInteger hσ hτ y :=
      Subtype.ext (hτ.1 x y)
    rw [h, map_add]

/-- The involution induced on the residue field. -/
def tauResidue :
    Residue (localReducedNormValuation L D) →+* Residue (localReducedNormValuation L D) :=
  Ideal.Quotient.lift (strictIdeal _) (tauReductionHom hσ hτ) (fun x hx => by
    apply (reduction_eq_zero_iff _ _).mpr
    change localReducedNormValuation L D (τ x) < 1
    rw [valuation_tau hσ hτ]
    exact hx)

@[simp] theorem tauResidue_reduction (x : (localReducedNormValuation L D).integer) :
    tauResidue hσ hτ (reduction _ x) = reduction _ (tauInteger hσ hτ x) := rfl

theorem tauResidue_tauResidue (r : Residue (localReducedNormValuation L D)) :
    tauResidue hσ hτ (tauResidue hσ hτ r) = r := by
  obtain ⟨x, rfl⟩ := reduction_surjective _ r
  rw [tauResidue_reduction, tauResidue_reduction]
  congr 1
  exact Subtype.ext (tau_tau hτ x)

theorem tauResidue_conj (j : Dˣ) (r : Residue (localReducedNormValuation L D)) :
    conjResidue _ (tauUnit hτ j) (tauResidue hσ hτ (conjResidue _ j r)) =
      tauResidue hσ hτ r := by
  obtain ⟨x, rfl⟩ := reduction_surjective _ r
  rw [conjResidue_reduction, tauResidue_reduction, conjResidue_reduction,
    tauResidue_reduction]
  congr 1
  apply Subtype.ext
  simp only [conjInteger_coe, tauInteger_coe, Units.val_inv_eq_inv_val]
  rw [tau_mul hτ, tau_mul hτ, tau_inv hτ]
  have hj : τ (j : D) ≠ 0 := (tauUnit hτ j).ne_zero
  change τ j * ((τ j)⁻¹ * (τ x * τ j)) * (τ j)⁻¹ = τ x
  rw [mul_inv_cancel_left₀ hj, mul_inv_cancel_right₀ hj]

/-- Conjugation by any unit acts on the residue field as an involution. -/
theorem conjResidue_conjResidue (j : Dˣ) (s : Residue (localReducedNormValuation L D)) :
    conjResidue _ j (conjResidue _ j s) = s := by
  let v := localReducedNormValuation L D
  let ψ := conjResidue v j
  let t := tauResidue hσ hτ
  have hcomm : ∀ a b : Residue v, a * b = b * a := localDivisionResidue_mul_comm L D
  have : Finite (Residue v) := localDivisionResidue_finite L D
  have h2 : ∀ s, conjResidue v (tauUnit hτ j) s = ψ s := fun s =>
    conjResidue_eq_of_value_eq v hcomm j (tauUnit hτ j) (valuation_tau hσ hτ j).symm s
  have h1 : ∀ s, ψ (t (ψ s)) = t s := fun s => by
    rw [← h2]
    exact tauResidue_conj hσ hτ j s
  have h5 := h1 (t s)
  rw [finiteField_ringHom_comm t ψ (t s)] at h5
  have h6 : t (t s) = s := tauResidue_tauResidue hσ hτ s
  rw [h6] at h5
  exact h5

/-- **Part I.** The reduced degree of a central division algebra over a local field with a
unitary involution divides two. -/
theorem reducedDegree_dvd_two : CentralSimple.reducedDegree L D ∣ 2 := by
  obtain ⟨u, hu⟩ := exists_unit_conjResidue_faithful L D
  apply hu 2
  intro r
  rw [conjResidue_pow]
  exact conjResidue_conjResidue hσ hτ u r

/-- **Unramified case.** If some integral element of `L` is moved by `σ` modulo the maximal
ideal, then `D` does not have reduced degree `2`. -/
theorem false_of_residue_moved (hd : CentralSimple.reducedDegree L D = 2) (θ : L)
    (hθ1 : valuation L θ ≤ 1) (hθ2 : valuation L (σ θ - θ) = 1) : False := by
  let v := localReducedNormValuation L D
  have : Finite (Residue v) := localDivisionResidue_finite L D
  obtain ⟨u, hu⟩ := exists_unit_conjResidue_faithful L D
  have hψ1 : ∃ r, conjResidue v u r ≠ r := by
    by_contra h
    push Not at h
    have := hu 1 (by simpa using h)
    rw [hd] at this
    norm_num at this
  have hval : ∀ c : L, v (algebraMap L D c) = valuation L c ^ 2 := fun c => by
    rw [localReducedNormValuation_algebraMap, hd]
  let xI : v.integer := ⟨algebraMap L D θ, by
    change v (algebraMap L D θ) ≤ 1
    rw [hval]
    exact pow_le_one₀ zero_le hθ1⟩
  rcases finiteField_involution_eq (conjResidue v u) (tauResidue hσ hτ)
      (conjResidue_conjResidue hσ hτ u) (tauResidue_tauResidue hσ hτ) hψ1 with h | h
  · have h' := h (reduction v xI)
    rw [tauResidue_reduction, reduction_eq_iff] at h'
    change v (τ (algebraMap L D θ) - algebraMap L D θ) < 1 at h'
    rw [tau_algebraMap hτ, ← map_sub, hval, hθ2, one_pow] at h'
    exact lt_irrefl _ h'
  · have h' := h (reduction v xI)
    have hfixψ : conjResidue v u (reduction v xI) = reduction v xI := by
      rw [conjResidue_reduction]
      congr 1
      apply Subtype.ext
      rw [conjInteger_coe]
      change (u : D) * algebraMap L D θ * ((u⁻¹ : Dˣ) : D) = algebraMap L D θ
      rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]
    rw [hfixψ, tauResidue_reduction, reduction_eq_iff] at h'
    change v (τ (algebraMap L D θ) - algebraMap L D θ) < 1 at h'
    rw [tau_algebraMap hτ, ← map_sub, hval, hθ2, one_pow] at h'
    exact lt_irrefl _ h'

end Local

end Langlands.UnitaryInvolution
