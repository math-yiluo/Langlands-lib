import Langlands.Analysis.Meromorphic.ShiftAnnihilation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ExponentDirectSum

/-! # Meromorphic propagation of moving generalized exponent support -/

universe u v

open Set
open scoped Manifold BigOperators

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Langlands.HarishChandraSchwartz

section Algebra

variable {A : Type u} [CommGroup A] {X : Type v}

private abbrev FunctionEnd := Module.End ℂ (X → ℂ)

private def shiftEnd (T : A →* FunctionEnd (X := X)) (a : A) (c : ℂ) : FunctionEnd (X := X) :=
  T a - c • 1

private theorem product_kills_of_mem (l : List (FunctionEnd (X := X)))
    {f : FunctionEnd (X := X)} {y : X → ℂ}
    (hcomm : ∀ g ∈ l, Commute f g) (hf : f ∈ l) (hzero : f y = 0) :
    l.prod y = 0 := by
  induction l with
  | nil => simp at hf
  | cons g l ih =>
    rcases List.mem_cons.mp hf with rfl | hf'
    · have hc := Commute.list_prod_right l f fun h hh => hcomm h (List.mem_cons_of_mem _ hh)
      rw [List.prod_cons, hc.eq, Module.End.mul_apply, hzero, map_zero]
    · rw [List.prod_cons, Module.End.mul_apply,
        ih (fun h hh => hcomm h (List.mem_cons_of_mem _ hh)) hf', map_zero]

private theorem shiftEnd_mem_joint (T : A →* FunctionEnd (X := X))
    (a : A) (c : ℂ) {χ : A → ℂ} {y : X → ℂ} (hy : y ∈ jointGenEigenspace T χ) :
    shiftEnd T a c y ∈ jointGenEigenspace T χ :=
  (jointGenEigenspace T χ).sub_mem (apply_mem_jointGenEigenspace T a hy)
    ((jointGenEigenspace T χ).smul_mem c hy)

private theorem shiftEnd_pow_injective_zero (T : A →* FunctionEnd (X := X))
    (a : A) (c : ℂ) {χ : A → ℂ} (hne : χ a ≠ c) (k : ℕ)
    {y : X → ℂ} (hy : y ∈ jointGenEigenspace T χ)
    (hzero : (shiftEnd T a c ^ k) y = 0) : y = 0 := by
  induction k generalizing y with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hzero
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply] at hzero
    have h := ih (shiftEnd_mem_joint T a c hy) hzero
    change T a y - c • y = 0 at h
    by_contra hy0
    obtain ⟨d, hd⟩ := mem_jointGenEigenspace.mp hy a
    exact hne (eq_of_apply_eq_smul_of_pow (T a) hy0 (sub_eq_zero.mp h) hd).symm

private theorem product_powers_commutes (T : A →* FunctionEnd (X := X))
    {I : Type*} (a : I → A) (c : I → ℂ) (k : ℕ) (l : List I) (b : A) :
    Commute (T b) (l.map (fun i => shiftEnd T (a i) (c i) ^ k)).prod := by
  apply Commute.list_prod_right
  intro f hf
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
  exact ((commute_jointFamily T b (a i)).sub_right
    ((Commute.one_right (T b)).smul_right (c i))).pow_right k

private theorem product_powers_injective_zero (T : A →* FunctionEnd (X := X))
    {I : Type*} (a : I → A) (c : I → ℂ) (k : ℕ) (l : List I)
    {χ : A → ℂ} (hne : ∀ i, χ (a i) ≠ c i)
    {y : X → ℂ} (hy : y ∈ jointGenEigenspace T χ)
    (hzero : (l.map (fun i => shiftEnd T (a i) (c i) ^ k)).prod y = 0) :
    y = 0 := by
  induction l with
  | nil => simpa only [List.map_nil, List.prod_nil, Module.End.one_apply] using hzero
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply] at hzero
    apply ih
    exact shiftEnd_pow_injective_zero T (a i) (c i) (hne i) k
      (mapsTo_jointGenEigenspace_of_commute T (product_powers_commutes T a c k l) χ hy) hzero

end Algebra

section ShiftEvaluation

variable {A : Type u} [CommGroup A] {X : Type v} {E I : Type*}
  (T : A →* FunctionEnd (X := X)) (shift : A → X → X)
  (hshift : ∀ a (y : X → ℂ) x, (T a) y x = y (shift a x))

include hshift

private theorem applyShiftFactors_eq_endProduct (l : List (A × (E → ℂ)))
    (φ : E → X → ℂ) (z : E) :
    applyShiftFactors (l.map (fun q => (shift q.1, q.2))) φ z =
      (l.map (fun q => shiftEnd T q.1 (q.2 z))).prod (φ z) := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    funext x
    change applyShiftFactors (l.map (fun q => (shift q.1, q.2))) φ z (shift q.1 x) -
      q.2 z * applyShiftFactors (l.map (fun q => (shift q.1, q.2))) φ z x = _
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [ih]
    simp only [shiftEnd, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hshift]

private theorem applyPoweredShiftFactors_eq_product (a : I → A) (c : I → E → ℂ)
    (l : List I) (k : ℕ) (φ : E → X → ℂ) (z : E) :
    applyShiftFactors ((l.flatMap fun i => List.replicate k (a i, c i)).map
      (fun q => (shift q.1, q.2))) φ z =
      (l.map (fun i => shiftEnd T (a i) (c i z) ^ k)).prod (φ z) := by
  rw [applyShiftFactors_eq_endProduct T shift hshift]
  congr 1
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.flatMap_cons, List.map_append, List.prod_append, List.map_replicate,
      List.prod_replicate, List.map_cons, List.prod_cons, ih]

end ShiftEvaluation

/-- A finite list of moving joint generalized exponents supports a meromorphic
family throughout its common holomorphy domain if it supports the family
on a nonempty open patch. The conclusion excludes unwanted components in any
supplied finite generalized exponent decomposition at a continued parameter. -/
def MeromorphicExponentSupportStatement : Prop :=
  ∀ (n : ℕ) (A : Type u) [CommGroup A] (X : Type v) (D W : Set (Fin n → ℂ))
    (T : A →* Module.End ℂ (X → ℂ)) (shift : A → X → X),
    (∀ a (y : X → ℂ) x, (T a) y x = y (shift a x)) →
    ∀ (m : ℕ) (χ : Fin m → (Fin n → ℂ) → A → ℂ) (φ : (Fin n → ℂ) → X → ℂ),
    IsOpen D → Dense D → IsOpen W → W.Nonempty →
    (∀ x, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun z => φ z x) D) →
    (∀ i a, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun z => χ i z a) D) →
    (∀ z ∈ W, ∃ v : Fin m → X → ℂ,
      (∀ i, v i ∈ jointGenEigenspace T (χ i z)) ∧ φ z = ∑ i, v i) →
    ∀ z ∈ D, ∀ (s : Finset (A → ℂ)) (v : (A → ℂ) → X → ℂ),
      (∀ δ ∈ s, v δ ∈ jointGenEigenspace T δ) →
      (∑ δ ∈ s, v δ) = φ z →
      ∀ δ ∈ s, (∀ i, δ ≠ χ i z) → v δ = 0

theorem meromorphicExponentSupport : MeromorphicExponentSupportStatement.{u, v} := by
  classical
  intro n A _ X D W T shift hshift m χ φ hoD hdD hoW hnW hφ hc hW z hz s v hv hsum δ hδ hne
  choose a ha using fun i => Function.ne_iff.mp (hne i)
  let c (i : Fin m) (t : Fin n → ℂ) := χ i t (a i)
  let l : List (Fin m) := List.ofFn id
  let factors (k : ℕ) := (l.flatMap fun i => List.replicate k (a i, c i)).map
    (fun q => (shift q.1, q.2))
  let P (k : ℕ) (t : Fin n → ℂ) := (l.map (fun i => shiftEnd T (a i) (c i t) ^ k)).prod
  have happly (k : ℕ) (t : Fin n → ℂ) :
      applyShiftFactors (factors k) φ t = P k t (φ t) :=
    applyPoweredShiftFactors_eq_product T shift hshift a c l k φ t
  have hmer (k : ℕ) (factor : (X → X) × ((Fin n → ℂ) → ℂ)) (hf : factor ∈ factors k) :
      IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) factor.2 D := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hf
    obtain ⟨i, _, hqi⟩ := List.mem_flatMap.mp hq
    have hq' := (List.mem_replicate.mp hqi).2
    rw [hq']
    exact hc i (a i)
  have hseed (t : Fin n → ℂ) (ht : t ∈ W) :
      ∃ k, applyShiftFactors (factors k) φ t = 0 := by
    obtain ⟨w, hw, hφt⟩ := hW t ht
    choose d hd using fun i => mem_jointGenEigenspace.mp (hw i) (a i)
    let k := ∑ i, d i
    refine ⟨k, ?_⟩
    rw [happly, hφt, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    apply product_kills_of_mem (l.map fun j => shiftEnd T (a j) (c j t) ^ k)
      (f := shiftEnd T (a i) (c i t) ^ k)
    · intro f hf
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf
      exact (commute_jointFamily_sub_smul T (a i) (a j) (c i t) (c j t)).pow_pow k k
    · exact List.mem_map_of_mem (by simp only [l, List.mem_ofFn]; exact ⟨i, rfl⟩)
    · have hle : d i ≤ k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      calc
        (shiftEnd T (a i) (c i t) ^ k) (w i) =
            (shiftEnd T (a i) (c i t) ^ (k - d i + d i)) (w i) := by rw [Nat.sub_add_cancel hle]
        _ = 0 := by
          rw [pow_add, Module.End.mul_apply]
          have hdi : (shiftEnd T (a i) (c i t) ^ d i) (w i) = 0 := hd i
          rw [hdi, map_zero]
  obtain ⟨k, hk⟩ := meromorphicShiftAnnihilation n X D W φ factors hoD hdD hoW hnW hφ hmer hseed
  have hkill := hk z hz
  rw [happly, ← hsum, map_sum] at hkill
  have hterms (δ' : A → ℂ) (hδ' : δ' ∈ s) :
      P k z (v δ') ∈ jointGenEigenspace T δ' :=
    mapsTo_jointGenEigenspace_of_commute T (product_powers_commutes T a (fun i => c i z) k l)
      δ' (hv δ' hδ')
  have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
    (iSupIndep_jointGenEigenspace T) s (fun δ' => P k z (v δ')) hterms hkill δ hδ
  exact product_powers_injective_zero T a (fun i => c i z) k l ha (hv δ hδ) hzero

end Langlands.Analysis.Meromorphic
