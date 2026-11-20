import Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Powers of a spectrum with an induced Euler polynomial

If the Euler polynomial of an unordered spectrum `A` of nonzero complex numbers is the
product `∏ᵢ (1 - cᵢ X^{fᵢ})`, then for every common multiple `N` of the `fᵢ` the spectrum
of `N`-th powers of `A` consists of `fᵢ` copies of `cᵢ ^ (N / fᵢ)` for every `i`. The proof
compares the roots of both sides: the roots of `1 - c X^f` are the `f`-th roots of `c⁻¹`.
-/

noncomputable section

open Polynomial

set_option autoImplicit false

namespace Langlands.Unramified.Eigenvalues

/-- The roots of `1 - c X^f` are the `f`-th roots of `c⁻¹`. -/
theorem roots_one_sub_C_mul_X_pow {c : ℂ} (hc : c ≠ 0) (f : ℕ) :
    (1 - C c * X ^ f : ℂ[X]).roots = nthRoots f c⁻¹ := by
  have h1 : C (-c) * C c⁻¹ = (-1 : ℂ[X]) := by
    rw [← C_mul, neg_mul, mul_inv_cancel₀ hc, C_neg, C_1]
  have h : (1 - C c * X ^ f : ℂ[X]) = C (-c) * (X ^ f - C c⁻¹) := by
    rw [mul_sub, h1, C_neg]
    ring
  rw [h, roots_C_mul _ (neg_ne_zero.mpr hc)]
  rfl

/-- Over `ℂ`, a nonzero number has exactly `f` many `f`-th roots, counted with
multiplicity, and their `N`-th powers are all `a ^ (N / f)` when `f ∣ N`. -/
theorem map_pow_nthRoots {f : ℕ} (hf : 0 < f) {N : ℕ} (hdvd : f ∣ N) (a : ℂ) :
    (nthRoots f a).map (fun x => x ^ N) = Multiset.replicate f (a ^ (N / f)) := by
  classical
  rw [Multiset.eq_replicate]
  constructor
  · rw [Multiset.card_map, (Complex.isPrimitiveRoot_exp f hf.ne').card_nthRoots a]
    split_ifs with h
    · rfl
    · exact absurd (IsAlgClosed.exists_pow_nat_eq a hf) h
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hb
    rw [mem_nthRoots hf] at hx
    rw [← hx, ← pow_mul, Nat.mul_div_cancel' hdvd]

/-- If the Euler polynomial of `A` is `∏ᵢ (1 - cᵢ X^{fᵢ})` with `0 < fᵢ ∣ N`, then the
spectrum of `N`-th powers of `A` is the sum over `i` of `fᵢ` copies of `cᵢ ^ (N / fᵢ)`. -/
theorem coe_power_eq_sum_replicate {n : ℕ} (A : Eigenvalues n) {ι : Type*} [Fintype ι]
    (c : ι → ℂˣ) (f : ι → ℕ) (N : ℕ) (hf : ∀ i, 0 < f i) (hdvd : ∀ i, f i ∣ N)
    (h : A.eulerPolynomial = ∏ i, (1 - C (c i : ℂ) * X ^ f i)) :
    ((A.power N : Eigenvalues n) : Multiset ℂˣ) =
      ∑ i, Multiset.replicate (f i) (c i ^ (N / f i)) := by
  classical
  let g : ℂˣ → ℂ := fun z => ((z⁻¹ : ℂˣ) : ℂ)
  have hg : Function.Injective g := fun a b hab => inv_injective (Units.ext hab)
  apply Multiset.map_injective hg
  have hroots := congrArg Polynomial.roots h
  rw [eulerPolynomial_roots, roots_prod _ _ (by
    rw [← h]; exact eulerPolynomial_ne_zero A)] at hroots
  have hroots' : (A : Multiset ℂˣ).map g =
      ∑ i, nthRoots (f i) ((c i : ℂ))⁻¹ := by
    rw [hroots, Multiset.bind, Finset.sum_eq_multiset_sum, Multiset.join]
    congr 1
    exact Multiset.map_congr rfl fun i _ => roots_one_sub_C_mul_X_pow (c i).ne_zero (f i)
  have hmapsum : ∀ {α β : Type} (φ : α → β) (m : ι → Multiset α),
      Multiset.map φ (∑ i, m i) = ∑ i, Multiset.map φ (m i) := fun φ m =>
    map_sum (Multiset.mapAddMonoidHom φ) m Finset.univ
  calc Multiset.map g ((A.power N : Eigenvalues n) : Multiset ℂˣ)
      = Multiset.map (fun x : ℂ => x ^ N) (Multiset.map g (A : Multiset ℂˣ)) := by
        rw [power, Sym.coe_map, Multiset.map_map, Multiset.map_map]
        refine Multiset.map_congr rfl fun z _ => ?_
        simp [g, inv_pow]
    _ = ∑ i, Multiset.map (fun x : ℂ => x ^ N) (nthRoots (f i) ((c i : ℂ))⁻¹) := by
        rw [hroots', hmapsum]
    _ = ∑ i, Multiset.replicate (f i) (((c i : ℂ))⁻¹ ^ (N / f i)) :=
        Finset.sum_congr rfl fun i _ => map_pow_nthRoots (hf i) (hdvd i) _
    _ = Multiset.map g (∑ i, Multiset.replicate (f i) (c i ^ (N / f i))) := by
        rw [hmapsum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Multiset.map_replicate]
        simp [g, inv_pow]
