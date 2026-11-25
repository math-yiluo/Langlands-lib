module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.OrbitExtension

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Eliminating degree-prime ramification: pole-order reduction

Artin--Schreier presentations of minimal pole order, the pole-reduction step by a translation,
the constant-numerator obstruction to divisibility of the pole order, and lifting and Laurent
expansions modulo powers of a uniformizer.
-/

@[expose] public section

open Polynomial
open nonZeroDivisors
open WithZero

open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra
attribute [local instance] Ideal.Quotient.field

universe uA uB uC uK uL uM uK₁

namespace IsDiscreteValuationRing

/-- For a finite subgroup `V` contained in an ideal `I`, the product `∏_{v ∈ V} (x - v)` agrees
with `x ^ |V|` modulo the extension of `I`. -/
private theorem prod_sub_algebraMap_sub_pow_mem_map {Base Extension : Type*} [CommRing Base]
    [CommRing Extension] [Algebra Base Extension]
    (translations : AddSubgroup Base) [Fintype translations]
    (ideal : Ideal Base) (contained : ∀ element : translations, (element : Base) ∈ ideal)
    (point : Extension) :
    ∏ element : translations, (point - algebraMap Base Extension element) -
        point ^ Fintype.card translations ∈ ideal.map (algebraMap Base Extension) := by
  classical
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_prod, map_pow]
  have vanishes : ∀ element : translations,
      Ideal.Quotient.mk (ideal.map (algebraMap Base Extension))
        (algebraMap Base Extension element) = 0 :=
    fun element => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ (contained element))
  simp only [map_sub, vanishes, sub_zero, Finset.prod_const, Finset.card_univ, sub_self]

/-- The uniformiser relation of the orbit extension: if `∏_{v ∈ V} (α - v) = π` with
`V ⊆ π ^ N A`, then `α ^ |V| ≡ π` modulo `π ^ N`. -/
private theorem pow_card_sub_mem_span_pow_of_prod_eq {Base Extension : Type*} [CommRing Base]
    [CommRing Extension] [Algebra Base Extension]
    (translations : AddSubgroup Base) [Fintype translations] (π : Base) (depth : ℕ)
    (contained : ∀ element : translations, (element : Base) ∈ Ideal.span {π ^ depth})
    (point : Extension)
    (equation : ∏ element : translations, (point - algebraMap Base Extension element) =
      algebraMap Base Extension π) :
    point ^ Fintype.card translations - algebraMap Base Extension π ∈
      Ideal.span {algebraMap Base Extension π ^ depth} := by
  have h := prod_sub_algebraMap_sub_pow_mem_map translations _ contained point
  rw [equation, Ideal.map_span, Set.image_singleton, map_pow] at h
  simpa [neg_sub] using (Ideal.span {algebraMap Base Extension π ^ depth}).neg_mem h

/-- Over a discrete valuation ring with uniformiser `π`, every element of the fraction field
becomes integral after multiplication by a power of `π`. -/
private theorem exists_pow_mul_mem_range {B L : Type*} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Field L] [Algebra B L] [IsFractionRing B L]
    {π : B} (hπ : Irreducible π) (ξ : L) :
    ∃ n : ℕ, algebraMap B L π ^ n * ξ ∈ (algebraMap B L).range := by
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors B) ξ
  simp only at hxy
  have hy0 : (y : B) ≠ 0 := nonZeroDivisors.coe_ne_zero y
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
  refine ⟨n, ↑u⁻¹ * x, ?_⟩
  have hunit : algebraMap B L ↑u * algebraMap B L ↑u⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [map_mul, ← hxy, hu, map_mul, map_pow]
  linear_combination (algebraMap B L π ^ n * ξ) * hunit

/-- Among all Artin--Schreier presentations `z ^ p - z = ξ` of `M / L`, one may choose one whose
pole order `n` (the least `n` with `π ^ n ξ ∈ B`) is minimal. -/
theorem exists_artinSchreier_presentation_minimal_poleOrder
    (B L M : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field L] [Field M] [Algebra B L] [IsFractionRing B L] [Algebra L M]
    (p : ℕ) {π : B} (hπ : Irreducible π)
    (hex : ∃ (ξ : L) (z : M), z ^ p - z = algebraMap L M ξ ∧ Algebra.adjoin L {z} = ⊤) :
    ∃ (n : ℕ) (ξ : L) (z : M), z ^ p - z = algebraMap L M ξ ∧ Algebra.adjoin L {z} = ⊤ ∧
      algebraMap B L π ^ n * ξ ∈ (algebraMap B L).range ∧
      ∀ (m : ℕ) (ξ' : L) (z' : M), z' ^ p - z' = algebraMap L M ξ' →
        Algebra.adjoin L {z'} = ⊤ → algebraMap B L π ^ m * ξ' ∈ (algebraMap B L).range →
          n ≤ m := by
  classical
  let P : ℕ → Prop := fun n => ∃ (ξ : L) (z : M), z ^ p - z = algebraMap L M ξ ∧
    Algebra.adjoin L {z} = ⊤ ∧ algebraMap B L π ^ n * ξ ∈ (algebraMap B L).range
  have hP : ∃ n, P n := by
    obtain ⟨ξ, z, hz, hgen⟩ := hex
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_range (L := L) hπ ξ
    exact ⟨n, ξ, z, hz, hgen, hn⟩
  obtain ⟨ξ, z, hz, hgen, hn⟩ := Nat.find_spec hP
  exact ⟨Nat.find hP, ξ, z, hz, hgen, hn, fun m ξ' z' hz' hgen' hm =>
    Nat.find_min' hP ⟨ξ', z', hz', hgen', hm⟩⟩

/-- Translating a generator by an element of the base ring does not change the subalgebra it
generates.

Public, and placed ahead of the pole reduction, because the reduction translates its generator by
`t ^ (-m) * a₀`: any caller tracking the reduction — in particular an induction down to a pole
order prime to `p`, as in
`StacksFrontier.RingTheory.DiscreteValuationRing.EppFrobeniusNumerator` — needs to know the
translated element still generates. `artinSchreier_sub_poleReduction_eq` returns that fact directly,
and this
is what proves it. -/
theorem adjoin_singleton_sub_algebraMap {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] (z : S) (c : R) :
    Algebra.adjoin R {z - algebraMap R S c} = Algebra.adjoin R {z} := by
  apply le_antisymm
  · refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    exact (Algebra.adjoin R {z}).sub_mem (Algebra.subset_adjoin rfl)
      ((Algebra.adjoin R {z}).algebraMap_mem c)
  · apply Algebra.adjoin_le
    apply Set.singleton_subset_iff.mpr
    change z ∈ Algebra.adjoin R {z - algebraMap R S c}
    simpa only [sub_add_cancel] using
      (Algebra.adjoin R {z - algebraMap R S c}).add_mem
        (Algebra.subset_adjoin (Set.mem_singleton _))
        ((Algebra.adjoin R {z - algebraMap R S c}).algebraMap_mem c)

/-- Elements of a discrete valuation ring with the same residue differ by a multiple of the
uniformizer. -/
private theorem exists_eq_add_uniformizer_mul_of_residue_eq {A : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} (hπ : Irreducible π) (a c : A)
    (h : IsLocalRing.residue A a = IsLocalRing.residue A c) :
    ∃ a₁ : A, a = c + π * a₁ := by
  have ha : a - c ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.residue_eq_zero_iff _).mp (by rw [map_sub, h, sub_self])
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
    Ideal.mem_span_singleton] at ha
  obtain ⟨a₁, ha₁⟩ := ha
  exact ⟨a₁, by linear_combination ha₁⟩

/-- Let `B` be a discrete valuation ring of characteristic `p` and let `N > 0`. The residue map
`B → κ(B)` has a set-theoretic section `σ` whose reduction modulo `𝔪 ^ N` is a ring homomorphism
`κ(B) →+* B ⧸ 𝔪 ^ N`. -/
theorem exists_residueField_lift_mod_pow {B : Type uB}
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (p : ℕ) [Fact p.Prime] [CharP B p] (N : ℕ) (hN : 0 < N) :
    ∃ σ : IsLocalRing.ResidueField B → B,
      (∀ x, IsLocalRing.residue B (σ x) = x) ∧
      ∃ s : IsLocalRing.ResidueField B →+* B ⧸ (IsLocalRing.maximalIdeal B)^N,
        ∀ x, Ideal.Quotient.mk _ (σ x) = s x := by
  let I := (IsLocalRing.maximalIdeal B)^N
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal B).ne_top
    (Ideal.pow_le_self (by omega))
  let Q := B ⧸ I
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing Q := IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mk I
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  let : CharP Q p := (CharP.charP_iff_prime_eq_zero (R := Q) (Fact.out : p.Prime)).mpr
    (by rw [← map_natCast q, CharP.cast_eq_zero B p, map_zero])
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal Q) := by
    refine ⟨N, ?_⟩
    rw [← IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective,
      ← Ideal.map_pow]
    exact Ideal.map_quotient_self I
  obtain ⟨sQ, hsQ, -⟩ :=
    IsLocalRing.exists_residueField_section_compatible.{uB, uB} (p := p) Q hnil
  let e := IsLocalRing.ResidueField.map q
  let s : IsLocalRing.ResidueField B →+* Q := sQ.comp e
  choose σ hσ using fun x => Ideal.Quotient.mk_surjective (s x)
  refine ⟨σ, ?_, s, hσ⟩
  intro x
  apply e.injective
  rw [IsLocalRing.ResidueField.map_residue]
  change IsLocalRing.residue Q (q (σ x)) = e x
  rw [hσ]
  exact DFunLike.congr_fun hsQ (e x)

private theorem exists_eq_sum_uniformizer_pow {B : Type*}
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {π : B} (hπ : Irreducible π)
    (σ : IsLocalRing.ResidueField B → B)
    (hσ : ∀ x, IsLocalRing.residue B (σ x) = x) (n : ℕ) (a : B) :
    ∃ (coeff : ℕ → IsLocalRing.ResidueField B) (b : B),
      a = (∑ i ∈ Finset.range n, σ (coeff i) * π ^ i) + π ^ n * b := by
  induction n generalizing a with
  | zero => exact ⟨fun _ => 0, a, by simp⟩
  | succ n ih =>
    obtain ⟨a₁, ha₁⟩ := exists_eq_add_uniformizer_mul_of_residue_eq hπ a
      (σ (IsLocalRing.residue B a)) (by rw [hσ])
    obtain ⟨coeff, b, hb⟩ := ih a₁
    refine ⟨fun i => Nat.casesOn i (IsLocalRing.residue B a) coeff, b, ?_⟩
    rw [Finset.sum_range_succ']
    simp only [pow_zero, mul_one, pow_succ]
    have hs : (∑ k ∈ Finset.range n, σ (coeff k) * (π ^ k * π)) =
        π * ∑ k ∈ Finset.range n, σ (coeff k) * π ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hs]
    linear_combination ha₁ + π * hb

/-- If `u` has the residue of an element of `κ_A`, then its `p ^ N`-th power is congruent modulo
`𝔪 ^ N` to the image of an element of `A`. -/
private theorem exists_pow_sub_algebraMap_mem_pow {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (p : ℕ) [Fact p.Prime] [CharP B p] (N : ℕ) (u : B) (r : IsLocalRing.ResidueField A)
    (hu : IsLocalRing.residue B u =
      algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) r) :
    ∃ a₀ : A, u ^ (p ^ N) - algebraMap A B a₀ ∈ (IsLocalRing.maximalIdeal B) ^ N := by
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective r
  have hd : u - algebraMap A B a₀ ∈ IsLocalRing.maximalIdeal B := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, hu, ← IsLocalRing.ResidueField.algebraMap_residue, sub_self]
  have hN : N ≤ p ^ N :=
    (Nat.le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left (Fact.out : p.Prime).two_le N)
  have hdN := (Ideal.pow_le_pow_right hN) (Ideal.pow_mem_pow hd (p ^ N))
  rw [sub_pow_char_pow] at hdN
  exact ⟨a₀ ^ (p ^ N), by simpa only [map_pow] using hdN⟩

/-- **Finite-support normalization through a residue overfield.**

Let `F` be a coefficient field whose elements have compatible lifts to the truncated target DVR
`B / ᵐ_B^N`.  Suppose a coefficient `a : F` has a `p ^ N`-th root `x : F`, and the image of
that root in `κ_B` is also the image of `rootBase : κ_A`.  Then the chosen lift of `a` agrees
modulo `ᵐ_B^N` with an element coming from `A`.

Unlike `exists_sub_algebraMap_mem_pow_of_pow_eq`, this does not require a section of the whole
residue field of `B`.  It only requires compatible truncated lifts of the original coefficient
field `F`.  This is the form needed after normal residue absorption: a conjugate factor contains
the transported coefficient field and the absorbed base residue field inside one residue
overfield, but its full residue field need not admit a coefficient section extending the original
one.

The proof uses both root incarnations.  Their equality in `κ_B` makes arbitrary ring lifts
congruent modulo the maximal ideal; raising that congruence to the `p ^ N`-th power promotes it to
one modulo `ᵐ_B^N`.  The truncated ring hom on `F` identifies the resulting power with the
chosen lift of `a`. -/
theorem exists_sub_algebraMap_mem_pow_of_pow_eq_over_residueField
    {A B F : Type*} [CommRing A] [CommRing B] [Field F]
    [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (p : ℕ) [Fact p.Prime] [CharP B p]
    (N : ℕ) (f : F →+* IsLocalRing.ResidueField B)
    (σ : F → B)
    (hσ : ∀ x, IsLocalRing.residue B (σ x) = f x)
    (s : F →+* B ⧸ (IsLocalRing.maximalIdeal B) ^ N)
    (hs : ∀ x, Ideal.Quotient.mk _ (σ x) = s x)
    (a x : F) (hx : x ^ (p ^ N) = a)
    (rootBase : IsLocalRing.ResidueField A)
    (hroot : algebraMap (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B) rootBase = f x) :
    ∃ a₀ : A, σ a - algebraMap A B a₀ ∈ (IsLocalRing.maximalIdeal B) ^ N := by
  obtain ⟨a₀, h⟩ := exists_pow_sub_algebraMap_mem_pow p N (σ x) rootBase ((hσ x).trans hroot.symm)
  refine ⟨a₀, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_sub, map_pow, hs, ← hx] using Ideal.Quotient.eq_zero_iff_mem.mpr h

/-- A finite residue expansion becomes a finite Laurent expansion in the fraction field. -/
theorem exists_laurent_expansion {B L : Type*}
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    {π : B} (hπ : Irreducible π)
    (σ : IsLocalRing.ResidueField B → B)
    (hσ : ∀ x, IsLocalRing.residue B (σ x) = x)
    (n : ℕ) (ξ : L) (hξ : algebraMap B L π ^ n * ξ ∈ (algebraMap B L).range) :
    ∃ (coeff : ℕ → IsLocalRing.ResidueField B) (b : B),
      ξ = (∑ i ∈ Finset.range n,
        algebraMap B L (σ (coeff i)) * (algebraMap B L π)⁻¹ ^ (n - i)) +
          algebraMap B L b := by
  obtain ⟨a, ha⟩ := hξ
  obtain ⟨coeff, b, hab⟩ := exists_eq_sum_uniformizer_pow hπ σ hσ n a
  refine ⟨coeff, b, ?_⟩
  have ht : algebraMap B L π ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B L).ne hπ.ne_zero
  apply (mul_left_cancel₀ (pow_ne_zero n ht))
  rw [mul_add, Finset.mul_sum, ← ha, hab, map_add, map_sum, map_mul, map_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, map_pow, inv_pow_sub₀ ht (Nat.le_of_lt (Finset.mem_range.mp hi))]
  field_simp

end IsDiscreteValuationRing
