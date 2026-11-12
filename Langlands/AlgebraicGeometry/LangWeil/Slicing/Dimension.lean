import Langlands.AlgebraicGeometry.SchemePureDimensionAffine
import Langlands.AnthropicFLT.Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Dimension of hypersurface sections of irreducible affine schemes

For a ring `T` whose nilradical is prime (an irreducible affine scheme), killing an ideal not
contained in the nilradical lowers the Krull dimension by at least one, and, when `T` is of
finite type over a field, killing one element lowers it by at most one (Krull's principal ideal
theorem together with the dimension formula for affine domains). A ring with prime nilradical
has pure dimension equal to its Krull dimension.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil.Slicing

open SchemeFiberGeometry

variable {T : Type*} [CommRing T]

/-- Reducing modulo the nilradical does not change the Krull dimension. -/
theorem ringKrullDim_quotient_nilradical :
    ringKrullDim (T ⧸ nilradical T) = ringKrullDim T := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have hsurj : ∀ x : T ⧸ nilradical T, ∃ n > 0, x ^ n ∈ (Ideal.Quotient.mk _).range := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨1, one_pos, by rw [pow_one]; exact ⟨y, rfl⟩⟩
  exact IsHomeomorph.topologicalKrullDim_eq _
    (PrimeSpectrum.isHomeomorph_comap (Ideal.Quotient.mk (nilradical T)) hsurj
      (Ideal.mk_ker).le)

set_option backward.isDefEq.respectTransparency false in
/-- In a ring with prime nilradical, killing an ideal not contained in the nilradical lowers the
Krull dimension by at least one. -/
theorem ringKrullDim_quotient_succ_le_of_not_le_nilradical (hT : (nilradical T).IsPrime)
    {I : Ideal T} (hI : ¬ I ≤ nilradical T) :
    ringKrullDim (T ⧸ I) + 1 ≤ ringKrullDim T := by
  by_cases hI' : I = ⊤
  · rw [hI', ringKrullDim_eq_bot_of_subsingleton]
    simp
  have : Nonempty (PrimeSpectrum.zeroLocus (R := T) I) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty, ne_eq,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have := Ideal.Quotient.nontrivial_iff.mpr hI'
  have := (Ideal.Quotient.mk I).domain_nontrivial
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_length, ringKrullDim,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  let p' : PrimeSpectrum T := ⟨nilradical T, hT⟩
  have hp' : p' < l.head := by
    refine lt_of_le_of_ne (nilradical_le_prime l.head.1.asIdeal) fun h => hI ?_
    have hle : (I : Set T) ⊆ l.head.1.asIdeal := l.head.2
    rw [← h] at hle
    exact hle
  refine le_trans ?_ (le_iSup _ ((l.map Subtype.val (fun _ _ ↦ id)).cons p' hp'))
  simp

/-- For a ring `T` of finite type over a field with prime nilradical, killing an element that is
not a unit lowers the Krull dimension by at most one. -/
theorem ringKrullDim_le_quotient_span_singleton_add_one (k : Type*) [Field k] [Algebra k T]
    [Algebra.FiniteType k T] (hT : (nilradical T).IsPrime) {h : T} (hne : Ideal.span {h} ≠ ⊤) :
    ringKrullDim T ≤ ringKrullDim (T ⧸ Ideal.span {h}) + 1 := by
  set N := nilradical T with hN
  have : N.IsPrime := hT
  have : IsDomain (T ⧸ N) := Ideal.Quotient.isDomain N
  have : IsNoetherianRing (T ⧸ N) := Algebra.FiniteType.isNoetherianRing k (T ⧸ N)
  set h' : T ⧸ N := Ideal.Quotient.mk N h with hh'
  obtain ⟨m, hm, hhm⟩ := Ideal.exists_le_maximal _ hne
  have hNm : RingHom.ker (Ideal.Quotient.mk N) ≤ m := by
    rw [Ideal.mk_ker]
    exact nilradical_le_prime m
  have : (m.map (Ideal.Quotient.mk N)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hNm
  have hspan : Ideal.span {h'} = (Ideal.span {h}).map (Ideal.Quotient.mk N) := by
    rw [Ideal.map_span, Set.image_singleton]
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {h'})
    (J := m.map (Ideal.Quotient.mk N)) (by rw [hspan]; exact Ideal.map_mono hhm)
  have : q.IsPrime := hq.1.1
  have : (Ideal.span {h'}).IsPrincipal := ⟨⟨h', rfl⟩⟩
  have hheight : q.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {h'}) q hq
  have hformula := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k q
  have hle : ringKrullDim ((T ⧸ N) ⧸ q) ≤ ringKrullDim (T ⧸ Ideal.span {h}) := by
    refine ringKrullDim_le_of_surjective
      (Ideal.Quotient.lift (Ideal.span {h}) ((Ideal.Quotient.mk q).comp (Ideal.Quotient.mk N))
        fun a ha => ?_)
      (Ideal.Quotient.lift_surjective_of_surjective _ _
        (Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective))
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact hq.1.2 (hspan ▸ Ideal.mem_map_of_mem _ ha)
  rw [← ringKrullDim_quotient_nilradical, ← hformula, add_comm]
  exact add_le_add hle (by exact_mod_cast hheight)

/-- A ring with prime nilradical has pure dimension equal to its Krull dimension. -/
theorem hasPureRingDimension_of_isPrime_nilradical {A : Type u} [CommRing A]
    (hA : (nilradical A).IsPrime) {e : ℕ} (he : ringKrullDim A = e) :
    HasPureRingDimension A e := by
  intro p hp
  have : p.IsPrime := hp.1.1
  have : p = nilradical A :=
    le_antisymm (hp.2 ⟨hA, bot_le⟩ (nilradical_le_prime p)) (nilradical_le_prime p)
  subst this
  rw [ringKrullDim_quotient_nilradical, he]

/-- For a ring of finite type over a field with prime nilradical and dimension `e + 1`, the
quotient by a non-unit outside the nilradical has dimension `e`. -/
theorem ringKrullDim_quotient_span_singleton_eq (k : Type*) [Field k] [Algebra k T]
    [Algebra.FiniteType k T] (hT : (nilradical T).IsPrime) {h : T} (hh : h ∉ nilradical T)
    (hne : Ideal.span {h} ≠ ⊤) {e : ℕ} (he : ringKrullDim T = (e + 1 : ℕ)) :
    ringKrullDim (T ⧸ Ideal.span {h}) = e := by
  have h1 := ringKrullDim_quotient_succ_le_of_not_le_nilradical hT (I := Ideal.span {h})
    (by rwa [Ideal.span_singleton_le_iff_mem])
  have h2 := ringKrullDim_le_quotient_span_singleton_add_one k hT hne
  have := Ideal.Quotient.nontrivial_iff.mpr hne
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot (by simp)
    (ringKrullDim_nonneg_of_nontrivial (R := T ⧸ Ideal.span {h})))
  rw [← hm] at h1 h2 ⊢
  rw [he] at h1 h2
  norm_cast at h1 h2 ⊢
  have h1' : m ≤ e := (ENat.add_le_add_iff_right ENat.one_ne_top).mp h1
  have h2' : (e : ℕ∞) ≤ m := (ENat.add_le_add_iff_right ENat.one_ne_top).mp h2
  exact le_antisymm h1' h2'

end Langlands.AlgebraicGeometry.LangWeil.Slicing
