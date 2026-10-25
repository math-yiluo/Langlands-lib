import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Finset.Basic
import Langlands.Global.Arithmetic.KummerRadical
import Langlands.Global.Arithmetic.SUnitIndex
import Langlands.ClassField.Global.LocalPowerIndex
import Langlands.Global.Arithmetic.CyclicNonsplitPrimeStatement

/-! # Choosing auxiliary characters with prescribed common kernel -/

namespace Langlands.Global.Arithmetic.AuxiliaryPrimes

section GroupTheory

variable {V : Type*} [CommGroup V] [Finite V] {p : ℕ} [hp : Fact p.Prime]

/-- Cutting a subgroup `W` by a homomorphism into a group of order at most `p` that is
nontrivial on `W` divides its order by `p`, provided `W` has exponent `p`. -/
theorem card_inf_ker_mul {A : Type*} [Group A] [Finite A] (hA : Nat.card A ≤ p)
    (hV : ∀ v : V, v ^ p = 1) (χ : V →* A) (W : Subgroup V) (hW : ¬ W ≤ χ.ker) :
    Nat.card (W ⊓ χ.ker : Subgroup V) * p = Nat.card W := by
  set f : W →* A := χ.comp W.subtype
  have hker : Nat.card f.ker = Nat.card (W ⊓ χ.ker : Subgroup V) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcard : Nat.card W = Nat.card f.ker * Nat.card f.range := by
    rw [← Subgroup.index_ker, mul_comm, Subgroup.index_mul_card]
  have hpgroup : IsPGroup p W := fun w => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hV w.1)⟩
  obtain ⟨k, hk⟩ := hpgroup.exists_card_eq
  have hdvd : Nat.card f.range ∣ p ^ k := by
    rw [← hk, hcard]; exact Dvd.intro_left _ rfl
  obtain ⟨j, hj, hjk⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd
  have hrange_le : Nat.card f.range ≤ p :=
    (Nat.card_le_card_of_injective _ Subtype.val_injective).trans hA
  have hrange_ne : Nat.card f.range ≠ 1 := by
    intro h1
    apply hW
    intro w hw
    have hm : f ⟨w, hw⟩ ∈ f.range := ⟨⟨w, hw⟩, rfl⟩
    rw [Subgroup.card_eq_one.1 h1] at hm
    exact Subgroup.mem_bot.1 hm
  have hrange : Nat.card f.range = p := by
    rcases j with - | j
    · rw [pow_zero] at hjk; exact absurd hjk hrange_ne
    · rcases j with - | j
      · simpa using hjk
      · have : p ^ (j + 2) ≤ p := hjk ▸ hrange_le
        have h2 : p < p ^ (j + 2) := by
          calc p = p ^ 1 := (pow_one p).symm
            _ < p ^ (j + 2) := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
        omega
  rw [hcard, hker, hrange]

variable {ι : Type*} {A : ι → Type*} [∀ i, Group (A i)] [∀ i, Finite (A i)]

/-- Repeatedly cutting by characters that kill `α` but not the current subgroup reaches
`⟨α⟩`; every cut divides the order by `p`. -/
theorem exists_finset_inf_iInf_ker (hA : ∀ i, Nat.card (A i) ≤ p) (hV : ∀ v : V, v ^ p = 1)
    (χ : ∀ i, V →* A i) {α : V}
    (haux : ∀ W : Subgroup V, α ∈ W → W ≠ Subgroup.zpowers α →
      ∃ i, χ i α = 1 ∧ ¬ W ≤ (χ i).ker) :
    ∀ W : Subgroup V, α ∈ W → ∃ T : Finset ι,
      W ⊓ (⨅ i ∈ T, (χ i).ker) = Subgroup.zpowers α ∧
        Nat.card (Subgroup.zpowers α) * p ^ T.card ≤ Nat.card W := by
  classical
  intro W
  induction hW : Nat.card W using Nat.strong_induction_on generalizing W with
  | _ n IH =>
  intro hαW
  by_cases hWα : W = Subgroup.zpowers α
  · refine ⟨∅, ?_, ?_⟩
    · simp [hWα]
    · simp [hWα, ← hW]
  obtain ⟨i, hiα, hiW⟩ := haux W hαW hWα
  have hcard := card_inf_ker_mul (hA i) hV (χ i) W hiW
  have hpos : 0 < Nat.card (W ⊓ (χ i).ker : Subgroup V) := Nat.card_pos
  have hlt : Nat.card (W ⊓ (χ i).ker : Subgroup V) < n := by
    rw [← hW, ← hcard]
    have := hp.out.two_le
    nlinarith
  obtain ⟨T', hT', hcT'⟩ := IH _ hlt (W ⊓ (χ i).ker) rfl ⟨hαW, hiα⟩
  refine ⟨insert i T', ?_, ?_⟩
  · rw [Finset.iInf_insert, ← inf_assoc]
    exact hT'
  · calc Nat.card (Subgroup.zpowers α) * p ^ (insert i T').card
        ≤ Nat.card (Subgroup.zpowers α) * p ^ (T'.card + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.out.pos (Finset.card_insert_le _ _))
      _ = Nat.card (Subgroup.zpowers α) * p ^ T'.card * p := by ring
      _ ≤ Nat.card (W ⊓ (χ i).ker : Subgroup V) * p := Nat.mul_le_mul_right _ hcT'
      _ = n := by rw [hcard, hW]

/-- **Auxiliary characters.** If `V` has order `p ^ s` and exponent `p`, `α ≠ 1`, and characters
`χ i` into groups of order at most `p` satisfy the separation property `haux`, then there are
`s - 1` of them whose common kernel is `⟨α⟩` and which are jointly surjective. -/
theorem exists_finset_surjective (hA : ∀ i, Nat.card (A i) ≤ p) (hV : ∀ v : V, v ^ p = 1)
    (χ : ∀ i, V →* A i) {α : V} (hα : α ≠ 1) {s : ℕ} (hcardV : Nat.card V = p ^ s)
    (haux : ∀ W : Subgroup V, α ∈ W → W ≠ Subgroup.zpowers α →
      ∃ i, χ i α = 1 ∧ ¬ W ≤ (χ i).ker) :
    ∃ T : Finset ι, T.card + 1 = s ∧ (⨅ i ∈ T, (χ i).ker) = Subgroup.zpowers α ∧
      Function.Surjective (MonoidHom.pi fun i : T => χ i.1) := by
  classical
  obtain ⟨T, hT, hcT⟩ := exists_finset_inf_iInf_ker hA hV χ (by
    intro W hαW hW; exact haux W hαW hW) ⊤ (Subgroup.mem_top α)
  rw [top_inf_eq] at hT
  have horder : orderOf α = p := orderOf_eq_prime (hV α) hα
  have hzp : Nat.card (Subgroup.zpowers α) = p := by rw [Nat.card_zpowers, horder]
  set Φ := MonoidHom.pi fun i : T => χ i.1
  have hker : Φ.ker = Subgroup.zpowers α := by
    rw [← hT]
    ext v
    simp only [MonoidHom.mem_ker, Subgroup.mem_iInf]
    constructor
    · intro h i hi
      exact congrFun h ⟨i, hi⟩
    · intro h
      funext i
      exact h i.1 i.2
  have hrange : Nat.card Φ.range * p = p ^ s := by
    have h := Φ.ker.card_mul_index
    rw [Subgroup.index_ker, hker, hzp, hcardV] at h
    rw [mul_comm]; exact h
  have hcod : Nat.card (∀ i : T, A i.1) ≤ p ^ T.card := by
    rw [Nat.card_pi]
    calc ∏ i : T, Nat.card (A i.1) ≤ p ^ (Finset.univ : Finset T).card :=
          Finset.prod_le_pow_card _ _ _ fun i _ => hA i.1
      _ = p ^ T.card := by rw [Finset.card_univ, Fintype.card_coe]
  have hle : Nat.card Φ.range ≤ Nat.card (∀ i : T, A i.1) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have hs : T.card + 1 = s := by
    rw [hzp, Subgroup.card_top] at hcT
    have h1 : p ^ (T.card + 1) ≤ p ^ s := by rw [pow_succ, mul_comm, ← hcardV]; exact hcT
    have h2 : p ^ s ≤ p ^ (T.card + 1) := by
      rw [← hrange, pow_succ]
      exact Nat.mul_le_mul_right _ (hle.trans hcod)
    exact Nat.pow_right_injective hp.out.two_le (le_antisymm h1 h2)
  refine ⟨T, hs, hT, ?_⟩
  have heq : Nat.card Φ.range = Nat.card (∀ i : T, A i.1) := by
    apply le_antisymm hle
    have : Nat.card Φ.range = p ^ T.card := by
      have := hrange
      rw [← hs, pow_succ] at this
      exact Nat.eq_of_mul_eq_mul_right hp.out.pos this
    rw [this]; exact hcod
  rw [← MonoidHom.range_eq_top, ← Subgroup.card_eq_iff_eq_top]
  exact heq

end GroupTheory

section LocalCharacters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.ClassField.Global Langlands.Global.Arithmetic.SUnitIndex
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {K : Type*} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The image of an `S`-unit in the valuation units `U_q` of `K_q`, for a finite place
`q ∉ S`. -/
noncomputable def sUnitsToLocalUnits (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ S) :
    sUnits K S →* localUnits q :=
  ((Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom).comp
    (sUnits K S).subtype).codRestrict (localUnits q) fun x => by
      rw [mem_localUnits_iff]
      exact (valuedAdicCompletion_eq_valuation' q ((x : Kˣ) : K)).trans (x.2 q hq)

@[simp] theorem coe_sUnitsToLocalUnits (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ S)
    (x : sUnits K S) :
    (((sUnitsToLocalUnits S q hq x : localUnits q) : (q.adicCompletion K)ˣ) :
      q.adicCompletion K) = algebraMap K (q.adicCompletion K) ((x : Kˣ) : K) := rfl

/-- The group `U_S / U_S ^ p` of `S`-units modulo `p`-th powers. -/
abbrev sUnitsModPowers (p : ℕ) : Type _ :=
  sUnits K S ⧸ (powMonoidHom p : sUnits K S →* sUnits K S).range

/-- The local character `χ_q : U_S / U_S ^ p → U_q / U_q ^ p` at a finite place `q ∉ S`. -/
noncomputable def localChar (p : ℕ) (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ S) :
    sUnitsModPowers S p →* localUnits q ⧸ localUnitPowers q p :=
  QuotientGroup.lift _ ((QuotientGroup.mk' _).comp (sUnitsToLocalUnits S q hq)) (by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, powMonoidHom_apply, map_pow]
    exact ⟨_, rfl⟩)

theorem localChar_mk (p : ℕ) (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ S) (x : sUnits K S) :
    localChar S p q hq (QuotientGroup.mk x) =
      QuotientGroup.mk (sUnitsToLocalUnits S q hq x) :=
  rfl

/-- If `p` is a unit at `q`, then `U_q / U_q ^ p` has at most `p` elements. -/
theorem card_localUnits_quotient_le (q : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p ≠ 0)
    (hpq : IsUnit (p : q.adicCompletionIntegers K)) :
    Nat.card (localUnits q ⧸ localUnitPowers q p) ≤ p := by
  have h := index_localUnitPowers_le q p hp
  rw [Ideal.span_singleton_eq_top.2 hpq] at h
  have h1 : Nat.card (q.adicCompletionIntegers K ⧸
      (⊤ : Ideal (q.adicCompletionIntegers K))) = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨Ideal.Quotient.subsingleton_iff.2 rfl, inferInstance⟩
  rw [h1, mul_one] at h
  exact h

/-- **Local separation.** Let `Q` be a finite place of an extension `K'` above `q ∉ S`, with
`|U_q / U_q ^ p| ≤ p`. If `α` becomes a `p`-th power in `K'_Q` and `β` does not, then
`χ_q(α) = 1` and `χ_q(β) ≠ 1`. -/
theorem localChar_separates {p : ℕ} [hp : Fact p.Prime] (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∉ S) (hcard : Nat.card (localUnits q ⧸ localUnitPowers q p) ≤ p)
    {K' : Type*} [Field K'] [NumberField K'] [Algebra K K'] (Q : HeightOneSpectrum (𝓞 K'))
    [Q.asIdeal.LiesOver q.asIdeal] {α β : sUnits K S}
    (hα : ∃ c : Q.adicCompletion K', c ^ p = algebraMap K _ ((α : Kˣ) : K))
    (hβ : ¬ ∃ c : Q.adicCompletion K', c ^ p = algebraMap K _ ((β : Kˣ) : K)) :
    localChar S p q hq (QuotientGroup.mk α) = 1 ∧
      localChar S p q hq (QuotientGroup.mk β) ≠ 1 := by
  have key : ∀ x : sUnits K S, localChar S p q hq (QuotientGroup.mk x) = 1 →
      ∃ c : Q.adicCompletion K', c ^ p = algebraMap K _ ((x : Kˣ) : K) := by
    intro x hx
    rw [localChar_mk, QuotientGroup.eq_one_iff] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨algebraMap (q.adicCompletion K) (Q.adicCompletion K')
      (((y : localUnits q) : (q.adicCompletion K)ˣ) : q.adicCompletion K), ?_⟩
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, ← powMonoidHom_apply, hy,
      coe_sUnitsToLocalUnits, ← IsScalarTower.algebraMap_apply]
  refine ⟨?_, fun h => hβ (key β h)⟩
  by_contra hne
  have := localUnitPowers_finiteIndex q p hp.out.ne_zero
  have hAp : localChar S p q hq (QuotientGroup.mk α) ^ p = 1 := by
    have h : (QuotientGroup.mk (α ^ p) : sUnitsModPowers S p) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨α, rfl⟩
    rw [← map_pow, ← QuotientGroup.mk_pow, h, map_one]
  have htop : Subgroup.zpowers (localChar S p q hq (QuotientGroup.mk α)) = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [Nat.card_zpowers, orderOf_eq_prime hAp hne]
    exact hcard
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (htop ▸ Subgroup.mem_top (localChar S p q hq (QuotientGroup.mk β)))
  have h1 : localChar S p q hq (QuotientGroup.mk (β * (α ^ k)⁻¹)) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow, map_mul, map_inv,
      map_zpow, ← hk, mul_inv_cancel]
  obtain ⟨c', hc'⟩ := key _ h1
  obtain ⟨c, hc⟩ := hα
  refine hβ ⟨c' * c ^ k, ?_⟩
  have hα0 : algebraMap K (Q.adicCompletion K') ((α : Kˣ) : K) ≠ 0 :=
    (map_ne_zero _).2 (α : Kˣ).ne_zero
  have hck : (c ^ k) ^ p = (c ^ p) ^ k := by
    rw [← zpow_natCast (c ^ k) p, ← zpow_natCast c p]
    exact zpow_comm c k p
  rw [mul_pow, hc', hck, hc]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀]
  exact inv_mul_cancel_right₀ (zpow_ne_zero k hα0) _

end LocalCharacters

section Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial
open Langlands.ClassField.Global Langlands.Global.Arithmetic.SUnitIndex
  Langlands.Global.Arithmetic.KummerRadical
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

/-- The finite places of `K'` above a finite set of finite places of `K` form a finite set. -/
theorem exists_finset_under_mem {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] [Algebra K K'] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 K')), ∀ Q : HeightOneSpectrum (𝓞 K'),
      Q.under (𝓞 K) ∈ S → Q ∈ S' := by
  have hfin : {Q : HeightOneSpectrum (𝓞 K') | Q.under (𝓞 K) ∈ S}.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion
      (t := fun v => HeightOneSpectrum.asIdeal ⁻¹' (v.asIdeal.primesOver (𝓞 K')))
      S.finite_toSet fun v _ => ?_) ?_
    · have := v.isMaximal
      exact (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K')).preimage
        fun _ _ _ _ h => HeightOneSpectrum.ext h
    · intro Q hQ
      rw [Set.mem_iUnion₂]
      exact ⟨_, hQ, Q.isPrime, ⟨rfl⟩⟩
  exact ⟨hfin.toFinset, fun Q hQ => hfin.mem_toFinset.2 hQ⟩

variable {K : Type u} [Field K] [NumberField K]

omit [NumberField K] in
/-- An element of `K` that becomes a `p`-th power in `K(a^{1/p})` lies in `a ^ ℕ · K ^ p`. -/
theorem exists_eq_pow_mul_pow_of_radical {p : ℕ} [hp : Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {a : K} (ha : ∀ c : K, c ^ p ≠ a)
    [Fact (Irreducible (X ^ p - C a))] {b : K} {γ : radicalExtension K p a}
    (hγ : γ ^ p = algebraMap K _ b) : ∃ (k : ℕ) (c : K), b = a ^ k * c ^ p := by
  have := isGalois_radicalExtension (x := a) hζ
  have hcard : Nat.card (radicalExtension K p a ≃ₐ[K] radicalExtension K p a) = p := by
    rw [IsGalois.card_aut_eq_finrank, finrank_radicalExtension]
  refine exists_eq_pow_mul_pow_of_eq_pow hζ hcard (radicalRoot_pow p a) ?_ hγ
  rintro ⟨c, hc⟩
  apply ha c
  apply (algebraMap K (radicalExtension K p a)).injective
  rw [map_pow, hc, radicalRoot_pow]

/-- If `b = a ^ k · c ^ p` for `S`-units `a, b`, then the class of `b` in `U_S / U_S ^ p` is a
power of the class of `a`. -/
theorem mk_mem_zpowers_of_eq {p : ℕ} [hp : Fact p.Prime] (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a b : sUnits K S} {k : ℕ} {c : K} (h : ((b : Kˣ) : K) = ((a : Kˣ) : K) ^ k * c ^ p) :
    (QuotientGroup.mk b : sUnitsModPowers S p) ∈ Subgroup.zpowers (QuotientGroup.mk a) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.out.ne_zero, mul_zero] at h
    exact (b : Kˣ).ne_zero h
  have hcS : Units.mk0 c hc0 ∈ sUnits K S := by
    intro v hv
    have hv' := congrArg (v.valuation K) h
    rw [map_mul, map_pow, map_pow, a.2 v hv, b.2 v hv, one_pow, one_mul] at hv'
    exact (pow_eq_one_iff.1 hv'.symm).resolve_right hp.out.ne_zero
  have hk : (QuotientGroup.mk a : sUnitsModPowers S p) ^ k = QuotientGroup.mk b := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq]
    refine ⟨⟨Units.mk0 c hc0, hcS⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    simp only [powMonoidHom_apply, Subgroup.coe_pow, Units.val_pow_eq_pow_val, Units.val_mk0,
      Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val, h]
    have ha0 : ((a : Kˣ) : K) ^ k ≠ 0 := pow_ne_zero k (a : Kˣ).ne_zero
    field_simp
  rw [← hk]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k

/-- **Auxiliary primes** (Artin–Tate, Chapter VI, §3, proof of Lemma 3). Let `K` contain a
primitive `p`-th root of unity, let `S` contain the finite places above `p`, and let `α` be an
`S`-unit that is not a `p`-th power. Then there is a finite set `T` of finite places outside
`S`, with `|T| + 1 = |S| + |S_∞|`, at which `α` is a local `p`-th power and such that every
family of local units on `T` is congruent to a single `S`-unit modulo local `p`-th powers. -/
theorem exists_auxiliaryPrimes (hNS : CyclicNonsplitPrimeStatement.{u, u}) {p : ℕ}
    [hp : Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v ∉ S, IsUnit (p : v.adicCompletionIntegers K)) (α : Kˣ) (hαS : α ∈ sUnits K S)
    (hα : ∀ c : K, c ^ p ≠ α) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint S T ∧
      T.card + 1 = S.card + Fintype.card (InfinitePlace K) ∧
      (∀ q ∈ T, ∃ c : q.adicCompletion K, c ^ p = algebraMap K _ (α : K)) ∧
      ∀ u : ∀ q : HeightOneSpectrum (𝓞 K), (q.adicCompletion K)ˣ,
        (∀ q ∈ T, Valued.v (u q : q.adicCompletion K) = 1) →
        ∃ e ∈ sUnits K S, ∀ q ∈ T, ∃ c : (q.adicCompletion K)ˣ,
          u q = Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom e * c ^ p := by
  classical
  have hp0 := hp.out.ne_zero
  have hcardV : Nat.card (sUnitsModPowers S p) =
      p ^ (S.card + Fintype.card (InfinitePlace K)) := index_pow_sUnits K S p hζ
  have : Finite (sUnitsModPowers S p) :=
    Nat.finite_of_card_ne_zero (by rw [hcardV]; exact pow_ne_zero _ hp0)
  have hV : ∀ v : sUnitsModPowers S p, v ^ p = 1 := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨x, rfl⟩
  set a : sUnits K S := ⟨α, hαS⟩
  have ha1 : (QuotientGroup.mk a : sUnitsModPowers S p) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    rintro ⟨y, hy⟩
    apply hα ((y : Kˣ) : K)
    have := congrArg (fun z : sUnits K S => ((z : Kˣ) : K)) hy
    simpa using this
  let χ : ∀ i : {q // q ∉ S}, sUnitsModPowers S p →* localUnits i.1 ⧸ localUnitPowers i.1 p :=
    fun i => localChar S p i.1 i.2
  have : ∀ i : {q // q ∉ S}, Finite (localUnits i.1 ⧸ localUnitPowers i.1 p) := fun i => by
    have := localUnitPowers_finiteIndex i.1 p hp0
    infer_instance
  have hA : ∀ i : {q // q ∉ S}, Nat.card (localUnits i.1 ⧸ localUnitPowers i.1 p) ≤ p :=
    fun i => card_localUnits_quotient_le i.1 hp0 (hpS i.1 i.2)
  have haux : ∀ W : Subgroup (sUnitsModPowers S p), (QuotientGroup.mk a) ∈ W →
      W ≠ Subgroup.zpowers (QuotientGroup.mk a) →
      ∃ i, χ i (QuotientGroup.mk a) = 1 ∧ ¬ W ≤ (χ i).ker := by
    intro W haW hW
    obtain ⟨bb, hbW, hbα⟩ : ∃ b ∈ W, b ∉ Subgroup.zpowers (QuotientGroup.mk a) := by
      by_contra! h
      exact hW (le_antisymm h (Subgroup.zpowers_le.2 haW))
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective bb
    have : Fact (Irreducible (X ^ p - C (α : K))) :=
      ⟨irreducible_of_forall_pow_ne hp.out hα⟩
    have : NumberField (radicalExtension K p (α : K)) := numberField_radicalExtension
    set K' := radicalExtension K p (α : K)
    set b' : K' := algebraMap K K' ((b : Kˣ) : K)
    have hb' : ∀ γ : K', γ ^ p ≠ b' := by
      intro γ hγ
      obtain ⟨k, c, hkc⟩ := exists_eq_pow_mul_pow_of_radical hζ hα hγ
      exact hbα (mk_mem_zpowers_of_eq S (a := a) hkc)
    have : Fact (Irreducible (X ^ p - C b')) := ⟨irreducible_of_forall_pow_ne hp.out hb'⟩
    have : NumberField (radicalExtension K' p b') := numberField_radicalExtension
    have hζ' : IsPrimitiveRoot (algebraMap K K' ζ) p :=
      hζ.map_of_injective (algebraMap K K').injective
    have : IsGalois K' (radicalExtension K' p b') := isGalois_radicalExtension hζ'
    have hfin : Module.finrank K' (radicalExtension K' p b') = p := finrank_radicalExtension
    have : IsCyclic (radicalExtension K' p b' ≃ₐ[K'] radicalExtension K' p b') :=
      isCyclic_of_prime_card (by rw [IsGalois.card_aut_eq_finrank, hfin])
    obtain ⟨S', hS'⟩ := exists_finset_under_mem (K' := K') S
    obtain ⟨Q, hQS', w, hw, hQw⟩ :=
      hNS K' (radicalExtension K' p b') (by rw [hfin]; exact hp.out.one_lt) S'
    have hq : Q.under (𝓞 K) ∉ S := fun h => hQS' (hS' Q h)
    have : Q.asIdeal.LiesOver (Q.under (𝓞 K)).asIdeal := ⟨rfl⟩
    have hβQ : ¬ ∃ c : Q.adicCompletion K', c ^ p = algebraMap K _ ((b : Kˣ) : K) := by
      rintro ⟨c, hc⟩
      have := hw
      have : NeZero p := ⟨hp0⟩
      apply hQw
      refine finrank_adicCompletion_eq_one hζ' (adjoin_radicalRoot p b') (radicalRoot_pow p b')
        Q w (c := c) ?_
      rw [hc, IsScalarTower.algebraMap_apply K K' (Q.adicCompletion K')]
    have hαQ : ∃ c : Q.adicCompletion K', c ^ p = algebraMap K _ (α : K) :=
      ⟨algebraMap K' _ (radicalRoot K p (α : K)), by
        rw [← map_pow, radicalRoot_pow, ← IsScalarTower.algebraMap_apply]⟩
    obtain ⟨h1, h2⟩ := localChar_separates S (Q.under (𝓞 K)) hq
      (card_localUnits_quotient_le _ hp0 (hpS _ hq)) Q (α := a) (β := b) hαQ hβQ
    exact ⟨⟨Q.under (𝓞 K), hq⟩, h1, fun hle => h2 (hle hbW)⟩
  obtain ⟨T', hT'card, hT'ker, hsurj⟩ := exists_finset_surjective hA hV χ ha1 hcardV haux
  have hker : ∀ i ∈ T', χ i (QuotientGroup.mk a) = 1 := by
    have hmem : (QuotientGroup.mk a : sUnitsModPowers S p) ∈ ⨅ i ∈ T', (χ i).ker :=
      hT'ker ▸ Subgroup.mem_zpowers _
    intro i hi
    exact (Subgroup.mem_iInf.1 hmem i |> Subgroup.mem_iInf.1) hi
  refine ⟨T'.map (Function.Embedding.subtype _), ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro q hqS hqT
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hqT
    exact i.2 hqS
  · rw [Finset.card_map, hT'card]
  · intro q hqT
    obtain ⟨i, hiT, rfl⟩ := Finset.mem_map.1 hqT
    have h := hker i hiT
    change localChar S p i.1 i.2 (QuotientGroup.mk a) = 1 at h
    rw [localChar_mk, QuotientGroup.eq_one_iff] at h
    obtain ⟨y, hy⟩ := h
    refine ⟨(((y : localUnits i.1) : (i.1.adicCompletion K)ˣ) : i.1.adicCompletion K), ?_⟩
    have hy' := congrArg
      (fun z : localUnits i.1 => ((z : (i.1.adicCompletion K)ˣ) : i.1.adicCompletion K)) hy
    simp only [powMonoidHom_apply, Subgroup.coe_pow, Units.val_pow_eq_pow_val,
      coe_sUnitsToLocalUnits] at hy'
    exact hy'
  · intro u hu
    have hloc : ∀ i : T', u i.1.1 ∈ localUnits i.1.1 := fun i =>
      (mem_localUnits_iff _ _).2 (hu _ (Finset.mem_map_of_mem _ i.2))
    obtain ⟨vv, hvv⟩ := hsurj fun i => QuotientGroup.mk ⟨u i.1.1, hloc i⟩
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective vv
    refine ⟨e, e.2, ?_⟩
    intro q hqT
    obtain ⟨i, hiT, rfl⟩ := Finset.mem_map.1 hqT
    have h := congrFun hvv ⟨i, hiT⟩
    change localChar S p i.1 i.2 (QuotientGroup.mk e) = _ at h
    rw [localChar_mk, QuotientGroup.eq] at h
    obtain ⟨y, hy⟩ := h
    refine ⟨((y : localUnits i.1) : (i.1.adicCompletion K)ˣ), ?_⟩
    have hy' := congrArg (fun z : localUnits i.1 => (z : (i.1.adicCompletion K)ˣ)) hy
    simp only [powMonoidHom_apply, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv] at hy'
    have he : Units.map (algebraMap K (i.1.adicCompletion K)).toMonoidHom (e : Kˣ) =
        (sUnitsToLocalUnits S i.1 i.2 e : (i.1.adicCompletion K)ˣ) := rfl
    show u i.1 = Units.map (algebraMap K (i.1.adicCompletion K)).toMonoidHom (e : Kˣ) *
      ((y : localUnits i.1) : (i.1.adicCompletion K)ˣ) ^ p
    rw [hy', he, mul_inv_cancel_left]

end Global

end Langlands.Global.Arithmetic.AuxiliaryPrimes
