import Langlands.Global.Arithmetic.CyclicNonsplitPrimeProof
import Langlands.Global.Arithmetic.CyclicPrimePowerLocalDegreeProof
import Langlands.Global.Arithmetic.CyclotomicPrimePowerGalois
import Langlands.Global.Arithmetic.KummerRadical
import Langlands.Global.Arithmetic.PowerDescent
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-! # Global powers from local powers at almost all finite places -/

namespace Langlands.Global.Arithmetic.LocalPowerDescent

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u v

/-- Local `m`-th powers at almost all finite places of `F` remain local `m`-th powers at almost
all finite places of a finite extension `E`. -/
theorem eventually_pow_extension {F : Type u} {E : Type v} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] {m : ℕ} {a : F}
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∃ c : v.adicCompletion F, c ^ m = algebraMap F (v.adicCompletion F) a) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite,
      ∃ c : w.adicCompletion E, c ^ m = algebraMap E (w.adicCompletion E) (algebraMap F E a) := by
  have htend : Tendsto (fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F)) cofinite cofinite := by
    apply Filter.Tendsto.cofinite_of_finite_preimage_singleton
    intro v
    refine Finite.of_injective
      (fun w : (fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F)) ⁻¹' {v} =>
        (⟨w.1, ⟨?_⟩⟩ : AdelicFunctoriality.FinitePlacesAbove E v)) ?_
    · have hw : w.1.under (𝓞 F) = v := w.2
      exact (congrArg HeightOneSpectrum.asIdeal hw).symm
    · intro a b hab
      have hab' := congrArg Subtype.val hab
      exact Subtype.ext hab'
  refine (htend.eventually h).mono fun w hw => ?_
  obtain ⟨c, hc⟩ := hw
  refine ⟨AdelicFunctoriality.FiniteExtension.completionMap (w.under (𝓞 F)) w c, ?_⟩
  rw [← map_pow, hc, AdelicFunctoriality.FiniteExtension.completionMap_coe]

/-- The finite set of places where an eventually true local property fails. -/
theorem exists_finset_of_eventually {F : Type u} [Field F] [NumberField F]
    {P : HeightOneSpectrum (𝓞 F) → Prop} (h : ∀ᶠ v in cofinite, P v) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∉ S → P v := by
  classical
  refine ⟨(Filter.eventually_cofinite.1 h).toFinset, fun v hv => ?_⟩
  simpa using hv

/-- **Kummer step for a prime exponent.** If `B` contains a primitive `ℓ`-th root of unity and
`a` is an `ℓ`-th power in almost every completion, then `a` is an `ℓ`-th power in `B`. -/
theorem exists_pow_eq_of_eventually_prime {B : Type u} [Field B] [NumberField B] {ℓ : ℕ}
    (hℓ : ℓ.Prime) {ζ : B} (hζ : IsPrimitiveRoot ζ ℓ) {a : B}
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 B) in cofinite,
      ∃ c : v.adicCompletion B, c ^ ℓ = algebraMap B (v.adicCompletion B) a) :
    ∃ b : B, b ^ ℓ = a := by
  classical
  by_contra hne
  push Not at hne
  have : Fact (Irreducible (Polynomial.X ^ ℓ - Polynomial.C a)) :=
    ⟨KummerRadical.irreducible_of_forall_pow_ne hℓ hne⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let E := KummerRadical.radicalExtension B ℓ a
  have : NumberField E := KummerRadical.numberField_radicalExtension
  have : IsGalois B E := KummerRadical.isGalois_radicalExtension hζ
  have hdeg : Module.finrank B E = ℓ := KummerRadical.finrank_radicalExtension
  have : IsCyclic (E ≃ₐ[B] E) := isCyclic_of_prime_card (p := ℓ)
    (by rw [IsGalois.card_aut_eq_finrank, hdeg])
  obtain ⟨S, hS⟩ := exists_finset_of_eventually h
  obtain ⟨v, hvS, w, hw, hloc⟩ :=
    cyclicNonsplitPrimeStatement.{u, u} B E (by rw [hdeg]; exact hℓ.one_lt) S
  obtain ⟨c, hc⟩ := hS v hvS
  let := hw
  exact hloc (KummerRadical.finrank_adicCompletion_eq_one hζ (KummerRadical.adjoin_radicalRoot ℓ a)
    (KummerRadical.radicalRoot_pow ℓ a) v w hc)

/-- If `ζ` is a primitive `ℓ ^ (r + 1)`-th root of unity and `c ^ ℓ ^ (r + 1) = y ^ ℓ`, then `y` is
an `ℓ ^ r`-th power. -/
theorem exists_pow_eq_of_pow_eq_pow {L : Type*} [Field L] {ℓ r : ℕ} (hℓ : 0 < ℓ) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (ℓ ^ (r + 1))) {c y : L} (h : c ^ ℓ ^ (r + 1) = y ^ ℓ) :
    ∃ d : L, d ^ ℓ ^ r = y := by
  have : NeZero ℓ := ⟨hℓ.ne'⟩
  set e := c ^ ℓ ^ r with he
  have h' : y ^ ℓ = e ^ ℓ := by rw [he, ← pow_mul, ← pow_succ, h]
  by_cases he0 : e = 0
  · refine ⟨c, ?_⟩
    rw [he0, zero_pow hℓ.ne'] at h'
    rw [← he, he0]
    exact ((pow_eq_zero_iff hℓ.ne').1 h').symm
  have hω : IsPrimitiveRoot (ζ ^ ℓ ^ r) ℓ := hζ.pow (pow_pos hℓ _) (pow_succ ℓ r)
  have h1 : (y / e) ^ ℓ = 1 := by rw [div_pow, h', div_self (pow_ne_zero ℓ he0)]
  obtain ⟨i, -, hi⟩ := hω.eq_pow_of_pow_eq_one h1
  refine ⟨ζ ^ i * c, ?_⟩
  rw [mul_pow, ← pow_mul, mul_comm i, pow_mul, hi, ← he, div_mul_cancel₀ _ he0]

/-- **Kummer step for a prime-power exponent.** If `B` contains a primitive `ℓ ^ r`-th root of
unity and `a` is an `ℓ ^ r`-th power in almost every completion, then `a` is an `ℓ ^ r`-th power
in `B`. -/
theorem exists_pow_eq_of_eventually_primePow {B : Type u} [Field B] [NumberField B] {ℓ : ℕ}
    (hℓ : ℓ.Prime) : ∀ (r : ℕ) {ζ : B}, IsPrimitiveRoot ζ (ℓ ^ r) → ∀ {a : B},
      (∀ᶠ v : HeightOneSpectrum (𝓞 B) in cofinite,
        ∃ c : v.adicCompletion B, c ^ ℓ ^ r = algebraMap B (v.adicCompletion B) a) →
      ∃ b : B, b ^ ℓ ^ r = a
  | 0, _, _, a, _ => ⟨a, by rw [pow_zero, pow_one]⟩
  | r + 1, ζ, hζ, a, h => by
    have hζℓ : IsPrimitiveRoot (ζ ^ ℓ ^ r) ℓ := hζ.pow (pow_pos hℓ.pos _) (pow_succ ℓ r)
    obtain ⟨b, rfl⟩ := exists_pow_eq_of_eventually_prime hℓ hζℓ (h.mono fun v ⟨c, hc⟩ =>
      ⟨c ^ ℓ ^ r, by rw [← pow_mul, ← pow_succ, hc]⟩)
    have hb : ∀ᶠ v : HeightOneSpectrum (𝓞 B) in cofinite,
        ∃ c : v.adicCompletion B, c ^ ℓ ^ r = algebraMap B (v.adicCompletion B) b :=
      h.mono fun v ⟨c, hc⟩ => by
        rw [map_pow] at hc
        exact exists_pow_eq_of_pow_eq_pow hℓ.pos
          (hζ.map_of_injective (algebraMap B (v.adicCompletion B)).injective) hc
    have hζ' : IsPrimitiveRoot (ζ ^ ℓ) (ℓ ^ r) := hζ.pow (pow_pos hℓ.pos _) (pow_succ' ℓ r)
    obtain ⟨b', rfl⟩ := exists_pow_eq_of_eventually_primePow hℓ r hζ' hb
    exact ⟨b', by rw [← pow_mul, ← pow_succ]⟩

/-- **Cyclic descent.** Let `E / B` be a cyclic extension of prime-power degree, and let `E`
contain a primitive `m`-th root of unity and an `m`-th root `β` of `a ∈ Bˣ`. If `a` is an `m`-th
power in almost every completion of `B`, then `a` is an `m`-th power in `B`. -/
theorem exists_pow_eq_of_isCyclic {B : Type u} {E : Type u} [Field B] [NumberField B] [Field E]
    [NumberField E] [Algebra B E] [IsGalois B E] [IsCyclic (E ≃ₐ[B] E)] {ℓ e m : ℕ}
    (hℓ : ℓ.Prime) (hdeg : Module.finrank B E = ℓ ^ e) (hm : 0 < m) {ζ : E}
    (hζ : IsPrimitiveRoot ζ m) {a : B} (ha : a ≠ 0) {β : E} (hβ : β ^ m = algebraMap B E a)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 B) in cofinite,
      ∃ c : v.adicCompletion B, c ^ m = algebraMap B (v.adicCompletion B) a) :
    ∃ b : B, b ^ m = a := by
  classical
  have : NeZero m := ⟨hm.ne'⟩
  suffices hρ : ∃ ρ : E, ρ ^ m = algebraMap B E a ∧ ρ ∈ (⊥ : IntermediateField B E) by
    obtain ⟨ρ, hρm, hρB⟩ := hρ
    obtain ⟨b, rfl⟩ := IntermediateField.mem_bot.1 hρB
    exact ⟨b, (algebraMap B E).injective (by rw [map_pow, hρm])⟩
  rcases Nat.eq_zero_or_pos e with rfl | he
  · refine ⟨β, hβ, ?_⟩
    rw [pow_zero, ← IntermediateField.finrank_top', IntermediateField.finrank_eq_one_iff] at hdeg
    rw [← hdeg]
    exact IntermediateField.mem_top
  obtain ⟨S, hS⟩ := exists_finset_of_eventually h
  obtain ⟨v, hvS, w, hw, hloc⟩ :=
    cyclicPrimePowerLocalDegreeStatement.{u, u} B E ℓ e hℓ he hdeg S
  obtain ⟨c, hc⟩ := hS v hvS
  let := hw
  set ι := algebraMap E (w.adicCompletion E) with hι
  set c' := algebraMap (v.adicCompletion B) (w.adicCompletion E) c with hc'
  have hβ0 : ι β ≠ 0 := by
    rw [map_ne_zero]
    rintro rfl
    rw [zero_pow hm.ne', eq_comm, map_eq_zero] at hβ
    exact ha hβ
  have hβc : ι β ^ m = c' ^ m := by
    rw [← map_pow, hβ, ← map_pow, hc, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have hζw : IsPrimitiveRoot (ι ζ) m := hζ.map_of_injective ι.injective
  have h1 : (c' / ι β) ^ m = 1 := by rw [div_pow, ← hβc, div_self (pow_ne_zero m hβ0)]
  obtain ⟨j, -, hj⟩ := hζw.eq_pow_of_pow_eq_one h1
  set ρ := ζ ^ j * β with hρ
  have hρm : ρ ^ m = algebraMap B E a := by
    rw [hρ, mul_pow, ← pow_mul, mul_comm j, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hβ]
  have hρloc : ι ρ = c' := by rw [hρ, map_mul, map_pow, hj, div_mul_cancel₀ _ hβ0]
  refine ⟨ρ, hρm, ?_⟩
  set K' := IntermediateField.adjoin B {ρ} with hK'
  -- every element of `B(ρ)` maps into the image of `B_v`
  let Q : Subalgebra B E := Subalgebra.comap (IsScalarTower.toAlgHom B E (w.adicCompletion E))
    ((⊥ : Subalgebra (v.adicCompletion B) (w.adicCompletion E)).restrictScalars B)
  have hρQ : ρ ∈ Q := by
    change ι ρ ∈ (⊥ : Subalgebra (v.adicCompletion B) (w.adicCompletion E))
    rw [hρloc]
    exact Subalgebra.algebraMap_mem _ c
  have hKQ : ∀ k ∈ K', ι k ∈ Set.range (algebraMap (v.adicCompletion B) (w.adicCompletion E)) := by
    intro k hk
    have hle : K'.toSubalgebra ≤ Q := by
      rw [hK', IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic ρ)]
      exact Algebra.adjoin_le (Set.singleton_subset_iff.2 hρQ)
    exact Algebra.mem_bot.1 (hle hk)
  -- `E_w` is spanned over `B_v` by the image of a basis of `E / B(ρ)`
  let bE := Module.finBasis K' E
  let T : Submodule (v.adicCompletion B) (w.adicCompletion E) :=
    Submodule.span _ (Set.range fun i => ι (bE i))
  have hT : ∀ y : E, ι y ∈ T := by
    intro y
    rw [← bE.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨x, hx⟩ := hKQ _ (bE.repr y i).2
    rw [Algebra.smul_def, map_mul, IntermediateField.algebraMap_apply, ← hx, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hTT : T * T ≤ T := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    change ι (bE i) * ι (bE j) ∈ T
    rw [← map_mul]
    exact hT _
  have hmul : ∀ x y, x ∈ T → y ∈ T → x * y ∈ T := fun x y hx hy =>
    hTT (Submodule.mul_mem_mul hx hy)
  have h1T : (1 : w.adicCompletion E) ∈ T := by rw [← map_one ι]; exact hT 1
  have htop := AdelicFunctoriality.subalgebra_eq_top_of_algebraMap_mem v w
    (T.toSubalgebra h1T hmul) hT
  have hTtop : T = ⊤ := by
    rw [← Submodule.toSubalgebra_toSubmodule T h1T hmul, htop, Algebra.top_toSubmodule]
  have hle : Module.finrank (v.adicCompletion B) (w.adicCompletion E) ≤ Module.finrank K' E := by
    rw [← finrank_top, ← hTtop]
    exact (finrank_range_le_card _).trans (by simp)
  rw [hloc, ← Module.finrank_mul_finrank B K' E] at hle
  have hpos : 0 < Module.finrank K' E := Module.finrank_pos
  have hK1 : Module.finrank B K' = 1 := by
    have := Nat.le_of_mul_le_mul_right (a := Module.finrank B K') (b := 1)
      (by rw [one_mul]; exact hle) hpos
    have := Module.finrank_pos (R := B) (M := K')
    omega
  have hρK : ρ ∈ K' := IntermediateField.mem_adjoin_simple_self B ρ
  rwa [IntermediateField.finrank_eq_one_iff.1 hK1] at hρK

/-- Descent through a cyclic extension of prime-power degree that contains a primitive
`ℓ ^ m`-th root of unity. -/
theorem exists_pow_eq_of_cyclotomic {B : Type u} {E : Type u} [Field B] [NumberField B] [Field E]
    [NumberField E] [Algebra B E] [IsGalois B E] [IsCyclic (E ≃ₐ[B] E)] {ℓ e m : ℕ}
    (hℓ : ℓ.Prime) (hdeg : Module.finrank B E = ℓ ^ e) {ζ : E}
    (hζ : IsPrimitiveRoot ζ (ℓ ^ m)) {a : B} (ha : a ≠ 0)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 B) in cofinite,
      ∃ c : v.adicCompletion B, c ^ ℓ ^ m = algebraMap B (v.adicCompletion B) a) :
    ∃ b : B, b ^ ℓ ^ m = a := by
  obtain ⟨β, hβ⟩ := exists_pow_eq_of_eventually_primePow hℓ m hζ (eventually_pow_extension (E := E) h)
  exact exists_pow_eq_of_isCyclic hℓ hdeg (pow_pos hℓ.pos m) hζ ha hβ h

/-- Global powers in a field containing a primitive `ℓ ^ k`-th root of unity, where `k ≠ 0` and
`k + 2 ≤ ℓ * k`. -/
theorem exists_pow_eq_of_primitiveRoot {B : Type u} [Field B] [NumberField B] {ℓ n k : ℕ}
    (hℓ : ℓ.Prime) (hk : k ≠ 0) (hkℓ : k + 2 ≤ ℓ * k) {ξ : B} (hξ : IsPrimitiveRoot ξ (ℓ ^ k))
    {a : B} (ha : a ≠ 0)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 B) in cofinite,
      ∃ c : v.adicCompletion B, c ^ ℓ ^ (n + k) = algebraMap B (v.adicCompletion B) a) :
    ∃ b : B, b ^ ℓ ^ (n + k) = a := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  let E := CyclotomicField (ℓ ^ (n + k)) B
  have : IsGalois B E := IsCyclotomicExtension.isGalois {ℓ ^ (n + k)} B E
  obtain ⟨hcyc, e, hdeg⟩ :=
    CyclotomicPrimePowerGalois.isCyclic_and_finrank_eq_pow (E := E) (n := n) hℓ hk hkℓ hξ
  exact exists_pow_eq_of_cyclotomic hℓ hdeg (IsCyclotomicExtension.zeta_spec _ B E) ha h

/-- **Odd prime powers.** For an odd prime `ℓ`, a nonzero element that is an `ℓ ^ r`-th power in
almost every completion is an `ℓ ^ r`-th power. -/
theorem exists_pow_eq_of_eventually_oddPrimePow {K : Type u} [Field K] [NumberField K] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (r : ℕ) {a : K} (ha : a ≠ 0)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      ∃ c : v.adicCompletion K, c ^ ℓ ^ r = algebraMap K (v.adicCompletion K) a) :
    ∃ b : K, b ^ ℓ ^ r = a := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rcases r with _ | n
  · exact ⟨a, by rw [pow_zero, pow_one]⟩
  let B := CyclotomicField ℓ K
  have : FiniteDimensional K B := IsCyclotomicExtension.finiteDimensional {ℓ} K B
  have hξ : IsPrimitiveRoot (IsCyclotomicExtension.zeta ℓ K B) (ℓ ^ 1) := by
    rw [pow_one]; exact IsCyclotomicExtension.zeta_spec ℓ K B
  have h3 : 3 ≤ ℓ := by have := hℓ.two_le; omega
  obtain ⟨b, hb⟩ := exists_pow_eq_of_primitiveRoot (n := n) hℓ one_ne_zero (by omega) hξ
    ((map_ne_zero (algebraMap K B)).2 ha) (eventually_pow_extension (E := B) h)
  have hd : Module.finrank K B ∣ ℓ - 1 := by
    rw [← Nat.totient_prime hℓ]; exact CyclotomicPrimePowerGalois.finrank_dvd_totient
  have hcop : (Module.finrank K B).Coprime (ℓ ^ (n + 1)) := by
    refine Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 ?_))
    intro hdvd
    have hpos : 0 < Module.finrank K B := Module.finrank_pos
    have := Nat.le_of_dvd hpos hdvd
    have := Nat.le_of_dvd (by omega) hd
    omega
  exact PowerDescent.exists_pow_eq_of_coprime_degree hcop ⟨b, hb⟩

/-- **Powers of two.** A nonzero element that is a `2 ^ (s + 2)`-th power in almost every
completion is a `2 ^ (s + 1)`-th power. -/
theorem exists_pow_eq_of_eventually_twoPow {K : Type u} [Field K] [NumberField K] (s : ℕ) {a : K}
    (ha : a ≠ 0)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      ∃ c : v.adicCompletion K, c ^ 2 ^ (s + 2) = algebraMap K (v.adicCompletion K) a) :
    ∃ b : K, b ^ 2 ^ (s + 1) = a := by
  have hk : (2 : ℕ) + 2 ≤ 2 * 2 := le_refl _
  by_cases hi : ∃ i : K, i ^ 2 = -1
  · obtain ⟨i, hi⟩ := hi
    have hi4 : IsPrimitiveRoot i (2 ^ 2) := by
      have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := i) (by rw [pow_one, hi]; norm_num)
        (by
          have h4 : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hi]; norm_num
          simpa using h4)
      rw [← this]; exact IsPrimitiveRoot.orderOf i
    obtain ⟨b, hb⟩ := exists_pow_eq_of_primitiveRoot (n := s) Nat.prime_two two_ne_zero hk hi4 ha h
    exact ⟨b ^ 2, by rw [← pow_mul, ← pow_succ', hb]⟩
  let B := CyclotomicField (2 ^ 2) K
  have : FiniteDimensional K B := IsCyclotomicExtension.finiteDimensional {2 ^ 2} K B
  obtain ⟨b, hb⟩ := exists_pow_eq_of_primitiveRoot (n := s) Nat.prime_two two_ne_zero hk
    (IsCyclotomicExtension.zeta_spec (2 ^ 2) K B) ((map_ne_zero (algebraMap K B)).2 ha)
    (eventually_pow_extension (E := B) h)
  obtain ⟨c, hc⟩ := PowerDescent.exists_pow_eq_degree_of_root (K := K) ⟨b, hb⟩
  obtain ⟨t, ht⟩ : Module.finrank K B ∣ 2 := by
    have := CyclotomicPrimePowerGalois.finrank_dvd_totient (K := K) (L := B) (m := 2 ^ 2)
    rw [Nat.totient_prime_pow Nat.prime_two two_pos] at this
    simpa using this
  set y := (c ^ t) ^ 2 ^ (s + 1) with hy
  have ha2 : a ^ 2 = y ^ 2 := by
    calc a ^ 2 = (a ^ Module.finrank K B) ^ t := by rw [← pow_mul, ← ht]
      _ = y ^ 2 := by
        rw [← hc, hy, ← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 ha2 with hay | hay
  · exact ⟨c ^ t, hay.symm⟩
  exfalso
  refine hi (exists_pow_eq_of_eventually_prime Nat.prime_two (IsPrimitiveRoot.neg_one 0 two_ne_zero.symm) ?_)
  have hy0 : y ≠ 0 := by rintro hy0; rw [hy0, neg_zero] at hay; exact ha hay
  refine h.mono fun v ⟨z, hz⟩ => ⟨((z ^ 2) / algebraMap K _ (c ^ t)) ^ 2 ^ s, ?_⟩
  have hct : algebraMap K (v.adicCompletion K) (c ^ t) ≠ 0 := by
    rw [map_ne_zero]; rintro h0; rw [hy, h0, zero_pow (pow_ne_zero _ two_ne_zero)] at hy0
    exact hy0 rfl
  have hz' : (z ^ 2) ^ 2 ^ (s + 1) =
      -(algebraMap K (v.adicCompletion K) (c ^ t)) ^ 2 ^ (s + 1) := by
    rw [← pow_mul, show 2 * 2 ^ (s + 1) = 2 ^ (s + 2) by ring, hz, hay, hy, map_neg, map_pow]
  rw [← pow_mul, show 2 ^ s * 2 = 2 ^ (s + 1) by ring, div_pow, hz', neg_div,
    div_self (pow_ne_zero _ hct), map_neg, map_one]

end Langlands.Global.Arithmetic.LocalPowerDescent
