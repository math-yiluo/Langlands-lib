import Langlands.GaloisCohomology.Global.Units.ComplexRestriction

/-!
# `H²` of the `S`-units of `K_S` and the Brauer group outside `S`

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places of `K`, `K_S ⊆ Ω` the
maximal extension unramified outside `S` (and the infinite places), `G_S = Gal(K_S/K)`, `𝒪_Sˣ` the
`S`-units of `K_S`, and `ℓ` a prime such that every place above `ℓ` lies in `S`.

* `maximalSUnitsInflation K Ω S n : Hⁿ(G_S, 𝒪_Sˣ) → Hⁿ(Gal(Ω/K), Ωˣ)`, through `K_Sˣ`.
* `eq_zero_of_maximalSUnitsInflation_eq_zero`: it is injective on the `ℓ`-primary part in degree
  `2` (because `H¹(G_S, K_Sˣ/𝒪_Sˣ)` is killed by integers prime to `ℓ`).
* `brauerLocalization_maximalSUnitsInflation_eq_zero`: the image vanishes at every finite place
  outside `S`.
* `exists_maximalSUnitsInflation_eq`: every `ℓ`-primary Brauer class of `K` which vanishes at the
  finite places outside `S` is the image of an `ℓ`-primary class (the class dies in a totally complex
  subextension of `K_S`, so is inflated from `H²(G_S, K_Sˣ)`; its divisor class in `H²(G_S, D)`
  vanishes by the comparison of local classes and order classes, and the kernel of
  `H²(G_S, K_Sˣ/𝒪_Sˣ) → H²(G_S, D)` is killed by integers prime to `ℓ`).
* `maximalSUnitsPrimaryEquiv`: hence `H²(G_S, 𝒪_Sˣ)(ℓ)` is the group of `ℓ`-primary Brauer classes
  vanishing outside `S`; `existsUnique_maximalSUnitsInflation_localization` describes it by local
  classes at the places of `S` and the real places with sum of invariants zero (NSW (8.3.11) (iii)).
* `exists_prime_nsmul_eq_cohomology_two_maximalSUnits`: if `ℓ` is odd or `K` has no real place,
  `H²(G_S, 𝒪_Sˣ)` is `ℓ`-divisible.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open Langlands.ClassFieldTheory.Local Langlands.ClassFieldTheory.Global

universe u

noncomputable section

section Divisible

variable {G : Type*} [AddCommGroup G]

theorem exists_mul_add_mul_eq_one {a b : ℕ} (h : Nat.Coprime a b) :
    ∃ s t : ℤ, (a : ℤ) * s + (b : ℤ) * t = 1 :=
  ⟨Nat.gcdA a b, Nat.gcdB a b, by rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one h, Nat.cast_one]⟩

/-- In a torsion group, if every element killed by a power of the prime `ℓ` is divisible by `ℓ`, every
element is divisible by `ℓ`. -/
theorem exists_prime_nsmul_eq_of_primary {ℓ : ℕ} (hℓ : ℓ.Prime) (hG : ∀ y : G, IsOfFinAddOrder y)
    (h : ∀ y : G, (∃ k : ℕ, ℓ ^ k • y = 0) → ∃ y', ℓ • y' = y) (y : G) : ∃ y', ℓ • y' = y := by
  obtain ⟨a, N, hN, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (addOrderOf_pos_iff.2 (hG y)).ne' ℓ
    hℓ.ne_one
  have hcop' : Nat.Coprime ℓ N := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hN
  have hcop : Nat.Coprime (ℓ ^ a) N := Nat.Coprime.pow_left _ hcop'
  obtain ⟨s, t, hst⟩ := exists_mul_add_mul_eq_one hcop
  obtain ⟨s', t', hst'⟩ := exists_mul_add_mul_eq_one hcop'
  have hy0 : ((ℓ ^ a * N : ℕ) : ℤ) • y = 0 := by
    rw [natCast_zsmul, ← hn, addOrderOf_nsmul_eq_zero]
  obtain ⟨z₁, hz₁⟩ := h (((N : ℤ) * t) • y) ⟨a, by
    rw [← natCast_zsmul, smul_smul, show ((ℓ ^ a : ℕ) : ℤ) * (N * t) = t * ((ℓ ^ a * N : ℕ) : ℤ) by
      push_cast; ring, mul_smul, hy0, smul_zero]⟩
  have key : ((ℓ : ℤ) * (s' * (((ℓ ^ a : ℕ) : ℤ) * s))) • y = (((ℓ ^ a : ℕ) : ℤ) * s) • y := by
    have e : (ℓ : ℤ) * (s' * (((ℓ ^ a : ℕ) : ℤ) * s)) =
        ((ℓ ^ a : ℕ) : ℤ) * s - (s * t') * ((ℓ ^ a * N : ℕ) : ℤ) := by
      push_cast
      linear_combination ((ℓ : ℤ) ^ a * s) * hst'
    rw [e, sub_zsmul, mul_smul (s * t'), hy0, smul_zero]
    simp
  refine ⟨z₁ + (s' * (((ℓ ^ a : ℕ) : ℤ) * s)) • y, ?_⟩
  rw [smul_add, hz₁, ← natCast_zsmul, smul_smul, key, ← add_zsmul,
    show (N : ℤ) * t + ((ℓ ^ a : ℕ) : ℤ) * s = 1 by linear_combination hst, one_zsmul]

/-- In `ℚ/ℤ`, an element killed by `ℓ ^ k` is `ℓ` times an element killed by `ℓ ^ (k + 1)`, which may
be taken to be zero when the element is zero. -/
theorem exists_rationalModIntegers_nsmul_eq {ℓ : ℕ} (hℓ : ℓ ≠ 0) {k : ℕ} (r : RationalModIntegers)
    (hr : ℓ ^ k • r = 0) :
    ∃ r' : RationalModIntegers, ℓ • r' = r ∧ ℓ ^ (k + 1) • r' = 0 ∧ (r = 0 → r' = 0) := by
  classical
  by_cases h0 : r = 0
  · exact ⟨0, by rw [h0, smul_zero], smul_zero _, fun _ => rfl⟩
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk'_surjective _ r
  have h1 : ℓ • rationalClass (q / ℓ) = QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) q := by
    rw [← map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hℓ)]
    rfl
  refine ⟨rationalClass (q / ℓ), h1, ?_, fun h => absurd h h0⟩
  rw [pow_succ, ← smul_smul, h1, hr]

end Divisible

section RealTwo

variable {K : Type u} [Field K] [NumberField K]

/-- The local Brauer group at an infinite place is killed by `2`. -/
theorem two_nsmul_realBrauerGroup (w : InfinitePlace K) (b : RealBrauerGroup w) : 2 • b = 0 := by
  classical
  apply realInvariant_injective w
  rw [← realInvariantHom_apply, map_nsmul, realInvariantHom_apply, realInvariant_zero]
  unfold realInvariant
  split_ifs
  · exact smul_zero _
  · rw [← map_nsmul, show (2 • (1 / 2 : ℚ)) = 1 by norm_num]
    exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples 1)

/-- For `ℓ` odd, an `ℓ`-primary class of the local Brauer group at an infinite place is zero. -/
theorem eq_zero_realBrauerGroup_of_odd {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) (w : InfinitePlace K)
    (b : RealBrauerGroup w) {k : ℕ} (hb : ℓ ^ k • b = 0) : b = 0 :=
  eq_zero_of_coprime_nsmul_eq_zero (Nat.coprime_primes Nat.prime_two hℓ |>.2 h2.symm)
    (two_nsmul_realBrauerGroup w b) hb

end RealTwo

section Brauer

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K)))

variable (K Ω) in
/-- Inflation `Hⁿ(G_S, 𝒪_Sˣ) → Hⁿ(Gal(Ω/K), Ωˣ)`, through `K_Sˣ`. -/
def maximalSUnitsInflation (n : ℕ) :
    cohomology (maximalSUnitsModule K Ω S) n →+ cohomology (unitsModule K Ω) n :=
  (maximalUnitsInflation K Ω S n).comp
    (coeffMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) n).hom.toAddMonoidHom

theorem maximalSUnitsInflation_apply (n : ℕ) (y : cohomology (maximalSUnitsModule K Ω S) n) :
    maximalSUnitsInflation K Ω S n y = maximalUnitsInflation K Ω S n
      ((coeffMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) n).hom y) :=
  rfl

/-- The `S`-units have zero divisor. -/
theorem sUnitsToUnits_comp_unitsToSDivisor (ι : PlaceEmbeddings K Ω) :
    sUnitsToUnits S (maximalUnramifiedOutside K Ω S) ≫ unitsToSDivisor S ι = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact (unitsToSDivisor_eq_zero_iff S ι _).2 (Additive.toMul x).2

/-- The divisor map factors through `K_Sˣ/𝒪_Sˣ`. -/
theorem mkQ_comp_unitsModSUnitsToSDivisor (ι : PlaceEmbeddings K Ω) :
    (sUnitsQuotSequence K Ω S).g ≫ unitsModSUnitsToSDivisor S ι = unitsToSDivisor S ι := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

/-- **The image of `H²(G_S, 𝒪_Sˣ)` vanishes outside `S`.** -/
theorem brauerLocalization_maximalSUnitsInflation_eq_zero (ι : PlaceEmbeddings K Ω)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (y : cohomology (maximalSUnitsModule K Ω S) 2) :
    brauerLocalization ι v 2 (maximalSUnitsInflation K Ω S 2 y) = 0 := by
  refine (brauerLocalization_maximalUnitsInflation_eq_zero_iff S ι ⟨v, hv⟩ _).2 ?_
  have h : (coeffMap (unitsToSDivisor S ι) 2).hom
      ((coeffMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) 2).hom y) = 0 := by
    rw [← ModuleCat.comp_apply, ← coeffMap_comp, sUnitsToUnits_comp_unitsToSDivisor, coeffMap_zero]
    rfl
  have h' := congrArg (map (outsideLocalizationHom S ι ⟨v, hv⟩)
    (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) ⟨v, hv⟩) 2).hom h
  rw [map_zero] at h'
  exact h'

variable {ℓ : ℕ} (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)

include hℓ hS in
/-- **Injectivity on the `ℓ`-primary part.** A class of `H²(G_S, 𝒪_Sˣ)` killed by a power of `ℓ`
whose image in the Brauer group of `K` is zero is zero. -/
theorem eq_zero_of_maximalSUnitsInflation_eq_zero (y : cohomology (maximalSUnitsModule K Ω S) 2)
    {k : ℕ} (hy : ℓ ^ k • y = 0) (h : maximalSUnitsInflation K Ω S 2 y = 0) : y = 0 := by
  have h1 : (coeffMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) 2).hom y = 0 :=
    maximalUnitsInflation_two_injective S (h.trans (map_zero _).symm)
  have hS' := sUnitsQuotSequence_shortExact K Ω S
  obtain ⟨q, hq⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS' 1 2 rfl) y h1
  obtain ⟨N, hN, hNq⟩ := exists_coprime_nsmul_cohomology_one_unitsModSUnits S hℓ hS q
  have hq' : (δ hS' 1 2 rfl).hom q = y := hq
  refine eq_zero_of_coprime_nsmul_eq_zero hN ?_ hy
  rw [← hq']
  exact (map_nsmul (δ hS' 1 2 rfl).hom N q).symm.trans
    (by rw [show N • q = 0 from hNq, map_zero]; rfl)

include hℓ hS in
/-- **Surjectivity onto the `ℓ`-primary classes unramified outside `S`.** Every Brauer class of `K`
killed by a power of `ℓ` and vanishing at the finite places outside `S` is the image of a class of
`H²(G_S, 𝒪_Sˣ)` killed by a power of `ℓ`. -/
theorem exists_maximalSUnitsInflation_eq (ι : PlaceEmbeddings K Ω)
    (x : cohomology (unitsModule K Ω) 2) {k : ℕ} (hx : ℓ ^ k • x = 0)
    (hloc : ∀ v, v ∉ S → brauerLocalization ι v 2 x = 0) :
    ∃ y : cohomology (maximalSUnitsModule K Ω S) 2, (∃ j : ℕ, ℓ ^ j • y = 0) ∧
      maximalSUnitsInflation K Ω S 2 y = x := by
  classical
  -- `x` dies in a totally complex subextension of `K_S`
  obtain ⟨hfin, -⟩ := localInvariant_finite_support_and_sum_eq_zero ι x
  obtain ⟨E, _, hES, hEc, hEdeg⟩ :=
    exists_isComplex_le_maximalUnramifiedOutside (Ω := Ω) S hℓ hS hfin.toFinset k
  have hres : brauerRestriction E x = 0 := by
    refine brauerRestriction_eq_zero_of_isComplex ι E hEc x (ℓ ^ k) hx fun v hv w _ =>
      hEdeg v ?_ w
    rw [Set.Finite.mem_toFinset, Function.mem_support, Ne, localInvariant_eq_zero_iff]
    exact hv
  obtain ⟨z, rfl⟩ := exists_maximalUnitsInflation_eq S E hES x hres
  have hz : ℓ ^ k • z = 0 :=
    maximalUnitsInflation_two_injective S (by rw [map_nsmul, hx, map_zero])
  -- the divisor class of `z` vanishes
  have hD : (coeffMap (unitsToSDivisor S ι) 2).hom z = 0 := by
    have hcd : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        CompactSpace Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K) ∧
          TotallyDisconnectedSpace
            Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K) := fun v => by
      have : CharZero (v.1.adicCompletion K) := charZero_adicCompletion v.1
      have : IsGalois (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)) :=
        IsGalois.mk
      exact ⟨(galois_isProfinite _ _).1, (galois_isProfinite _ _).2.2⟩
    have := fun v => (hcd v).1
    have := fun v => (hcd v).2
    exact eq_zero_of_divisorEval_eq_zero (outsideLocalizationHom S ι) _ fun v =>
      (brauerLocalization_maximalUnitsInflation_eq_zero_iff S ι v z).1 (hloc v.1 v.2)
  -- hence its class in `H²(G_S, K_Sˣ/𝒪_Sˣ)` is killed by an integer prime to `ℓ`, so is zero
  have hQ : (coeffMap (sUnitsQuotSequence K Ω S).g 2).hom z = 0 := by
    have h1 : (coeffMap (unitsModSUnitsToSDivisor S ι) 2).hom
        ((coeffMap (sUnitsQuotSequence K Ω S).g 2).hom z) = 0 := by
      rw [← hD, ← mkQ_comp_unitsModSUnitsToSDivisor S ι]
      exact (congrArg (fun F => F.hom z) (coeffMap_comp (sUnitsQuotSequence K Ω S).g
        (unitsModSUnitsToSDivisor S ι) 2)).symm
    obtain ⟨N, hN, hNq⟩ := exists_coprime_nsmul_of_coeffMap_sDivisor_eq_zero S ι hℓ hS _ h1
    have e : ℓ ^ k • (coeffMap (sUnitsQuotSequence K Ω S).g 2).hom z = 0 :=
      (map_nsmul (coeffMap (sUnitsQuotSequence K Ω S).g 2).hom (ℓ ^ k) z).symm.trans
        ((congrArg (coeffMap (sUnitsQuotSequence K Ω S).g 2).hom hz).trans (map_zero _))
    exact eq_zero_of_coprime_nsmul_eq_zero hN hNq e
  obtain ⟨y₀, hy₀⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (cohomology_exact₂ (sUnitsQuotSequence_shortExact K Ω S) 2) z hQ
  have hy₀' : (coeffMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) 2).hom y₀ = z := hy₀
  -- an `ℓ`-primary preimage
  obtain ⟨y, hy, hyz⟩ := exists_primary_map_eq
    (coeffMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) 2).hom.toAddMonoidHom hℓ
    (isTorsion_cohomology (maximalSUnitsModule K Ω S) (by norm_num) y₀) (k := k)
    (by
      have e : (coeffMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) 2).hom.toAddMonoidHom y₀ =
        z := hy₀'
      rw [e]
      exact hz)
  refine ⟨y, hy, ?_⟩
  rw [maximalSUnitsInflation_apply]
  change maximalUnitsInflation K Ω S 2
    ((coeffMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) 2).hom.toAddMonoidHom y) = _
  rw [hyz]
  exact congrArg _ hy₀'

/-- The `ℓ`-primary Brauer classes of `K` which vanish at every finite place outside `S`. -/
def brauerPrimaryOutside (ι : PlaceEmbeddings K Ω) (ℓ : ℕ) :
    AddSubgroup (cohomology (unitsModule K Ω) 2) where
  carrier := {x | (∃ k : ℕ, ℓ ^ k • x = 0) ∧ ∀ v, v ∉ S → brauerLocalization ι v 2 x = 0}
  add_mem' {a b} ha hb := by
    obtain ⟨⟨m, hm⟩, ha'⟩ := ha
    obtain ⟨⟨n, hn⟩, hb'⟩ := hb
    refine ⟨⟨m + n, ?_⟩, fun v hv => ?_⟩
    · have h1 : ℓ ^ (m + n) • a = 0 := by rw [pow_add, mul_comm, ← smul_smul, hm, smul_zero]
      have h2 : ℓ ^ (m + n) • b = 0 := by rw [pow_add, ← smul_smul, hn, smul_zero]
      rw [smul_add, h1, h2, add_zero]
    · rw [map_add, ha' v hv, hb' v hv, add_zero]
  zero_mem' := ⟨⟨0, smul_zero _⟩, fun v _ => map_zero _⟩
  neg_mem' {a} ha := by
    obtain ⟨⟨m, hm⟩, ha'⟩ := ha
    exact ⟨⟨m, by rw [smul_neg, hm, neg_zero]⟩, fun v hv => by rw [map_neg, ha' v hv, neg_zero]⟩

theorem mem_brauerPrimaryOutside (ι : PlaceEmbeddings K Ω) (ℓ : ℕ)
    (x : cohomology (unitsModule K Ω) 2) :
    x ∈ brauerPrimaryOutside S ι ℓ ↔
      (∃ k : ℕ, ℓ ^ k • x = 0) ∧ ∀ v, v ∉ S → brauerLocalization ι v 2 x = 0 :=
  Iff.rfl

/-- `maximalSUnitsInflation` on the `ℓ`-primary component. -/
def maximalSUnitsInflationPrimary (ι : PlaceEmbeddings K Ω) (ℓ : ℕ) :
    AddCommGroup.primaryComponent (cohomology (maximalSUnitsModule K Ω S) 2) ℓ →+
      brauerPrimaryOutside S ι ℓ :=
  ((maximalSUnitsInflation K Ω S 2).comp
    (AddCommGroup.primaryComponent _ ℓ).subtype).codRestrict _ fun y => by
    obtain ⟨k, hk⟩ := y.2
    refine ⟨⟨k, ?_⟩, fun v hv => brauerLocalization_maximalSUnitsInflation_eq_zero S ι hv y.1⟩
    change ℓ ^ k • maximalSUnitsInflation K Ω S 2 y.1 = 0
    rw [← map_nsmul, hk, map_zero]

include hℓ hS in
theorem bijective_maximalSUnitsInflationPrimary (ι : PlaceEmbeddings K Ω) :
    Function.Bijective (maximalSUnitsInflationPrimary S ι ℓ) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun x => ?_⟩
  · obtain ⟨m, hm⟩ := a.2
    exact Subtype.ext (eq_zero_of_maximalSUnitsInflation_eq_zero S hℓ hS a.1 hm
      (congrArg Subtype.val ha))
  · obtain ⟨⟨k, hk⟩, hx⟩ := x.2
    obtain ⟨y, hy, hyx⟩ := exists_maximalSUnitsInflation_eq S hℓ hS ι x.1 hk hx
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩

/-- **`H²` of the `S`-units.** The `ℓ`-primary part of `H²(G_S, 𝒪_Sˣ)` is the group of `ℓ`-primary
Brauer classes of `K` vanishing at every finite place outside `S`. -/
def maximalSUnitsPrimaryEquiv (ι : PlaceEmbeddings K Ω) :
    AddCommGroup.primaryComponent (cohomology (maximalSUnitsModule K Ω S) 2) ℓ ≃+
      brauerPrimaryOutside S ι ℓ :=
  AddEquiv.ofBijective _ (bijective_maximalSUnitsInflationPrimary S hℓ hS ι)

theorem coe_maximalSUnitsPrimaryEquiv_apply (ι : PlaceEmbeddings K Ω)
    (y : AddCommGroup.primaryComponent (cohomology (maximalSUnitsModule K Ω S) 2) ℓ) :
    (maximalSUnitsPrimaryEquiv S hℓ hS ι y : cohomology (unitsModule K Ω) 2) =
      maximalSUnitsInflation K Ω S 2 y :=
  rfl

include hℓ hS in
/-- **`H²(G_S, 𝒪_Sˣ)(ℓ)` by local classes.** For local classes `a v` at the finite places (zero
outside `S`, finitely many nonzero) and `b w` at the infinite places, all killed by a power of `ℓ`, with
sum of invariants zero, there is exactly one `ℓ`-primary class of `H²(G_S, 𝒪_Sˣ)` whose image in the
Brauer group of `K` has these localizations. -/
theorem existsUnique_maximalSUnitsInflation_localization (ι : PlaceEmbeddings K Ω)
    (a : ∀ v : HeightOneSpectrum (𝓞 K), LocalBrauerGroup v) (b : ∀ w : InfinitePlace K, RealBrauerGroup w)
    (ha : {v | a v ≠ 0}.Finite) (haS : ∀ v, v ∉ S → a v = 0) {k : ℕ}
    (hak : ∀ v, ℓ ^ k • a v = 0) (hbk : ∀ w, ℓ ^ k • b w = 0)
    (hab : ∑ᶠ v, finiteInvariant v (a v) + ∑ w, realInvariant w (b w) = 0) :
    ∃! y : AddCommGroup.primaryComponent (cohomology (maximalSUnitsModule K Ω S) 2) ℓ,
      (∀ v, brauerLocalization ι v 2 (maximalSUnitsInflation K Ω S 2 y) = a v) ∧
        ∀ w, realBrauerLocalization ι w 2 (maximalSUnitsInflation K Ω S 2 y) = b w := by
  obtain ⟨x, ⟨hxa, hxb⟩, -⟩ := existsUnique_brauerLocalization_eq' ι a b ha hab
  have hxk : ℓ ^ k • x = 0 := eq_zero_of_brauerLocalization_eq_zero' ι _
    (fun v => by rw [map_nsmul, hxa v, hak v]) (fun w => by rw [map_nsmul, hxb w, hbk w])
  have hx : x ∈ brauerPrimaryOutside S ι ℓ := ⟨⟨k, hxk⟩, fun v hv => (hxa v).trans (haS v hv)⟩
  obtain ⟨y, hy⟩ := (bijective_maximalSUnitsInflationPrimary S hℓ hS ι).2 ⟨x, hx⟩
  have hy' : maximalSUnitsInflation K Ω S 2 y = x := congrArg Subtype.val hy
  refine ⟨y, ⟨fun v => by rw [hy', hxa v], fun w => by rw [hy', hxb w]⟩, fun y' hy'' => ?_⟩
  apply (bijective_maximalSUnitsInflationPrimary S hℓ hS ι).1
  apply Subtype.ext
  change maximalSUnitsInflation K Ω S 2 y' = maximalSUnitsInflation K Ω S 2 y
  rw [hy']
  refine sub_eq_zero.1 (eq_zero_of_brauerLocalization_eq_zero' ι _ (fun v => ?_) (fun w => ?_))
  · rw [map_sub, hy''.1 v, hxa v, sub_self]
  · rw [map_sub, hy''.2 w, hxb w, sub_self]

include hℓ hS in
/-- **Divisibility.** If `ℓ` is odd or `K` has no real place, every class of `H²(G_S, 𝒪_Sˣ)` is
divisible by `ℓ`. -/
theorem exists_prime_nsmul_eq_cohomology_two_maximalSUnits (hK : ℓ ≠ 2 ∨ IsTotallyComplex K)
    (y : cohomology (maximalSUnitsModule K Ω S) 2) : ∃ y', ℓ • y' = y := by
  classical
  let ι : PlaceEmbeddings K Ω := Classical.arbitrary _
  refine exists_prime_nsmul_eq_of_primary hℓ
    (isTorsion_cohomology (maximalSUnitsModule K Ω S) (by norm_num)) (fun y₁ ⟨k, hk⟩ => ?_) y
  set x := maximalSUnitsInflation K Ω S 2 y₁ with hxdef
  have hxk : ℓ ^ k • x = 0 := by rw [hxdef, ← map_nsmul, hk, map_zero]
  -- the real components of `x` vanish
  have hreal : ∀ w, realBrauerLocalization ι w 2 x = 0 := by
    intro w
    rcases hK with h2 | hc
    · exact eq_zero_realBrauerGroup_of_odd hℓ h2 w _ (k := k) (by rw [← map_nsmul, hxk, map_zero])
    · have := subsingleton_realBrauerGroup_of_isComplex w (hc.isComplex w)
      exact Subsingleton.elim _ _
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [smul_zero]; exact (eq_zero_of_maximalSUnitsInflation_eq_zero S hℓ hS y₁ hk hx0).symm⟩
  -- a finite place where `x` is nonzero; it lies in `S`
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, brauerLocalization ι v₀ 2 x ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hx0 (eq_zero_of_brauerLocalization_eq_zero' ι x hne hreal)
  have hv₀S : v₀ ∈ S := by
    by_contra h
    exact hv₀ (brauerLocalization_maximalSUnitsInflation_eq_zero S ι h y₁)
  -- divide the local invariants by `ℓ`, keeping the sum zero
  let r : HeightOneSpectrum (𝓞 K) → RationalModIntegers := fun v => localInvariant ι v x
  have hrk : ∀ v, ℓ ^ k • r v = 0 := fun v => by
    simp only [r]
    rw [← map_nsmul, hxk, map_zero]
  choose r' hr'1 hr'2 hr'3 using fun v => exists_rationalModIntegers_nsmul_eq hℓ.ne_zero (r v) (hrk v)
  obtain ⟨hfin, hsum⟩ := localInvariant_finite_support_and_sum_eq_zero ι x
  have hreal' : ∑ w, realLocalInvariant ι w x = 0 :=
    Finset.sum_eq_zero fun w _ => by rw [realLocalInvariant, hreal w, realInvariant_zero]
  rw [hreal', add_zero] at hsum
  have hfin' : (Function.support r').Finite := hfin.subset fun v hv h0 => hv (hr'3 v h0)
  set c := ∑ᶠ v, r' v with hc
  have hcℓ : ℓ • c = 0 := by
    rw [hc, smul_finsum' ℓ hfin']
    simp only [hr'1]
    exact hsum
  let δ₀ : HeightOneSpectrum (𝓞 K) → RationalModIntegers := fun v => if v = v₀ then c else 0
  have hδfin : (Function.support δ₀).Finite :=
    (Set.finite_singleton v₀).subset fun v hv => by
      by_contra h
      exact hv (ite_eq_right_of_eq_false _ _ (eq_false h))
  let r'' : HeightOneSpectrum (𝓞 K) → RationalModIntegers := fun v => r' v - δ₀ v
  have hfin'' : (Function.support r'').Finite :=
    (hfin'.union hδfin).subset (Function.support_sub _ _)
  have hsum'' : ∑ᶠ v, r'' v = 0 := by
    rw [finsum_sub_distrib hfin' hδfin, finsum_eq_single δ₀ v₀ fun v hv => ite_eq_right_of_eq_false _ _ (eq_false hv), ← hc]
    simp [δ₀]
  have hδℓ : ∀ v, ℓ • δ₀ v = 0 := fun v => by
    simp only [δ₀]
    split_ifs
    · exact hcℓ
    · exact smul_zero _
  obtain ⟨x', hx'1, hx'2⟩ := exists_localInvariant_eq ι r'' hfin'' hsum''
  -- `ℓ x' = x`
  have hℓx' : ℓ • x' = x := by
    refine sub_eq_zero.1 (eq_zero_of_brauerLocalization_eq_zero' ι _ (fun v => ?_) (fun w => ?_))
    · rw [← localInvariant_eq_zero_iff, map_sub, map_nsmul, hx'1 v]
      simp only [r'', smul_sub, hr'1, hδℓ, sub_zero, r, sub_self]
    · rw [map_sub, map_nsmul, hx'2 w, hreal w, smul_zero, sub_zero]
  -- `x'` is killed by `ℓ ^ (k + 1)` and vanishes outside `S`
  have hx'k : ℓ ^ (k + 1) • x' = 0 := by
    refine eq_zero_of_brauerLocalization_eq_zero' ι _ (fun v => ?_) (fun w => ?_)
    · rw [← localInvariant_eq_zero_iff, map_nsmul, hx'1 v]
      simp only [r'', smul_sub, hr'2, zero_sub, neg_eq_zero]
      rw [pow_succ, ← smul_smul, hδℓ, smul_zero]
    · rw [map_nsmul, hx'2 w, smul_zero]
  have hx'S : ∀ v, v ∉ S → brauerLocalization ι v 2 x' = 0 := by
    intro v hv
    rw [← localInvariant_eq_zero_iff, hx'1 v]
    have hrv : r v = 0 := by
      simp only [r]
      rw [localInvariant_eq_zero_iff]
      exact brauerLocalization_maximalSUnitsInflation_eq_zero S ι hv y₁
    have hvv : v ≠ v₀ := fun h => hv (h ▸ hv₀S)
    simp only [r'', δ₀, hvv, ↓reduceIte, hr'3 v hrv, sub_zero]
  obtain ⟨y', ⟨j, hj⟩, hy'⟩ := exists_maximalSUnitsInflation_eq S hℓ hS ι x' hx'k hx'S
  refine ⟨y', sub_eq_zero.1 (eq_zero_of_maximalSUnitsInflation_eq_zero S hℓ hS _ (k := j + k) ?_ ?_)⟩
  · have h1 : ℓ ^ (j + k) • ℓ • y' = 0 := by
      rw [smul_comm, pow_add, mul_comm, ← smul_smul, hj, smul_zero, smul_zero]
    have h2 : ℓ ^ (j + k) • y₁ = 0 := by rw [pow_add, ← smul_smul, hk, smul_zero]
    rw [smul_sub, h1, h2, sub_zero]
  · rw [map_sub, map_nsmul, hy', hℓx', sub_self]

end Brauer

end

end Langlands.GaloisCohomology
