import Langlands.Global.Arithmetic.AuxiliaryPrimes
import Langlands.Global.Arithmetic.IdeleSUnits
import Langlands.Global.Arithmetic.KummerNormLift
import Langlands.Global.AdelicFunctoriality.IdeleClassCyclotomicSecondInequalityStatement
import Langlands.ClassField.Global.CyclicIdeleClassHerbrandQuotientStatement
import Langlands.ClassField.Global.CyclicH2NormIndexComparisonProof
import Langlands.ClassField.Global.IdeleClassNormGaloisProductProof
import Mathlib.FieldTheory.KummerExtension

/-! # The second inequality for Kummer extensions of prime degree -/

namespace Langlands.Global.Arithmetic.KummerSecondInequality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial
open Langlands.ClassField.Global Langlands.Global.AdelicFunctoriality
  Langlands.Global.Arithmetic.SUnitIndex Langlands.Global.Arithmetic.KummerRadical
  Langlands.Global.Arithmetic.IdeleSUnits Langlands.Global.Arithmetic.AuxiliaryPrimes
  Langlands.Global.Arithmetic.KummerNormLift
open scoped NumberField

universe u

/-- A divisor of a power of the prime `p` that is at most `p` divides `p`. -/
theorem dvd_of_dvd_pow_of_le {p n r : ℕ} (hp : p.Prime) (hn : n ∣ p ^ r) (hle : n ≤ p) :
    n ∣ p := by
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hn
  rcases j with - | - | j
  · simp
  · simp
  · exfalso
    have h : p ^ 1 < p ^ (j + 1 + 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
    rw [pow_one] at h
    omega

section Places

variable {K : Type*} [Field K] [NumberField K]

/-- An element of `Kˣ` has valuation one at all but finitely many finite places. -/
theorem finite_valuation_ne_one (x : Kˣ) :
    {v : HeightOneSpectrum (𝓞 K) | v.valuation K (x : K) ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (R := 𝓞 K) (x : K)).union
    (HeightOneSpectrum.Support.finite (R := 𝓞 K) ((x : K)⁻¹))).subset ?_
  intro v hv
  rcases (Ne.lt_or_gt hv) with h | h
  · right
    show 1 < v.valuation K (x : K)⁻¹
    have hx0 : v.valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
    rw [map_inv₀]
    exact one_lt_inv₀ (zero_lt_iff.2 hx0) |>.2 h
  · left
    exact h

/-- `p` is a unit in `O_v` when its valuation is one. -/
theorem isUnit_natCast_of_valuation_eq_one (v : HeightOneSpectrum (𝓞 K)) (p : ℕ)
    (h : v.valuation K (p : K) = 1) : IsUnit (p : v.adicCompletionIntegers K) := by
  rw [(adicCompletionIntegers.integers K v).isUnit_iff_valuation_eq_one, map_natCast,
    ← map_natCast (algebraMap K (v.adicCompletion K)) p]
  exact (valuedAdicCompletion_eq_valuation' v (p : K)).trans h

/-- **Choice of `S₁`.** There is a finite set of finite places with global uniformizers, outside
which `p` is a unit and `a` has valuation one. -/
theorem exists_initialPlaces (p : ℕ) (hp : p ≠ 0) (a : Kˣ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), HasGlobalUniformizers K S ∧
      (∀ v ∉ S, IsUnit (p : v.adicCompletionIntegers K)) ∧ a ∈ sUnits K S := by
  classical
  have hp' : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp
  have hfin := (finite_valuation_ne_one a).union (finite_valuation_ne_one (Units.mk0 _ hp'))
  obtain ⟨S, hS₀, hS⟩ := exists_hasGlobalUniformizers K hfin.toFinset
  refine ⟨S, hS, fun v hv => ?_, fun v hv => ?_⟩
  · apply isUnit_natCast_of_valuation_eq_one
    by_contra h
    exact hv (hS₀ (hfin.mem_toFinset.2 (Or.inr h)))
  · by_contra h
    exact hv (hS₀ (hfin.mem_toFinset.2 (Or.inl h)))

end Places

section PowerClasses

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- The product of the groups `K_vˣ / K_vˣ^p` over the finite places `v ∈ S` and of the groups
`K_wˣ / K_wˣ^p` over all infinite places `w`, as a plain product type. -/
abbrev PowerClassProd (S : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) : Type _ :=
  (∀ v : S, (v.1.adicCompletion K)ˣ ⧸ localPowers v.1 p) ×
    (∀ w : InfinitePlace K, (w.Completion)ˣ ⧸ infiniteUnitPowers w p)

variable (K) in
/-- The group `∏_{v ∈ S} K_vˣ / K_vˣ^p × ∏_{w ∣ ∞} K_wˣ / K_wˣ^p`. It is a type synonym of
`PowerClassProd K S p` carrying a single commutative group structure. -/
def PowerClassGroup (S : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) : Type _ :=
  PowerClassProd K S p

noncomputable instance (S : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) :
    CommGroup (PowerClassGroup K S p) :=
  inferInstanceAs (CommGroup (PowerClassProd K S p))

variable (K) in
/-- The classes modulo local `p`-th powers of the coordinates of an idele at the finite places of
`S` and at all infinite places. -/
noncomputable def powerClasses (S : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) :
    IdeleGroup (𝓞 K) K →* PowerClassGroup K S p :=
  (MonoidHom.prod (MonoidHom.pi fun v => (QuotientGroup.mk' _).comp (ideleCoordinate v.1))
    (MonoidHom.pi fun w => (QuotientGroup.mk' _).comp (ideleInfiniteCoordinate w)) :
      IdeleGroup (𝓞 K) K →* PowerClassProd K S p)

theorem powerClasses_fst (S : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ)
    (x : IdeleGroup (𝓞 K) K) (v : S) :
    (powerClasses K S p x : PowerClassProd K S p).1 v = QuotientGroup.mk (ideleCoordinate v.1 x) :=
  rfl

theorem powerClasses_snd (S : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ)
    (x : IdeleGroup (𝓞 K) K) (w : InfinitePlace K) :
    (powerClasses K S p x : PowerClassProd K S p).2 w =
      QuotientGroup.mk (ideleInfiniteCoordinate w x) :=
  rfl

theorem powerClasses_eq_one_iff {S : Finset (HeightOneSpectrum (𝓞 K))} {p : ℕ}
    {x : IdeleGroup (𝓞 K) K} :
    powerClasses K S p x = 1 ↔ (∀ v ∈ S, ideleCoordinate v x ∈ localPowers v p) ∧
      ∀ w, ideleInfiniteCoordinate w x ∈ infiniteUnitPowers w p := by
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun w => ?_⟩
    · have h1 : (QuotientGroup.mk (ideleCoordinate v x) :
          (v.adicCompletion K)ˣ ⧸ localPowers v p) = 1 :=
        congrArg (fun y : PowerClassProd K S p => y.1 ⟨v, hv⟩) h
      exact (QuotientGroup.eq_one_iff _).1 h1
    · have h2 : (QuotientGroup.mk (ideleInfiniteCoordinate w x) :
          (w.Completion)ˣ ⧸ infiniteUnitPowers w p) = 1 :=
        congrArg (fun y : PowerClassProd K S p => y.2 w) h
      exact (QuotientGroup.eq_one_iff _).1 h2
  · rintro ⟨h1, h2⟩
    have h : (powerClasses K S p x : PowerClassProd K S p) = (1 : PowerClassProd K S p) :=
      Prod.ext (funext fun v => (QuotientGroup.eq_one_iff _).2 (h1 v.1 v.2))
        (funext fun w => (QuotientGroup.eq_one_iff _).2 (h2 w))
    exact h

/-- The group `PowerClassGroup K S p` is finite when `K` contains a primitive `p`-th root of
unity. -/
theorem finite_powerClassGroup {p : ℕ} [hp : Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : Finite (PowerClassGroup K S p) := by
  have h1 : ∀ v : S, Finite ((v.1.adicCompletion K)ˣ ⧸ localPowers v.1 p) := fun v => by
    have := localPowers_finiteIndex v.1 p hp.out.ne_zero
    infer_instance
  have h2 : ∀ w : InfinitePlace K, Finite ((w.Completion)ˣ ⧸ infiniteUnitPowers w p) := by
    intro w
    rcases w.isReal_or_isComplex with hw | hw
    · have h := eq_two_of_isReal hζ w hw
      subst h
      have := infiniteUnitPowers_two_finiteIndex w hw
      infer_instance
    · rw [infiniteUnitPowers_eq_top_of_isComplex w hw p hp.out.ne_zero]
      infer_instance
  have h : Finite (PowerClassProd K S p) := inferInstance
  exact h

/-- `|PowerClassGroup K S p| ≤ p ^ (2 (|S| + |S_∞|))`. -/
theorem card_powerClassGroup_le (S : Finset (HeightOneSpectrum (𝓞 K))) {p : ℕ}
    [hp : Fact p.Prime] :
    Nat.card (PowerClassGroup K S p) ≤ p ^ (2 * (S.card + Fintype.card (InfinitePlace K))) := by
  change Nat.card (PowerClassProd K S p) ≤ _
  rw [Nat.card_prod, Nat.card_pi, Nat.card_pi]
  have h := prod_index_localPowers_le S p hp.out.two_le
  rw [← Finset.prod_coe_sort S] at h
  exact h

end PowerClasses

section Count

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
variable (K) in
/-- The group `D₂` of Artin–Tate: ideles that are units outside `S₁ ∪ T` and local `p`-th powers
at the finite places of `S₁` and at all infinite places. -/
noncomputable def kummerSubgroup (S₁ T : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) :
    Subgroup (IdeleGroup (𝓞 K) K) :=
  sUnitIdeles K (S₁ ∪ T) ⊓ (powerClasses K S₁ p).ker

open scoped Classical in
variable (K) in
/-- The local power classes of the `(S₁ ∪ T)`-units at the finite places of `S₁` and at the
infinite places. -/
noncomputable def sUnitPowerClasses (S₁ T : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) :
    sUnits K (S₁ ∪ T) →* PowerClassGroup K S₁ p :=
  (powerClasses K S₁ p).comp ((IdeleGroup.unitEmbedding (𝓞 K) K).comp (sUnits K (S₁ ∪ T)).subtype)

open scoped Classical in
variable (K) in
/-- The subgroup of local power classes of `(S₁ ∪ T)`-units. -/
noncomputable abbrev sUnitPowerClassRange (S₁ T : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) :
    Subgroup (PowerClassGroup K S₁ p) :=
  MonoidHom.range (G := sUnits K (S₁ ∪ T)) (N := PowerClassGroup K S₁ p)
    (sUnitPowerClasses K S₁ T p)

open scoped Classical in
/-- An idele of `J^{S₁ ∪ T}` lies in `K^× D₂` iff its local power classes are those of an
`(S₁ ∪ T)`-unit. -/
theorem principal_sup_kummerSubgroup_subgroupOf (S₁ T : Finset (HeightOneSpectrum (𝓞 K)))
    (p : ℕ) :
    (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ kummerSubgroup K S₁ T p).subgroupOf
        (sUnitIdeles K (S₁ ∪ T)) =
      Subgroup.comap (G := sUnitIdeles K (S₁ ∪ T)) (N := PowerClassGroup K S₁ p)
        ((powerClasses K S₁ p).comp (sUnitIdeles K (S₁ ∪ T)).subtype)
        (sUnitPowerClassRange K S₁ T p) := by
  ext ⟨x, hx⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  change x ∈ _ ↔ ∃ e, sUnitPowerClasses K S₁ T p e = powerClasses K S₁ p x
  constructor
  · intro hxPD
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hxPD
    obtain ⟨a, rfl⟩ := hy
    have hzD := Subgroup.mem_inf.1 hz
    have haS : a ∈ sUnits K (S₁ ∪ T) := by
      rw [← unitEmbedding_mem_sUnitIdeles_iff]
      have h := (sUnitIdeles K (S₁ ∪ T)).mul_mem hx ((sUnitIdeles K (S₁ ∪ T)).inv_mem hzD.1)
      rwa [mul_inv_cancel_right] at h
    refine ⟨⟨a, haS⟩, ?_⟩
    change powerClasses K S₁ p (IdeleGroup.unitEmbedding (𝓞 K) K a) = _
    rw [map_mul, MonoidHom.mem_ker.1 hzD.2, mul_one]
  · rintro ⟨e, he⟩
    have heS : IdeleGroup.unitEmbedding (𝓞 K) K e ∈ sUnitIdeles K (S₁ ∪ T) :=
      (unitEmbedding_mem_sUnitIdeles_iff _).2 e.2
    have hd : (IdeleGroup.unitEmbedding (𝓞 K) K e)⁻¹ * x ∈ kummerSubgroup K S₁ T p := by
      refine Subgroup.mem_inf.2
        ⟨(sUnitIdeles K (S₁ ∪ T)).mul_mem ((sUnitIdeles K (S₁ ∪ T)).inv_mem heS) hx, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      change (sUnitPowerClasses K S₁ T p e)⁻¹ * powerClasses K S₁ p x = 1
      rw [he, inv_mul_cancel]
    have h := Subgroup.mul_mem_sup (S := IdeleGroup.principalSubgroup (𝓞 K) K)
      (MonoidHom.mem_range.2 ⟨e, rfl⟩) hd
    rwa [mul_inv_cancel_left] at h

open scoped Classical in
/-- Since `J_K = K^× J^{S₁}`, the index of `K^× D₂` in `J_K` equals its index in
`J^{S₁ ∪ T}`. -/
theorem index_principal_sup_kummerSubgroup {S₁ : Finset (HeightOneSpectrum (𝓞 K))}
    (hS₁ : HasGlobalUniformizers K S₁) (T : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) :
    (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ kummerSubgroup K S₁ T p).index =
      ((IdeleGroup.principalSubgroup (𝓞 K) K ⊔ kummerSubgroup K S₁ T p).subgroupOf
        (sUnitIdeles K (S₁ ∪ T))).index := by
  have hsup : sUnitIdeles K (S₁ ∪ T) ⊔
      (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ kummerSubgroup K S₁ T p) = ⊤ := by
    rw [eq_top_iff, ← principal_sup_sUnitIdeles (hS₁.mono Finset.subset_union_left)]
    exact sup_le (le_sup_of_le_right le_sup_left) le_sup_left
  change _ = Subgroup.relIndex _ (sUnitIdeles K (S₁ ∪ T))
  rw [← Subgroup.relIndex_sup_right, hsup, Subgroup.relIndex_top_right]

open scoped Classical in
/-- **The index count** (Artin–Tate, Chapter VI §3, Lemma 2 for `S = S₁ ∪ T`). If the `S`-units
that are local `p`-th powers at `S₁` and at the infinite places are global `p`-th powers, then
`J_K / K^× D₂` is finite of order at most `p`. -/
theorem index_principal_sup_le {p : ℕ} [hp : Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {S₁ T : Finset (HeightOneSpectrum (𝓞 K))} (hS₁ : HasGlobalUniformizers K S₁)
    (hdisj : Disjoint S₁ T) (hcard : T.card + 1 = S₁.card + Fintype.card (InfinitePlace K))
    (hpow : (sUnitPowerClasses K S₁ T p).ker ≤
      (powMonoidHom p : sUnits K (S₁ ∪ T) →* sUnits K (S₁ ∪ T)).range) :
    (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ kummerSubgroup K S₁ T p).index ≠ 0 ∧
      (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ kummerSubgroup K S₁ T p).index ≤ p := by
  have hQ := finite_powerClassGroup hζ S₁
  have hrel : (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ kummerSubgroup K S₁ T p).index ∣
      (sUnitPowerClassRange K S₁ T p).index := by
    rw [index_principal_sup_kummerSubgroup hS₁, principal_sup_kummerSubgroup_subgroupOf,
      Subgroup.index_comap]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  have hmul := (sUnitPowerClassRange K S₁ T p).index_mul_card
  have hQ0 : Nat.card (PowerClassGroup K S₁ p) ≠ 0 := Nat.card_pos.ne'
  have hidx0 : (sUnitPowerClassRange K S₁ T p).index ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact hQ0 hmul.symm
  have hrange : p ^ ((S₁ ∪ T).card + Fintype.card (InfinitePlace K)) ≤
      Nat.card (sUnitPowerClassRange K S₁ T p) := by
    rw [← Subgroup.index_ker (sUnitPowerClasses K S₁ T p)]
    have hne : (sUnitPowerClasses K S₁ T p).ker.index ≠ 0 := by
      rw [Subgroup.index_ker (sUnitPowerClasses K S₁ T p)]
      exact Nat.card_pos.ne'
    rw [← index_pow_sUnits K (S₁ ∪ T) p hζ]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Subgroup.index_dvd_of_le hpow)
  have hScard : (S₁ ∪ T).card = S₁.card + T.card := Finset.card_union_of_disjoint hdisj
  have h2 : (sUnitPowerClassRange K S₁ T p).index *
        p ^ ((S₁ ∪ T).card + Fintype.card (InfinitePlace K)) ≤
      p * p ^ ((S₁ ∪ T).card + Fintype.card (InfinitePlace K)) :=
    calc (sUnitPowerClassRange K S₁ T p).index *
          p ^ ((S₁ ∪ T).card + Fintype.card (InfinitePlace K))
        ≤ (sUnitPowerClassRange K S₁ T p).index *
            Nat.card (sUnitPowerClassRange K S₁ T p) := Nat.mul_le_mul_left _ hrange
      _ = Nat.card (PowerClassGroup K S₁ p) := hmul
      _ ≤ p ^ (2 * (S₁.card + Fintype.card (InfinitePlace K))) := card_powerClassGroup_le S₁
      _ = p * p ^ ((S₁ ∪ T).card + Fintype.card (InfinitePlace K)) := by
        rw [← pow_succ']
        congr 1
        omega
  have hfr : (sUnitPowerClassRange K S₁ T p).index ≤ p :=
    Nat.le_of_mul_le_mul_right h2 (pow_pos hp.out.pos _)
  refine ⟨fun h => hidx0 (Nat.eq_zero_of_zero_dvd (h ▸ hrel)), ?_⟩
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hidx0) hrel).trans hfr

end Count

section PowerLocalGlobal

open scoped Classical in
/-- **Step (iii)** (Artin–Tate, Chapter VI §3, Lemma 2). Let `S₁` have global uniformizers, let
`p` be a unit outside `S₁`, and let `T` be a set of auxiliary primes as produced by
`exists_auxiliaryPrimes`. Assume the first inequality in the form of
`CyclicIdeleClassHerbrandQuotient` and Galois descent for idele classes. Then an
`(S₁ ∪ T)`-unit that is a local `p`-th power at the finite places of `S₁` and at all infinite
places is a `p`-th power of an `(S₁ ∪ T)`-unit. -/
theorem mem_range_pow_of_powerClasses_eq_one (hdescent : IdeleClassGaloisDescent.{u, u})
    (hherbrand : CyclicIdeleClassHerbrandQuotient.{u, u}) {K : Type u} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {S₁ T : Finset (HeightOneSpectrum (𝓞 K))} (hS₁ : HasGlobalUniformizers K S₁)
    (hpS : ∀ v ∉ S₁, IsUnit (p : v.adicCompletionIntegers K)) (hdisj : Disjoint S₁ T)
    (hT : ∀ u : ∀ q : HeightOneSpectrum (𝓞 K), (q.adicCompletion K)ˣ,
      (∀ q ∈ T, Valued.v (u q : q.adicCompletion K) = 1) →
        ∃ e ∈ sUnits K S₁, ∀ q ∈ T, ∃ c : (q.adicCompletion K)ˣ,
          u q = Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom e * c ^ p)
    (x : sUnits K (S₁ ∪ T))
    (hx : powerClasses K S₁ p (IdeleGroup.unitEmbedding (𝓞 K) K x) = 1) :
    x ∈ (powMonoidHom p : sUnits K (S₁ ∪ T) →* sUnits K (S₁ ∪ T)).range := by
  classical
  by_cases hxpow : ∃ c : K, c ^ p = ((x : Kˣ) : K)
  · obtain ⟨c, hc⟩ := hxpow
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.out.ne_zero] at hc
      exact (x : Kˣ).ne_zero hc.symm
    have hcS : Units.mk0 c hc0 ∈ sUnits K (S₁ ∪ T) := by
      intro v hv
      have h := congrArg (v.valuation K) hc
      rw [map_pow, x.2 v hv] at h
      exact (pow_eq_one_iff.1 h).resolve_right hp.out.ne_zero
    exact ⟨⟨Units.mk0 c hc0, hcS⟩, Subtype.ext (Units.ext hc)⟩
  exfalso
  push Not at hxpow
  obtain ⟨hxfin, hxinf⟩ := powerClasses_eq_one_iff.1 hx
  have : Fact (Irreducible (X ^ p - C ((x : Kˣ) : K))) :=
    ⟨irreducible_of_forall_pow_ne hp.out hxpow⟩
  have : NumberField (radicalExtension K p ((x : Kˣ) : K)) := numberField_radicalExtension
  have : IsGalois K (radicalExtension K p ((x : Kˣ) : K)) := isGalois_radicalExtension hζ
  have hfin : Module.finrank K (radicalExtension K p ((x : Kˣ) : K)) = p :=
    finrank_radicalExtension
  have : IsCyclic (radicalExtension K p ((x : Kˣ) : K) ≃ₐ[K] radicalExtension K p ((x : Kˣ) : K)) :=
    isCyclic_of_prime_card (by rw [IsGalois.card_aut_eq_finrank, hfin])
  set K' := radicalExtension K p ((x : Kˣ) : K)
  let ι := IdeleGroup.unitEmbedding (𝓞 K) K
  have hsurj : (ideleClassNorm (K := K) (L := K')).toMonoidHom.range = ⊤ := by
    rw [eq_top_iff]
    rintro c -
    induction c using QuotientGroup.induction_on with
    | H y =>
    have hy : y ∈ IdeleGroup.principalSubgroup (𝓞 K) K ⊔ sUnitIdeles K S₁ := by
      rw [principal_sup_sUnitIdeles hS₁]
      exact Subgroup.mem_top y
    obtain ⟨π, hπ, z, hz, rfl⟩ := Subgroup.mem_sup.1 hy
    obtain ⟨e, heS₁, he⟩ := hT (fun q => ideleCoordinate q z) fun q hq =>
      (ideleExponent_eq_one_iff q z).1
        (mem_sUnitIdeles_iff.1 hz q (Finset.disjoint_right.1 hdisj hq))
    have hdS₁ : z * (ι e)⁻¹ ∈ sUnitIdeles K S₁ :=
      (sUnitIdeles K S₁).mul_mem hz
        ((sUnitIdeles K S₁).inv_mem ((unitEmbedding_mem_sUnitIdeles_iff e).2 heS₁))
    have hdnorm : z * (ι e)⁻¹ ∈ (ideleNorm (K := K) (L := K')).toMonoidHom.range := by
      refine mem_range_ideleNorm_of_radical hζ hfin (adjoin_radicalRoot p _) (radicalRoot_pow p _)
        (S₁ ∪ T) ?_ ?_ (z * (ι e)⁻¹) ?_ ?_ ?_
      · intro v hv
        exact hpS v fun h => hv (Finset.mem_union_left _ h)
      · intro v hv
        exact (valuedAdicCompletion_eq_valuation' v _).trans (x.2 v hv)
      · intro v hv
        exact (ideleExponent_eq_one_iff v _).1
          (mem_sUnitIdeles_iff.1 hdS₁ v fun h => hv (Finset.mem_union_left _ h))
      · intro v hv
        rcases Finset.mem_union.1 hv with h | h
        · left
          obtain ⟨t, ht⟩ := hxfin v h
          exact ⟨(t : v.adicCompletion K), by
            rw [← Units.val_pow_eq_pow_val]
            exact congrArg Units.val ht⟩
        · right
          obtain ⟨c, hc⟩ := he v h
          refine ⟨c, ?_⟩
          change c ^ p = ideleCoordinate v z * (ideleCoordinate v (ι e))⁻¹
          have hιe : ideleCoordinate v (ι e) =
              Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom e :=
            Units.ext rfl
          rw [hιe, hc, mul_comm (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom e),
            mul_inv_cancel_right]
      · intro w
        left
        obtain ⟨t, ht⟩ := hxinf w
        exact ⟨(t : w.Completion), by
          rw [← Units.val_pow_eq_pow_val]
          exact congrArg Units.val ht⟩
    obtain ⟨z', hz'⟩ := hdnorm
    refine ⟨QuotientGroup.mk z', ?_⟩
    change ideleClassNorm (K := K) (L := K') (QuotientGroup.mk z') = _
    rw [ideleClassNorm_mk]
    change QuotientGroup.mk ((ideleNorm (K := K) (L := K')).toMonoidHom z') = _
    rw [hz', QuotientGroup.eq]
    have hrw : (z * (ι e)⁻¹)⁻¹ * (π * z) = π * ι e := by
      rw [mul_inv_rev, inv_inv, mul_comm π z, ← mul_assoc, inv_mul_cancel_right]
      exact mul_comm _ _
    rw [hrw]
    exact (IdeleGroup.principalSubgroup (𝓞 K) K).mul_mem hπ ⟨e, rfl⟩
  have hindex := cyclicH2NormIndexComparison hdescent ideleClassNormGaloisProduct K K'
  rw [hsurj, Subgroup.index_top] at hindex
  obtain ⟨-, -, hcard⟩ := hherbrand K K'
  rw [hcard, hfin] at hindex
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 (dvd_of_mul_right_dvd hindex))

end PowerLocalGlobal

section Main

/-- **The second inequality for Kummer extensions of prime degree** (Artin–Tate, Chapter VI §3,
Lemmas 2 and 3). Assume the cyclic nonsplit-prime statement, Galois descent for idele classes,
and the first inequality in the form `h²(C_E) = [E : F] h¹(C_E)`. Let `L/K` be Galois of prime
degree `p`, with `K` containing a primitive `p`-th root of unity. Then the index of the norm
range in `C_K` divides `p`. -/
theorem ideleClassKummerPrimeDegreeSecondInequality_of
    (hNS : CyclicNonsplitPrimeStatement.{u, u}) (hdescent : IdeleClassGaloisDescent.{u, u})
    (hherbrand : CyclicIdeleClassHerbrandQuotient.{u, u}) :
    IdeleClassKummerPrimeDegreeSecondInequality.{u, u} := by
  intro K _ _ L _ _ _ _ hprime hroot
  classical
  set p := Module.finrank K L with hpdef
  have : Fact p.Prime := ⟨hprime⟩
  have : FiniteDimensional K L := Module.finite_of_finrank_pos hprime.pos
  obtain ⟨ζ, hζ⟩ := hroot
  have : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (by rw [IsGalois.card_aut_eq_finrank])
  obtain ⟨β, ⟨a, ha⟩, hβtop⟩ :=
    exists_root_adjoin_eq_top_of_isCyclic K L ⟨ζ, (mem_primitiveRoots hprime.pos).2 hζ⟩
  have hirr := irreducible_X_pow_sub_C_of_root_adjoin_eq_top ha.symm hβtop
  have hapow : ∀ c : K, c ^ p ≠ a := (X_pow_sub_C_irreducible_iff_of_prime hprime).1 hirr
  have ha0 : a ≠ 0 := fun h => hapow 0 (by rw [h, zero_pow hprime.ne_zero])
  have hβ : Algebra.adjoin K {β} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite K β),
      hβtop, IntermediateField.top_toSubalgebra]
  obtain ⟨S₁, hS₁, hpS, haS⟩ := exists_initialPlaces p hprime.ne_zero (Units.mk0 a ha0)
  obtain ⟨T, hdisj, hcard, haT, hT⟩ :=
    exists_auxiliaryPrimes hNS hζ S₁ hpS (Units.mk0 a ha0) haS hapow
  obtain ⟨hne, hle⟩ := index_principal_sup_le hζ hS₁ hdisj hcard fun x hx =>
    mem_range_pow_of_powerClasses_eq_one hdescent hherbrand hζ hS₁ hpS hdisj hT x
      (MonoidHom.mem_ker.1 hx)
  have hD : kummerSubgroup K S₁ T p ≤ (ideleNorm (K := K) (L := L)).toMonoidHom.range := by
    intro y hy
    obtain ⟨hyS, hyψ⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨hψfin, hψinf⟩ := powerClasses_eq_one_iff.1 (MonoidHom.mem_ker.1 hyψ)
    refine mem_range_ideleNorm_of_radical hζ rfl hβ ha.symm (S₁ ∪ T) ?_ ?_ y ?_ ?_ ?_
    · intro v hv
      exact hpS v fun h => hv (Finset.mem_union_left _ h)
    · intro v hv
      exact (valuedAdicCompletion_eq_valuation' v a).trans
        (haS v fun h => hv (Finset.mem_union_left _ h))
    · intro v hv
      exact (ideleExponent_eq_one_iff v y).1 (mem_sUnitIdeles_iff.1 hyS v hv)
    · intro v hv
      rcases Finset.mem_union.1 hv with h | h
      · exact Or.inr (hψfin v h)
      · exact Or.inl (haT v h)
    · intro w
      exact Or.inr (hψinf w)
  set H := (ideleClassNorm (K := K) (L := L)).toMonoidHom.range
  have hcomap : IdeleGroup.principalSubgroup (𝓞 K) K ⊔ kummerSubgroup K S₁ T p ≤
      H.comap (QuotientGroup.mk' _) := by
    refine sup_le ?_ ?_
    · intro y hy
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).2 hy]
      exact H.one_mem
    · intro y hy
      obtain ⟨z, hz⟩ := hD hy
      refine ⟨QuotientGroup.mk z, ?_⟩
      change ideleClassNorm (K := K) (L := L) (QuotientGroup.mk z) = _
      rw [ideleClassNorm_mk]
      exact congrArg _ hz
  have hdvd : H.index ∣
      (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ kummerSubgroup K S₁ T p).index := by
    rw [← Subgroup.index_comap_of_surjective H (QuotientGroup.mk'_surjective _)]
    exact Subgroup.index_dvd_of_le hcomap
  have hHne : H.index ≠ 0 := fun h => hne (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  have hHle : H.index ≤ p := (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd).trans hle
  obtain ⟨r, hr⟩ := ideleClassNorm_range_index_dvd (K := K) (L := L) ⟨hHne⟩
  exact dvd_of_dvd_pow_of_le hprime hr hHle

end Main

end Langlands.Global.Arithmetic.KummerSecondInequality
