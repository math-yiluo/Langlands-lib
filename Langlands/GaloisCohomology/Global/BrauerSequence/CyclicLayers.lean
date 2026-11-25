import Langlands.GaloisCohomology.Global.BrauerSequence.Statement
import Langlands.Global.Arithmetic.CyclotomicSplitting
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Mathlib.FieldTheory.Galois.GaloisClosure

/-!
# Cyclic layers with prescribed local degrees

For a number field `K`, a separable closure `Ω`, a finite set `T` of finite places of `K` and
`m ≠ 0`, there is a finite cyclic Galois extension `E ⊆ Ω` of `K`, contained in a cyclotomic
extension `K(μ_N) ⊆ Ω`, whose local degrees above every place of `T` are multiples of `m`
(`exists_cyclic_layer`). This is the field `exists_isCyclic_dvd_localDegree` of
`BrauerSequenceData` (`exists_isCyclic_dvd_localDegree`).

The prime-power case comes from the Library: `CyclotomicSplitting.exists_cyclic_splitting` gives an
abstract cyclic extension inside a cyclotomic field with local degrees divisible by `ℓ ^ a` above
`T`. Its `ℓ`-primary part (the fixed field of the `ℓ ^ b`-th powers of a generator) keeps these
divisibilities, because the remaining local degrees divide a degree prime to `ℓ`
(`localDegreesDvd_primaryPart`). It is moved into `Ω` along an embedding
(`localDegreesDvd_of_algEquiv`: local degrees are invariant under isomorphisms over `K`, by
ramification indices and inertia degrees). The general case is the compositum of the prime-power
cases: the Galois group of a compositum embeds into the product of the Galois groups, which is
cyclic for coprime degrees, and local degrees grow in towers.
-/

namespace Langlands.GaloisCohomology

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Global.AdelicFunctoriality
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u v w

noncomputable section

section Definition

variable (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The local degrees `[L_w : K_v]` of `L / K` at all finite places `w` above places `v ∈ T` are
multiples of `m`. -/
def LocalDegreesDvd (T : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) : Prop :=
  ∀ v ∈ T, ∀ (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal],
    m ∣ Module.finrank (v.adicCompletion K) (w.adicCompletion L)

end Definition

section Transport

variable {K : Type u} {X : Type v} {Y : Type w} [Field K] [NumberField K] [Field X] [NumberField X]
  [Field Y] [NumberField Y] [Algebra K X] [Algebra K Y]

/-- Local degrees are invariant under an isomorphism of extensions of `K`. -/
theorem localDegreesDvd_of_algEquiv (φ : X ≃ₐ[K] Y) {T : Finset (HeightOneSpectrum (𝓞 K))}
    {m : ℕ} (h : LocalDegreesDvd K X T m) : LocalDegreesDvd K Y T m := by
  intro v hv w hw
  let φO : 𝓞 X ≃ₐ[𝓞 K] 𝓞 Y := RingOfIntegers.mapAlgEquiv φ
  let w' : HeightOneSpectrum (𝓞 X) :=
    ⟨w.asIdeal.comap φO, Ideal.comap_isPrime _ _, fun h => w.ne_bot (by
      rw [← Ideal.map_comap_of_surjective φO φO.surjective w.asIdeal, h, Ideal.map_bot])⟩
  have hw' : w'.asIdeal = w.asIdeal.comap φO := rfl
  have : w'.asIdeal.LiesOver v.asIdeal := by
    constructor
    rw [hw.over]
    ext x
    rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap, hw', Ideal.mem_comap,
      AlgEquiv.commutes]
  have : v.asIdeal.IsMaximal := v.isMaximal
  have : w.asIdeal.IsMaximal := w.isMaximal
  have : w'.asIdeal.IsMaximal := w'.isMaximal
  have key := h v hv w'
  rw [localDegree_eq] at key ⊢
  have he : w'.asIdeal.ramificationIdx (𝓞 K) = w.asIdeal.ramificationIdx (𝓞 K) := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w'.asIdeal v.ne_bot,
      ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot, hw']
    exact Ideal.ramificationIdx'_comap_eq v.asIdeal φO w.asIdeal
  have hf : w'.asIdeal.inertiaDeg (𝓞 K) = w.asIdeal.inertiaDeg (𝓞 K) := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w'.asIdeal,
      Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
    exact (Ideal.Quotient.algEquivOfEqComap v.asIdeal φO hw').toLinearEquiv.finrank_eq
  rwa [he, hf] at key

end Transport

section PrimaryPart

variable {K : Type u} {L : Type v} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- A finite cyclic Galois extension has, for every prime `ℓ`, a cyclic Galois subextension of
`ℓ`-power degree over which the top field has degree prime to `ℓ`. -/
theorem exists_primaryPart [IsGalois K L] [IsCyclic Gal(L/K)] {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ M : IntermediateField K L, IsGalois K M ∧ IsCyclic Gal(M/K) ∧
      (∃ b, Module.finrank K M = ℓ ^ b) ∧ (Module.finrank M L).Coprime ℓ := by
  classical
  set d := Module.finrank K L with hd
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Gal(L/K))
  have hcard : Nat.card Gal(L/K) = d := IsGalois.card_aut_eq_finrank K L
  have hdvd : ℓ ^ d.factorization ℓ ∣ orderOf g := by
    rw [hg, hcard]
    exact Nat.ordProj_dvd d ℓ
  let H : Subgroup Gal(L/K) := Subgroup.zpowers (g ^ ℓ ^ d.factorization ℓ)
  have hH : Nat.card H = d / ℓ ^ d.factorization ℓ := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (pow_ne_zero _ hℓ.ne_zero) hdvd, hg, hcard]
  have : IsMulCommutative Gal(L/K) := ⟨⟨fun a b => IsCyclic.commGroup.mul_comm a b⟩⟩
  let M := IntermediateField.fixedField H
  have htop : Module.finrank M L = d / ℓ ^ d.factorization ℓ := by
    rw [IntermediateField.finrank_fixedField_eq_card, hH]
  refine ⟨M, inferInstance,
    isCyclic_of_surjective (AlgEquiv.restrictNormalHom M) (AlgEquiv.restrictNormalHom_surjective L),
    ⟨d.factorization ℓ, ?_⟩, ?_⟩
  · have h1 := Module.finrank_mul_finrank K M L
    rw [htop, ← hd] at h1
    have h2 := Nat.ordProj_mul_ordCompl_eq_self d ℓ
    exact Nat.eq_of_mul_eq_mul_right (Nat.ordCompl_pos ℓ hd0) (h1.trans h2.symm)
  · rw [htop]
    exact (Nat.coprime_ordCompl hℓ hd0).symm

/-- The local degrees of a subextension `M` of a Galois extension `L / K` keep the divisibility by
`ℓ ^ a` of the local degrees of `L` when `[L : M]` is prime to `ℓ`. -/
theorem localDegreesDvd_primaryPart [IsGalois K L] (M : IntermediateField K L) [NumberField M]
    {T : Finset (HeightOneSpectrum (𝓞 K))} {ℓ a : ℕ} (hcop : (Module.finrank M L).Coprime ℓ)
    (h : LocalDegreesDvd K L T (ℓ ^ a)) : LocalDegreesDvd K M T (ℓ ^ a) := by
  intro v hv w hw
  obtain ⟨q, hq⟩ := exists_place_above (L := L) w
  have : q.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans q.asIdeal w.asIdeal v.asIdeal
  have h1 := h v hv q
  rw [localDegree_eq, Ideal.ramificationIdx_tower (R := 𝓞 K) w.asIdeal q.asIdeal,
    Ideal.inertiaDeg_tower (R := 𝓞 K) w.asIdeal q.asIdeal] at h1
  have : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
  have h2 := localDegree_dvd (K := M) (L := L) w q
  rw [localDegree_eq] at h2
  have hc : (ℓ ^ a).Coprime (q.asIdeal.ramificationIdx (𝓞 M) * q.asIdeal.inertiaDeg (𝓞 M)) :=
    Nat.Coprime.pow_left a (Nat.Coprime.coprime_dvd_left h2 hcop).symm
  rw [localDegree_eq]
  refine hc.dvd_of_dvd_mul_right ?_
  calc ℓ ^ a ∣ w.asIdeal.ramificationIdx (𝓞 K) * q.asIdeal.ramificationIdx (𝓞 M) *
        (w.asIdeal.inertiaDeg (𝓞 K) * q.asIdeal.inertiaDeg (𝓞 M)) := h1
    _ = _ := by ring

end PrimaryPart

section Compositum

variable {K : Type u} [Field K] [NumberField K] {Ω : Type v} [Field Ω] [Algebra K Ω]

/-- Local degrees grow along an inclusion of subextensions of `Ω`. -/
theorem localDegreesDvd_of_le {E₁ E₂ : IntermediateField K Ω} [NumberField E₁] [NumberField E₂]
    (hle : E₁ ≤ E₂) {T : Finset (HeightOneSpectrum (𝓞 K))} {m : ℕ}
    (h : LocalDegreesDvd K E₁ T m) : LocalDegreesDvd K E₂ T m := by
  let : Algebra E₁ E₂ := (IntermediateField.inclusion hle).toAlgebra
  have : IsScalarTower K E₁ E₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro v hv w _
  let w₁ : HeightOneSpectrum (𝓞 E₁) := w.under (𝓞 E₁)
  have : w.asIdeal.LiesOver w₁.asIdeal := ⟨rfl⟩
  have : w₁.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.tower_bot w.asIdeal w₁.asIdeal v.asIdeal
  exact (h v hv w₁).trans (localDegree_dvd_localDegree v w₁ w)

omit [NumberField K] in
/-- The compositum of two finite cyclic Galois extensions of coprime degrees is cyclic, of degree
dividing the product of the degrees. -/
theorem isCyclic_sup {E₁ E₂ : IntermediateField K Ω} [FiniteDimensional K E₁]
    [FiniteDimensional K E₂] [IsGalois K E₁] [IsGalois K E₂] [IsCyclic Gal(E₁/K)]
    [IsCyclic Gal(E₂/K)] (hcop : (Module.finrank K E₁).Coprime (Module.finrank K E₂)) :
    IsCyclic Gal((E₁ ⊔ E₂ : IntermediateField K Ω)/K) ∧
      Module.finrank K (E₁ ⊔ E₂ : IntermediateField K Ω) ∣
        Module.finrank K E₁ * Module.finrank K E₂ := by
  have hprod : IsCyclic (Gal(E₁/K) × Gal(E₂/K)) := by
    refine Group.isCyclic_prod_iff.2 ⟨inferInstance, inferInstance, ?_⟩
    rwa [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank]
  refine ⟨isCyclic_of_injective _ (IntermediateField.restrictNormalHomSupProd_injective E₁ E₂), ?_⟩
  have h := Subgroup.card_dvd_of_injective _
    (IntermediateField.restrictNormalHomSupProd_injective E₁ E₂)
  rwa [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    IsGalois.card_aut_eq_finrank] at h

end Compositum

section Layers

variable (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]

/-- The cyclotomic extension `K(μ_N) ⊆ Ω`, generated by the `N`-th roots of unity of `Ω`. -/
def cyclotomicLayer (N : ℕ) : IntermediateField K Ω :=
  IntermediateField.adjoin K {x : Ω | x ^ N = 1}

variable {K Ω}

omit [NumberField K] in
/-- `K(μ_N) ⊆ K(μ_N')` when `N ∣ N'`. -/
theorem cyclotomicLayer_mono {N N' : ℕ} (h : N ∣ N') :
    cyclotomicLayer K Ω N ≤ cyclotomicLayer K Ω N' := by
  obtain ⟨c, rfl⟩ := h
  refine IntermediateField.adjoin.mono K _ _ fun x (hx : x ^ N = 1) => ?_
  change x ^ (N * c) = 1
  rw [pow_mul, hx, one_pow]

/-- The image of the cyclotomic field `K(μ_N)` in `Ω` lies in `cyclotomicLayer K Ω N`. -/
theorem fieldRange_le_cyclotomicLayer (N : ℕ) [NeZero N] (g : CyclotomicField N K →ₐ[K] Ω) :
    g.fieldRange ≤ cyclotomicLayer K Ω N := by
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ Algebra.adjoin K {b : CyclotomicField N K |
      ∃ n : ℕ, n ∈ ({N} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1} :=
    IsCyclotomicExtension.adjoin_roots y
  have hle : Algebra.adjoin K {b : CyclotomicField N K |
      ∃ n : ℕ, n ∈ ({N} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1} ≤
      (cyclotomicLayer K Ω N).toSubalgebra.comap g := by
    refine Algebra.adjoin_le fun b ⟨n, hn, _, hb⟩ => ?_
    rw [Set.mem_singleton_iff] at hn
    subst hn
    refine IntermediateField.subset_adjoin K _ ?_
    change g b ^ n = 1
    rw [← map_pow, hb, map_one]
  exact hle hy

/-- The statement proved by induction on `m`: a cyclic layer whose degree has only prime factors
of `m`. -/
private def CyclicLayer (T : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) : Prop :=
  ∃ (E : IntermediateField K Ω) (_ : FiniteDimensional K E), IsGalois K E ∧ IsCyclic Gal(E/K) ∧
    (∀ p : ℕ, p.Prime → p ∣ Module.finrank K E → p ∣ m) ∧
    (∃ N : ℕ, N ≠ 0 ∧ E ≤ cyclotomicLayer K Ω N) ∧
    ∀ v ∈ T, ∀ (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal],
      m ∣ localDegree E v w

/-- The case `m = 1`: the trivial extension. -/
private theorem cyclicLayer_one (T : Finset (HeightOneSpectrum (𝓞 K))) :
    CyclicLayer (K := K) (Ω := Ω) T 1 := by
  refine ⟨⊥, inferInstance, IsGalois.of_algEquiv (IntermediateField.botEquiv K Ω).symm, ?_,
    fun p _ hp => ?_, ⟨1, one_ne_zero, bot_le⟩, fun _ _ _ _ => one_dvd _⟩
  · have : Subsingleton Gal((⊥ : IntermediateField K Ω)/K) :=
      ⟨fun σ τ => AlgEquiv.ext fun x => by
        obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 x.2
        have hx : x = algebraMap K (⊥ : IntermediateField K Ω) y := Subtype.ext hy.symm
        rw [hx, AlgEquiv.commutes, AlgEquiv.commutes]⟩
    exact isCyclic_of_subsingleton
  · rwa [IntermediateField.finrank_bot] at hp

variable [IsSepClosure K Ω]

/-- The prime-power case: the `ℓ`-primary part of the Library's cyclic splitting field, moved into
`Ω`. -/
private theorem cyclicLayer_primePow (T : Finset (HeightOneSpectrum (𝓞 K))) {ℓ n : ℕ}
    (hℓ : ℓ.Prime) (hn : 0 < n) : CyclicLayer (K := K) (Ω := Ω) T (ℓ ^ n) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨X, _, _, _, hGal, hCyc, ⟨N, hN, ⟨ψ⟩⟩, hloc, -⟩ :=
    Langlands.Global.CyclotomicSplitting.exists_cyclic_splitting K ℓ n T
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨M, hMGal, hMCyc, ⟨b, hb⟩, hcop⟩ := exists_primaryPart (K := K) (L := X) hℓ
  have := NumberField.of_module_finite K M
  have hlocM : LocalDegreesDvd K M T (ℓ ^ n) :=
    localDegreesDvd_primaryPart M hcop fun v hv w _ => hloc v hv w
  let g : CyclotomicField N K →ₐ[K] Ω := IsSepClosed.lift
  let f : X →ₐ[K] Ω := g.comp ψ
  let E : IntermediateField K Ω := M.map f
  let φ : M ≃ₐ[K] E := IntermediateField.equivMap M f
  have : FiniteDimensional K E := LinearEquiv.finiteDimensional φ.toLinearEquiv
  have := NumberField.of_module_finite K E
  have hEdeg : Module.finrank K E = ℓ ^ b := φ.toLinearEquiv.finrank_eq.symm.trans hb
  refine ⟨E, inferInstance, IsGalois.of_algEquiv φ,
    isCyclic_of_surjective (AlgEquiv.autCongr φ).toMonoidHom (AlgEquiv.autCongr φ).surjective,
    fun p hp hpE => ?_, ⟨N, hN.ne', ?_⟩, fun v hv w _ => localDegreesDvd_of_algEquiv φ hlocM v hv w⟩
  · rw [hEdeg] at hpE
    rw [(Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hpE)]
    exact dvd_pow_self ℓ hn.ne'
  · rintro _ ⟨x, -, rfl⟩
    exact fieldRange_le_cyclotomicLayer N g ⟨ψ x, rfl⟩

omit [IsSepClosure K Ω] in
/-- The coprime case: the compositum. -/
private theorem cyclicLayer_mul (T : Finset (HeightOneSpectrum (𝓞 K))) {a b : ℕ}
    (hab : a.Coprime b) (ha : CyclicLayer (K := K) (Ω := Ω) T a)
    (hb : CyclicLayer (K := K) (Ω := Ω) T b) : CyclicLayer (K := K) (Ω := Ω) T (a * b) := by
  obtain ⟨E₁, _, _, _, hp₁, ⟨N₁, hN₁, hE₁⟩, hl₁⟩ := ha
  obtain ⟨E₂, _, _, _, hp₂, ⟨N₂, hN₂, hE₂⟩, hl₂⟩ := hb
  have hcop : (Module.finrank K E₁).Coprime (Module.finrank K E₂) :=
    Nat.coprime_of_dvd fun p hp h₁ h₂ =>
      hp.not_dvd_one (hab ▸ Nat.dvd_gcd (hp₁ p hp h₁) (hp₂ p hp h₂))
  obtain ⟨hcyc, hdeg⟩ := isCyclic_sup hcop
  have := NumberField.of_module_finite K E₁
  have := NumberField.of_module_finite K E₂
  have := NumberField.of_module_finite K (E₁ ⊔ E₂ : IntermediateField K Ω)
  refine ⟨E₁ ⊔ E₂, inferInstance, inferInstance, hcyc, fun p hp hpE => ?_,
    ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, sup_le (hE₁.trans (cyclotomicLayer_mono (dvd_mul_right _ _)))
      (hE₂.trans (cyclotomicLayer_mono (dvd_mul_left _ _)))⟩, fun v hv w _ => ?_⟩
  · rcases (Nat.Prime.dvd_mul hp).1 (hpE.trans hdeg) with h | h
    · exact (hp₁ p hp h).trans (dvd_mul_right _ _)
    · exact (hp₂ p hp h).trans (dvd_mul_left _ _)
  · have h₁ : a ∣ localDegree _ v w :=
      localDegreesDvd_of_le (E₁ := E₁) le_sup_left (fun v hv w _ => hl₁ v hv w) v hv w
    have h₂ : b ∣ localDegree _ v w :=
      localDegreesDvd_of_le (E₁ := E₂) le_sup_right (fun v hv w _ => hl₂ v hv w) v hv w
    exact hab.mul_dvd_of_dvd_of_dvd h₁ h₂

/-- **Cyclic layers.** For a finite set `T` of finite places of `K` and `m ≠ 0` there is a
finite cyclic Galois extension `E ⊆ Ω` of `K`, contained in a cyclotomic extension `K(μ_N)`,
whose local degrees above every place of `T` are multiples of `m`. -/
theorem exists_cyclic_layer (T : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) (hm : m ≠ 0) :
    ∃ (E : IntermediateField K Ω) (_ : FiniteDimensional K E), IsGalois K E ∧
      IsCyclic Gal(E/K) ∧ (∃ N : ℕ, N ≠ 0 ∧ E ≤ cyclotomicLayer K Ω N) ∧
      ∀ v ∈ T, ∀ (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal],
        m ∣ localDegree E v w := by
  have key : ∀ m : ℕ, m ≠ 0 → CyclicLayer (K := K) (Ω := Ω) T m := by
    intro m
    induction m using Nat.recOnPosPrimePosCoprime with
    | prime_pow p n hp hn => exact fun _ => cyclicLayer_primePow T hp hn
    | zero => exact fun h => absurd rfl h
    | one => exact fun _ => cyclicLayer_one T
    | coprime a b ha hb hab iha ihb =>
      exact fun _ => cyclicLayer_mul T hab (iha (by omega)) (ihb (by omega))
  obtain ⟨E, hE, hGal, hCyc, -, hN, hloc⟩ := key m hm
  exact ⟨E, hE, hGal, hCyc, hN, hloc⟩

end Layers

/-- The field `exists_isCyclic_dvd_localDegree` of `BrauerSequenceData`, proved. -/
theorem exists_isCyclic_dvd_localDegree (K Ω : Type u) [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [IsSepClosure K Ω] (T : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ)
    (hm : m ≠ 0) :
    ∃ (E : IntermediateField K Ω) (_ : FiniteDimensional K E), IsGalois K E ∧ IsCyclic Gal(E/K) ∧
      ∀ v ∈ T, ∀ (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal],
        m ∣ localDegree E v w := by
  obtain ⟨E, hE, hGal, hCyc, -, hloc⟩ := exists_cyclic_layer (Ω := Ω) T m hm
  exact ⟨E, hE, hGal, hCyc, hloc⟩

end

end Langlands.GaloisCohomology
