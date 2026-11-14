import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.Translation

/-! # A separating coordinate for a finite-index enlargement of integral points

In the abstract setting of `Translation`, let `U` be the subgroup of integral points and let
`V ⊇ U` be a subgroup in which `U` is normal of finite index. We construct a coordinate `e`
that is integral on `V`, a unit at the identity, and lies in the maximal ideal at every
point of `V` outside `U`. -/

noncomputable section

universe u

open TensorProduct WithConv

namespace Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement

section Values

variable (R : Type u) [CommRing R] [IsLocalRing R] {K : Type u} [Field K] [Algebra R K]

/-- `z : K` is the image of a unit of `R`. -/
def IsIntUnit (z : K) : Prop :=
  ∃ r : R, IsUnit r ∧ algebraMap R K r = z

/-- `z : K` is the image of an element of the maximal ideal of `R`. -/
def IsIntSmall (z : K) : Prop :=
  ∃ r ∈ IsLocalRing.maximalIdeal R, algebraMap R K r = z

end Values

section ValueLemmas

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]

theorem IsIntUnit.mem_range {z : K} (h : IsIntUnit R z) : z ∈ (algebraMap R K).range := by
  obtain ⟨r, -, rfl⟩ := h
  exact RingHom.mem_range_self _ r

theorem IsIntSmall.mem_range [IsLocalRing R] {z : K} (h : IsIntSmall R z) :
    z ∈ (algebraMap R K).range := by
  obtain ⟨r, -, rfl⟩ := h
  exact RingHom.mem_range_self _ r

theorem isIntSmall_of_not_isIntUnit [IsLocalRing R] {z : K} (hz : z ∈ (algebraMap R K).range)
    (h : ¬ IsIntUnit R z) : IsIntSmall R z := by
  obtain ⟨r, rfl⟩ := hz
  refine ⟨r, ?_, rfl⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact fun hr => h ⟨r, hr, rfl⟩

theorem not_isIntSmall_of_isIntUnit [IsLocalRing R] [IsFractionRing R K] {z : K}
    (h : IsIntUnit R z) : ¬ IsIntSmall R z := by
  obtain ⟨r, hr, rfl⟩ := h
  rintro ⟨s, hs, hsr⟩
  rw [IsFractionRing.injective R K hsr, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs
  exact hs hr

theorem IsIntUnit.mul {a b : K} (ha : IsIntUnit R a) (hb : IsIntUnit R b) :
    IsIntUnit R (a * b) := by
  obtain ⟨r, hr, rfl⟩ := ha
  obtain ⟨s, hs, rfl⟩ := hb
  exact ⟨r * s, hr.mul hs, map_mul _ r s⟩

theorem IsIntUnit.pow {a : K} (ha : IsIntUnit R a) (n : ℕ) : IsIntUnit R (a ^ n) := by
  obtain ⟨r, hr, rfl⟩ := ha
  exact ⟨r ^ n, hr.pow n, map_pow _ r n⟩

theorem IsIntUnit.of_mul_left [IsFractionRing R K] {a b : K} (ha : a ∈ (algebraMap R K).range)
    (hb : b ∈ (algebraMap R K).range) (h : IsIntUnit R (a * b)) : IsIntUnit R a := by
  obtain ⟨r, rfl⟩ := ha
  obtain ⟨s, rfl⟩ := hb
  obtain ⟨t, ht, hts⟩ := h
  rw [← map_mul] at hts
  rw [IsFractionRing.injective R K hts] at ht
  exact ⟨r, isUnit_of_mul_isUnit_left ht, rfl⟩

theorem IsIntUnit.of_mul_right [IsFractionRing R K] {a b : K} (ha : a ∈ (algebraMap R K).range)
    (hb : b ∈ (algebraMap R K).range) (h : IsIntUnit R (a * b)) : IsIntUnit R b := by
  rw [mul_comm] at h
  exact h.of_mul_left hb ha

theorem IsIntSmall.mul [IsLocalRing R] {a b : K} (ha : IsIntSmall R a)
    (hb : b ∈ (algebraMap R K).range) :
    IsIntSmall R (a * b) := by
  obtain ⟨r, hr, rfl⟩ := ha
  obtain ⟨s, rfl⟩ := hb
  exact ⟨r * s, Ideal.mul_mem_right s _ hr, map_mul _ r s⟩

theorem IsIntSmall.mul_left [IsLocalRing R] {a b : K} (ha : a ∈ (algebraMap R K).range)
    (hb : IsIntSmall R b) :
    IsIntSmall R (a * b) := by
  rw [mul_comm]
  exact hb.mul ha

/-- If `ϖ ^ N * g` is integral and `f` is small then `g * f ^ (N + 1)` is small. -/
theorem isIntSmall_mul_pow [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    {N : ℕ} {f g : K}
    (hg : algebraMap R K (ϖ ^ N) * g ∈ (algebraMap R K).range) (hf : IsIntSmall R f) :
    IsIntSmall R (g * f ^ (N + 1)) := by
  obtain ⟨r, hr, rfl⟩ := hf
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hr
  obtain ⟨c, rfl⟩ := hr
  obtain ⟨d, hd⟩ := hg
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  refine ⟨d * ϖ * c ^ (N + 1), Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hϖm), ?_⟩
  simp only [map_mul, map_pow] at hd ⊢
  rw [hd]
  ring

/-- If `ϖ ^ (m + 1) * z` is integral but `ϖ ^ m * z` is not, then `ϖ ^ (m + 1) * z` is a unit. -/
theorem isIntUnit_of_not_mem [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) {m : ℕ} {z : K}
    (h1 : algebraMap R K (ϖ ^ (m + 1)) * z ∈ (algebraMap R K).range)
    (h2 : algebraMap R K (ϖ ^ m) * z ∉ (algebraMap R K).range) :
    IsIntUnit R (algebraMap R K (ϖ ^ (m + 1)) * z) := by
  by_contra hu
  obtain ⟨r, hr, hrz⟩ := isIntSmall_of_not_isIntUnit h1 hu
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hr
  obtain ⟨c, rfl⟩ := hr
  apply h2
  refine ⟨c, ?_⟩
  have hϖ0 : algebraMap R K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hϖ.ne_zero
  apply mul_left_cancel₀ hϖ0
  rw [← map_mul, mul_comm ϖ c, hrz]
  simp only [map_pow]
  ring

/-- A positive power of `ϖ` times an integral element is small. -/
theorem isIntSmall_pow_succ_mul [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
    (hϖ : Irreducible ϖ) (m : ℕ) {z : K} (hz : z ∈ (algebraMap R K).range) :
    IsIntSmall R (algebraMap R K (ϖ ^ (m + 1)) * z) := by
  obtain ⟨s, rfl⟩ := hz
  refine ⟨ϖ ^ (m + 1) * s, Ideal.mul_mem_right _ _ ?_, map_mul _ _ _⟩
  rw [hϖ.maximalIdeal_eq]
  exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self ϖ) _ m.succ_pos

end ValueLemmas

section Group

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
  {A : Type u} [CommRing A] [HopfAlgebra R A] {P : Type*} [Group P]
  (ev : P →* WithConv (A →ₐ[R] K))

theorem ev_mul_apply (x : P) (a b : A) : ev x (a * b) = ev x a * ev x b :=
  map_mul (ev x).ofConv a b

theorem ev_pow_apply (x : P) (a : A) (n : ℕ) : ev x (a ^ n) = ev x a ^ n :=
  map_pow (ev x).ofConv a n

theorem ev_one_right (x : P) : ev x 1 = 1 :=
  map_one (ev x).ofConv

end Group

section Cosets

variable {P : Type*} [Group P] (U V : Subgroup P)

/-- Finitely many left coset representatives for a finite-index subgroup. -/
theorem exists_finset_of_finiteIndex [(U.subgroupOf V).FiniteIndex] :
    ∃ T : Finset P, ∀ x ∈ V, ∃ r ∈ T, ∃ u ∈ U, x = r * u := by
  let f : V ⧸ U.subgroupOf V → P := fun q => ((Quotient.out q : V) : P)
  refine ⟨(Set.finite_range f).toFinset, fun x hx => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf V) (⟨x, hx⟩ : V)
  refine ⟨f (QuotientGroup.mk (⟨x, hx⟩ : V)), (Set.finite_range f).mem_toFinset.mpr
    (Set.mem_range_self _), ((h : V) : P)⁻¹, U.inv_mem h.2, ?_⟩
  simp only [f, hh, Subgroup.coe_mul, mul_inv_cancel_right]

/-- In a finite-index normal subgroup, some positive power of each element lies in the
subgroup. -/
theorem exists_pow_succ_mem [(U.subgroupOf V).Normal] [(U.subgroupOf V).FiniteIndex] :
    ∃ n : ℕ, ∀ x ∈ V, x ^ (n + 1) ∈ U := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := U.subgroupOf V))
  refine ⟨n, fun x hx => ?_⟩
  have := Subgroup.pow_index_mem (U.subgroupOf V) (⟨x, hx⟩ : V)
  rw [hn, Subgroup.mem_subgroupOf, Subgroup.coe_pow] at this
  exact this

/-- Conjugation by elements of `V` preserves a subgroup that is normal in `V`. -/
theorem inv_mul_mul_mem [(U.subgroupOf V).Normal] (hUV : U ≤ V) :
    ∀ x ∈ V, ∀ u ∈ U, x⁻¹ * u * x ∈ U := by
  intro x hx u hu
  have := Subgroup.Normal.conj_mem (inferInstance : (U.subgroupOf V).Normal)
    ⟨u, hUV hu⟩ (Subgroup.mem_subgroupOf.mpr hu) (⟨x, hx⟩ : V)⁻¹
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

end Cosets

section Separating

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsAlgClosed (IsLocalRing.ResidueField R)] {K : Type u} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Type u} [CommRing A] [HopfAlgebra R A] [Algebra.Smooth R A]
  {P : Type*} [Group P] (ev : P →* WithConv (A →ₐ[R] K))
  (U : Subgroup P) (hU : ∀ x, x ∈ U ↔ ∀ a, ev x a ∈ (algebraMap R K).range)
  (hsurj : ∀ σ : A →ₐ[R] R, ∃ u, (ev u).ofConv = (Algebra.ofId R K).comp σ)
  (V : Subgroup P) (hUV : U ≤ V) (hnorm : ∀ x ∈ V, ∀ u ∈ U, x⁻¹ * u * x ∈ U)
  (T : Finset P) (hT : ∀ x ∈ V, ∃ r ∈ T, ∃ u ∈ U, x = r * u)
  (n : ℕ) (hpow : ∀ x ∈ V, x ^ (n + 1) ∈ U)

omit [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] [Algebra.Smooth R A] in
include hU hT in
/-- Every coordinate has bounded denominators on `V`. -/
theorem exists_bound {ϖ : R} (hϖ : Irreducible ϖ) (a : A) :
    ∃ N : ℕ, ∀ x ∈ V, algebraMap R K (ϖ ^ N) * ev x a ∈ (algebraMap R K).range := by
  choose Nf hNf using fun r => exists_pow_smul_mem ev U hU hϖ r a
  refine ⟨T.sup Nf, fun x hx => ?_⟩
  obtain ⟨r, hr, u, hu, rfl⟩ := hT x hx
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := Nf) hr)
  have h := hNf r u hu
  rw [Algebra.smul_def] at h
  rw [hd, pow_add, map_mul, mul_comm (algebraMap R K (ϖ ^ Nf r)), mul_assoc]
  exact Subring.mul_mem _ (RingHom.mem_range_self _ _) h

omit [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsAlgClosed (IsLocalRing.ResidueField R)] [IsFractionRing R K] [Algebra.Smooth R A] in
/-- Units in a coset `x U` can be tested at any representative of the coset. -/
theorem exists_isIntUnit_iff {x r u' : P} (hu' : u' ∈ U) (hx : x = r * u')
    (f : A) : (∃ u ∈ U, IsIntUnit R (ev (x * u) f)) ↔ ∃ u ∈ U, IsIntUnit R (ev (r * u) f) := by
  subst hx
  constructor
  · rintro ⟨u, hu, h⟩
    exact ⟨u' * u, U.mul_mem hu' hu, by rwa [← mul_assoc]⟩
  · rintro ⟨u, hu, h⟩
    refine ⟨u'⁻¹ * u, U.mul_mem (U.inv_mem hu') hu, ?_⟩
    rwa [mul_assoc, mul_inv_cancel_left]

include hU hsurj hnorm hT hpow in
open scoped Classical in
/-- The separating coordinate, constructed by strong induction on the number of cosets of `U`
in an intermediate subgroup `W`. -/
theorem exists_separating_aux {ϖ : R} (hϖ : Irreducible ϖ) (k : ℕ) :
    ∀ W : Subgroup P, (T.filter (· ∈ W)).card = k → U ≤ W → W ≤ V →
      ∃ e : A, (∀ x ∈ W, ev x e ∈ (algebraMap R K).range) ∧ IsIntUnit R (ev 1 e) ∧
        ∀ x ∈ W, x ∉ U → IsIntSmall R (ev x e) := by
  classical
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro W hk hUW hWV
  -- coordinates integral on `W` and a unit at the identity
  let S : A → Prop := fun f =>
    (∀ x ∈ W, ev x f ∈ (algebraMap R K).range) ∧ IsIntUnit R (ev 1 f)
  -- the representatives of cosets on which a coordinate takes a unit value
  let supp : A → Finset P := fun f =>
    T.filter (fun r => r ∈ W ∧ ∃ u ∈ U, IsIntUnit R (ev (r * u) f))
  have h1S : S 1 := ⟨fun x _ => ⟨1, by rw [map_one, ev_one_right]⟩,
    ⟨1, isUnit_one, by rw [map_one, ev_one_right]⟩⟩
  have hex : ∃ m, ∃ f, S f ∧ (supp f).card = m := ⟨_, 1, h1S, rfl⟩
  obtain ⟨f0, hf0S, hf0card⟩ := Nat.find_spec hex
  have hmin : ∀ f, S f → (supp f0).card ≤ (supp f).card := fun f hf =>
    hf0card ▸ Nat.find_min' hex ⟨f, hf, rfl⟩
  have hWrep : ∀ x ∈ W, ∃ r ∈ T, r ∈ W ∧ ∃ u ∈ U, x = r * u := by
    intro x hx
    obtain ⟨r, hrT, u, hu, rfl⟩ := hT x (hWV hx)
    refine ⟨r, hrT, ?_, u, hu, rfl⟩
    simpa using W.mul_mem hx (W.inv_mem (hUW hu))
  -- every support contains the minimal one
  have hP1 : ∀ g, S g → ∀ x ∈ W, (∃ u ∈ U, IsIntUnit R (ev (x * u) f0)) →
      ∃ u ∈ U, IsIntUnit R (ev (x * u) g) := by
    intro g hg x hxW hx
    have hprod : S (f0 * g) := ⟨fun y hy => by
      rw [ev_mul_apply]; exact Subring.mul_mem _ (hf0S.1 y hy) (hg.1 y hy), by
      rw [ev_mul_apply]; exact hf0S.2.mul hg.2⟩
    have hsub : supp (f0 * g) ⊆ supp f0 := by
      intro r hr
      simp only [supp, Finset.mem_filter] at hr ⊢
      obtain ⟨hrT, hrW, u, hu, hunit⟩ := hr
      rw [ev_mul_apply] at hunit
      exact ⟨hrT, hrW, u, hu, hunit.of_mul_left (hf0S.1 _ (W.mul_mem hrW (hUW hu)))
        (hg.1 _ (W.mul_mem hrW (hUW hu)))⟩
    have hsub' : supp (f0 * g) ⊆ supp g := by
      intro r hr
      simp only [supp, Finset.mem_filter] at hr ⊢
      obtain ⟨hrT, hrW, u, hu, hunit⟩ := hr
      rw [ev_mul_apply] at hunit
      exact ⟨hrT, hrW, u, hu, hunit.of_mul_right (hf0S.1 _ (W.mul_mem hrW (hUW hu)))
        (hg.1 _ (W.mul_mem hrW (hUW hu)))⟩
    have heq : supp (f0 * g) = supp f0 := Finset.eq_of_subset_of_card_le hsub (hmin _ hprod)
    obtain ⟨r, hrT, hrW, u', hu', hxr⟩ := hWrep x hxW
    have hr0 : r ∈ supp (f0 * g) := by
      rw [heq]
      exact Finset.mem_filter.2 ⟨hrT, hrW, (exists_isIntUnit_iff ev U hu' hxr f0).1 hx⟩
    exact (exists_isIntUnit_iff ev U hu' hxr g).2 (Finset.mem_filter.1 (hsub' hr0)).2.2
  -- the elements whose coset contains a unit value of `f0`
  let memH : P → Prop := fun x => x ∈ W ∧ ∃ u ∈ U, IsIntUnit R (ev (x * u) f0)
  have hmulH : ∀ x y, memH x → memH y → memH (x * y) := by
    rintro x y ⟨hxW, u0, hu0, hx⟩ ⟨hyW, u1, hu1, hy⟩
    have hxu0 : x * u0 ∈ W := W.mul_mem hxW (hUW hu0)
    obtain ⟨g, hg⟩ := exists_left_translate ev U hU hsurj (x * u0) f0
      (fun u hu => hf0S.1 _ (W.mul_mem hxu0 (hUW hu)))
    have hgS : S g := ⟨fun z hz => by rw [hg]; exact hf0S.1 _ (W.mul_mem hxu0 hz), by
      rw [hg, mul_one]; exact hx⟩
    obtain ⟨u, hu, hyu⟩ := hP1 g hgS y hyW ⟨u1, hu1, hy⟩
    rw [hg] at hyu
    refine ⟨W.mul_mem hxW hyW, y⁻¹ * u0 * y * u, U.mul_mem (hnorm y (hWV hyW) u0 hu0) hu, ?_⟩
    have he : x * y * (y⁻¹ * u0 * y * u) = x * u0 * (y * u) := by group
    rw [he]
    exact hyu
  have hUH : ∀ u ∈ U, memH u := fun u hu =>
    ⟨hUW hu, u⁻¹, U.inv_mem hu, by rw [mul_inv_cancel]; exact hf0S.2⟩
  have hpowH : ∀ x, memH x → ∀ j : ℕ, memH (x ^ j) := by
    intro x hx j
    induction j with
    | zero => rw [pow_zero]; exact hUH 1 U.one_mem
    | succ j ihj => rw [pow_succ]; exact hmulH _ _ ihj hx
  obtain ⟨H, hH⟩ : ∃ H : Subgroup P, ∀ x, x ∈ H ↔ memH x := by
    refine ⟨{ carrier := {x | memH x}
              mul_mem' := fun hx hy => hmulH _ _ hx hy
              one_mem' := hUH 1 U.one_mem
              inv_mem' := fun {x} hx => ?_ }, fun x => Iff.rfl⟩
    have he : x⁻¹ = x ^ n * (x ^ (n + 1))⁻¹ := by group
    show memH x⁻¹
    rw [he]
    exact hmulH _ _ (hpowH x hx n) (hUH _ (U.inv_mem (hpow x (hWV hx.1))))
  by_cases hall : ∀ x ∈ W, memH x
  · by_cases hWU : ∀ x ∈ W, x ∈ U
    · exact ⟨f0, hf0S.1, hf0S.2, fun x hx hxU => absurd (hWU x hx) hxU⟩
    · exfalso
      push Not at hWU
      obtain ⟨v, hvW, hvU⟩ := hWU
      have hna : ¬ ∀ a, ev v a ∈ (algebraMap R K).range := fun h => hvU ((hU v).2 h)
      push Not at hna
      obtain ⟨a, ha⟩ := hna
      obtain ⟨N0, hN0⟩ := exists_bound ev U hU V T hT hϖ a
      have hexm : ∃ m, ∀ x ∈ W, algebraMap R K (ϖ ^ m) * ev x a ∈ (algebraMap R K).range :=
        ⟨N0, fun x hx => hN0 x (hWV hx)⟩
      have hm := Nat.find_spec hexm
      have hm0 : Nat.find hexm ≠ 0 := by
        intro h0
        apply ha
        have := hm v hvW
        rwa [h0, pow_zero, map_one, one_mul] at this
      obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have hnot : ¬ ∀ x ∈ W, algebraMap R K (ϖ ^ m') * ev x a ∈ (algebraMap R K).range :=
        Nat.find_min hexm (by omega)
      push Not at hnot
      obtain ⟨x1, hx1W, hx1⟩ := hnot
      rw [hm'] at hm
      have hunit1 := isIntUnit_of_not_mem hϖ (hm x1 hx1W) hx1
      have hev' : ∀ y, ev y (algebraMap R A (ϖ ^ (m' + 1)) * a) =
          algebraMap R K (ϖ ^ (m' + 1)) * ev y a := by
        intro y
        rw [ev_mul_apply, ev_algebraMap]
      obtain ⟨g, hg⟩ := exists_left_translate ev U hU hsurj x1
        (algebraMap R A (ϖ ^ (m' + 1)) * a)
        (fun u hu => by rw [hev']; exact hm _ (W.mul_mem hx1W (hUW hu)))
      have hgS : S g := ⟨fun z hz => by rw [hg, hev']; exact hm _ (W.mul_mem hx1W hz), by
        rw [hg, mul_one, hev']; exact hunit1⟩
      obtain ⟨u, hu, hgu⟩ := hP1 g hgS x1⁻¹ (W.inv_mem hx1W) (hall _ (W.inv_mem hx1W)).2
      rw [hg, ← mul_assoc, mul_inv_cancel, one_mul, hev'] at hgu
      exact not_isIntSmall_of_isIntUnit hgu (isIntSmall_pow_succ_mul hϖ m' ((hU u).1 hu a))
  · push Not at hall
    obtain ⟨x0, hx0W, hx0H⟩ := hall
    have hHW : H ≤ W := fun x hx => ((hH x).1 hx).1
    have hUH' : U ≤ H := fun u hu => (hH u).2 (hUH u hu)
    have hlt : (T.filter (· ∈ H)).card < k := by
      rw [← hk]
      apply Finset.card_lt_card
      have hsub : T.filter (· ∈ H) ⊆ T.filter (· ∈ W) := fun r hr =>
        Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hr).1, hHW (Finset.mem_filter.1 hr).2⟩
      rw [Finset.ssubset_iff_of_subset hsub]
      obtain ⟨r, hrT, hrW, u', hu', rfl⟩ := hWrep x0 hx0W
      refine ⟨r, Finset.mem_filter.2 ⟨hrT, hrW⟩, fun hr => hx0H ((hH _).1 ?_)⟩
      exact H.mul_mem (Finset.mem_filter.1 hr).2 (hUH' hu')
    obtain ⟨g, hgH, hg1, hgsmall⟩ := ih _ hlt H rfl hUH' (hHW.trans hWV)
    obtain ⟨N, hN⟩ := exists_bound ev U hU V T hT hϖ g
    have hev : ∀ x, ev x (g * f0 ^ (N + 1)) = ev x g * ev x f0 ^ (N + 1) := by
      intro x
      rw [ev_mul_apply, ev_pow_apply]
    have hout : ∀ x ∈ W, x ∉ H → IsIntSmall R (ev x (g * f0 ^ (N + 1))) := by
      intro x hxW hxH
      have hf0x : ¬ IsIntUnit R (ev x f0) := fun h =>
        hxH ((hH x).2 ⟨hxW, 1, U.one_mem, by rwa [mul_one]⟩)
      rw [hev]
      exact isIntSmall_mul_pow hϖ (hN x (hWV hxW))
        (isIntSmall_of_not_isIntUnit (hf0S.1 x hxW) hf0x)
    refine ⟨g * f0 ^ (N + 1), fun x hxW => ?_, ?_, fun x hxW hxU => ?_⟩
    · by_cases hxH : x ∈ H
      · rw [hev]
        exact Subring.mul_mem _ (hgH x hxH) (Subring.pow_mem _ (hf0S.1 x hxW) _)
      · exact (hout x hxW hxH).mem_range
    · rw [hev]
      exact hg1.mul (hf0S.2.pow _)
    · by_cases hxH : x ∈ H
      · rw [hev]
        exact (hgsmall x hxH hxU).mul (Subring.pow_mem _ (hf0S.1 x hxW) _)
      · exact hout x hxW hxH

include hU hsurj hUV hnorm hT hpow in
/-- **Separating coordinate.** There is a coordinate integral on `V`, a unit at the identity,
and small at every point of `V` outside `U`. -/
theorem exists_separating :
    ∃ e : A, (∀ x ∈ V, ev x e ∈ (algebraMap R K).range) ∧ IsIntUnit R (ev 1 e) ∧
      ∀ x ∈ V, x ∉ U → IsIntSmall R (ev x e) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact exists_separating_aux ev U hU hsurj V hnorm T hT n hpow hϖ _ V rfl hUV le_rfl

end Separating

end Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement
