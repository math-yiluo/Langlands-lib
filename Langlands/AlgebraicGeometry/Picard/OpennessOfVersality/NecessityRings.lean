import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.ChartOpenness
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Noetherian.Nilpotent

/-! # Artinian test rings realizing a linear form on the conormal module -/

universe u

open CategoryTheory

set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.NecessityRings

open Langlands.Algebra Langlands.AlgebraicGeometry.Deformation

section Local

/-- A noetherian ring with a surjection onto a field whose kernel consists of nilpotent
elements is local Artinian. -/
lemma localArtinian_of_nil {S k : Type u} [CommRing S] [Field k] [IsNoetherianRing S]
    (χ : S →+* k) (hχ : Function.Surjective χ) (hnil : ∀ x ∈ RingHom.ker χ, IsNilpotent x) :
    IsLocalRing S ∧ IsArtinianRing S := by
  haveI : Nontrivial S := χ.domain_nontrivial
  have hunit : ∀ a : S, χ a ≠ 0 → IsUnit a := by
    intro a ha
    obtain ⟨b, hb⟩ := hχ (χ a)⁻¹
    have hn : IsNilpotent (a * b - 1) := hnil _ (by
      rw [RingHom.mem_ker, map_sub, map_mul, hb, mul_inv_cancel₀ ha, map_one, sub_self])
    have : IsUnit (a * b) := by
      have := hn.isUnit_one_add
      rwa [add_sub_cancel] at this
    exact isUnit_of_mul_isUnit_left this
  haveI : IsLocalRing S := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases ha : χ a = 0
    · right
      apply hunit
      rw [map_sub, map_one, ha, sub_zero]
      exact one_ne_zero
    · exact Or.inl (hunit a ha)
  refine ⟨this, ?_⟩
  apply (isArtinianRing_iff_isNilpotent_maximalIdeal S).mpr
  rw [← IsLocalRing.ker_eq_maximalIdeal χ hχ]
  exact (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).mpr
    fun x hx => hnil x hx

end Local

section Ext

variable {R : Type u} [CommRing R] {P : Type u} [CommRing P] [Algebra R P]
  {A₀ : Type u} [CommRing A₀] [Algebra R A₀] [Algebra P A₀] [IsScalarTower R P A₀]
  {k : Type u} [Field k] [Algebra R k] [Algebra A₀ k] [IsScalarTower R A₀ k]
  [Algebra P k] [IsScalarTower P A₀ k]
  {Q : Type u} [AddCommGroup Q] [Module A₀ Q] [Module P Q] [IsScalarTower P A₀ Q]
  (jQ : Q →ₗ[P] P) (φ : Q →ₗ[A₀] k)

variable (P k) in
/-- The ideal of `P` of the residue point. -/
abbrev mP : Ideal P := RingHom.ker (algebraMap P k)

omit [Algebra R P] [IsScalarTower R P A₀] in
include φ in
/-- `φ` vanishes on `m_P • J`. -/
lemma vanish_of_mem_smul (hjQinj : Function.Injective jQ)
    (hJ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ x, jQ x = a)
    {S : Submodule P P} (hS : S ≤ RingHom.ker (algebraMap P A₀)) (x : Q)
    (hx : jQ x ∈ mP P k • S) : φ x = 0 := by
  have key : ∀ a ∈ mP P k • S, ∃ y, jQ y = a ∧ φ y = 0 := by
    intro a ha
    refine Submodule.smul_induction_on (p := fun a => ∃ y, jQ y = a ∧ φ y = 0) ha ?_ ?_
    · intro r hr n hn
      obtain ⟨y, rfl⟩ := (hJ n).mp (hS hn)
      refine ⟨r • y, jQ.map_smul r y, ?_⟩
      rw [LinearMap.map_smul_of_tower, Algebra.smul_def, RingHom.mem_ker.mp hr, zero_mul]
    · rintro a b ⟨y, hy, hy0⟩ ⟨y', hy', hy0'⟩
      exact ⟨y + y', by rw [map_add, hy, hy'], by rw [map_add, hy0, hy0', add_zero]⟩
  obtain ⟨y, hy, hy0⟩ := key _ hx
  rw [hjQinj hy] at hy0
  exact hy0

omit [Algebra R P] [IsScalarTower R P A₀] in
/-- **Artin–Rees.** `φ` vanishes on the elements of `J` lying in a high power of `m_P`. -/
lemma exists_pow_vanish [IsNoetherianRing P] (hjQinj : Function.Injective jQ)
    (hJ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ x, jQ x = a) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : Q, jQ x ∈ mP P k ^ N → φ x = 0 := by
  obtain ⟨n₀, hn₀⟩ := Ideal.exists_pow_inf_eq_pow_smul (mP P k)
    (RingHom.ker (algebraMap P A₀) : Submodule P P)
  refine ⟨n₀ + 1, Nat.succ_pos _, fun x hx => ?_⟩
  have hmem : jQ x ∈ (mP P k ^ (n₀ + 1) • ⊤ ⊓ RingHom.ker (algebraMap P A₀) : Submodule P P) := by
    refine ⟨?_, (hJ _).mpr ⟨x, rfl⟩⟩
    change jQ x ∈ (mP P k ^ (n₀ + 1) • ⊤ : Ideal P)
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hx
  rw [hn₀ (n₀ + 1) (Nat.le_succ n₀), Nat.add_sub_cancel_left, pow_one] at hmem
  exact vanish_of_mem_smul jQ φ hjQinj hJ inf_le_right x hmem

end Ext

section Rings

variable {R : Type u} [CommRing R] {P : Type u} [CommRing P] [Algebra R P]
  {A₀ : Type u} [CommRing A₀] [Algebra R A₀] [Algebra P A₀] [IsScalarTower R P A₀]
  {k : Type u} [Field k] [Algebra R k] [Algebra A₀ k] [IsScalarTower R A₀ k]
  [Algebra P k] [IsScalarTower P A₀ k]
  {Q : Type u} [AddCommGroup Q] [Module A₀ Q] [Module P Q] [IsScalarTower P A₀ Q]
  (jQ : Q →ₗ[P] P) (φ : Q →ₗ[A₀] k) (N : ℕ) (hN : 0 < N)
  (hjQ0 : ∀ x, algebraMap P A₀ (jQ x) = 0)

omit [Algebra R P] [IsScalarTower R P A₀] [Module A₀ Q] [IsScalarTower P A₀ Q] in
include hN hjQ0 in
lemma smul_eq_zero_of_mem (x : Q) (m : P) (hm : m ∈ mP P k ^ N) (t : k) :
    (jQ x + m) • t = 0 := by
  have hm' : m ∈ mP P k := Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hN) hm
  rw [Algebra.smul_def, map_add, IsScalarTower.algebraMap_apply P A₀ k (jQ x), hjQ0,
    map_zero, RingHom.mem_ker.mp hm', add_zero, zero_mul]

/-- The ideal `{(jQ x + m, -φ x) | x ∈ Q, m ∈ m_P^N}` of `P ⊕ k`. -/
def extIdeal : Ideal (Thick P k) where
  carrier := {y | ∃ x : Q, ∃ m ∈ mP P k ^ N, y = Thick.inl (jQ x + m) - Thick.inr (φ x)}
  add_mem' := by
    rintro _ _ ⟨x, m, hm, rfl⟩ ⟨x', m', hm', rfl⟩
    refine ⟨x + x', m + m', add_mem hm hm', ?_⟩
    ext
    · simp only [Thick.fst_add, Thick.fst_sub, Thick.fst_inl, Thick.fst_inr, map_add]
      abel
    · simp only [Thick.snd_add, Thick.snd_sub, Thick.snd_inl, Thick.snd_inr, map_add]
      abel
  zero_mem' := ⟨0, 0, zero_mem _, by ext <;> simp⟩
  smul_mem' := by
    rintro c _ ⟨x, m, hm, rfl⟩
    refine ⟨Thick.fst c • x, Thick.fst c * m, Ideal.mul_mem_left _ _ hm, ?_⟩
    ext
    · change Thick.fst (c * _) = _
      simp only [Thick.fst_mul, Thick.fst_sub, Thick.fst_inl, Thick.fst_inr, sub_zero,
        LinearMap.map_smul, smul_eq_mul]
      ring
    · change Thick.snd (c * _) = _
      simp only [Thick.snd_mul, Thick.fst_sub, Thick.snd_sub, Thick.fst_inl, Thick.fst_inr,
        Thick.snd_inl, Thick.snd_inr, sub_zero, zero_sub, smul_neg]
      rw [smul_eq_zero_of_mem jQ N hN hjQ0 x m hm, add_zero, LinearMap.map_smul_of_tower]

/-- The extension ring `(P ⊕ k) / extIdeal`. -/
abbrev ExtRing := Thick P k ⧸ extIdeal jQ φ N hN hjQ0

/-- The inclusion of `k` into the extension ring. -/
def ι : k →ₗ[P] ExtRing jQ φ N hN hjQ0 :=
  (Ideal.Quotient.mkₐ P (extIdeal jQ φ N hN hjQ0)).toLinearMap ∘ₗ Thick.inr

lemma ι_apply (t : k) :
    ι jQ φ N hN hjQ0 t = Ideal.Quotient.mk (extIdeal jQ φ N hN hjQ0) (Thick.inr t) := rfl

lemma ι_mul_ι (t t' : k) : ι jQ φ N hN hjQ0 t * ι jQ φ N hN hjQ0 t' = 0 := by
  rw [ι_apply, ι_apply, ← map_mul, Thick.inr_mul_inr, map_zero]

lemma algebraMap_jQ (x : Q) :
    algebraMap P (ExtRing jQ φ N hN hjQ0) (jQ x) = ι jQ φ N hN hjQ0 (φ x) := by
  rw [ι_apply, IsScalarTower.algebraMap_apply P (Thick P k), Ideal.Quotient.algebraMap_eq]
  apply Ideal.Quotient.eq.mpr
  refine ⟨x, 0, zero_mem _, ?_⟩
  rw [add_zero]
  rfl

omit [Algebra R P] [IsScalarTower R P A₀] in
include hN hjQ0 in
lemma ι_injective (hvan : ∀ x : Q, jQ x ∈ mP P k ^ N → φ x = 0) :
    Function.Injective (ι jQ φ N hN hjQ0) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  rw [ι_apply, Ideal.Quotient.eq_zero_iff_mem] at ht
  obtain ⟨x, m, hm, hxm⟩ := ht
  have h1 := congrArg Thick.fst hxm
  have h2 := congrArg Thick.snd hxm
  simp only [Thick.fst_inr, Thick.fst_sub, Thick.fst_inl, Thick.snd_inr, Thick.snd_sub,
    Thick.snd_inl, zero_sub] at h1 h2
  have hx : jQ x ∈ mP P k ^ N := by
    have : jQ x = -m := by linear_combination -h1
    rw [this]
    exact neg_mem hm
  rw [h2, hvan x hx, neg_zero]

section Base

variable (A₀ k) in
/-- The maximal ideal of the residue point. -/
abbrev mA : Ideal A₀ := RingHom.ker (algebraMap A₀ k)

variable (A₀ k) in
/-- The Artinian quotient `A₀ / m^N`. -/
abbrev BaseRing := A₀ ⧸ mA A₀ k ^ N

variable (R A₀ k) in
/-- The chart map `A₀ → A₀ / m^N`. -/
def chiN : A₀ →ₐ[R] BaseRing A₀ k N := Ideal.Quotient.mkₐ R _

omit [Algebra R P] [IsScalarTower R P A₀] [Algebra R k] [IsScalarTower R A₀ k] in
lemma map_mP_le : Ideal.map (algebraMap P A₀) (mP P k) ≤ mA A₀ k := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
  exact ha

omit [Algebra R P] [IsScalarTower R P A₀] [Algebra R k] [IsScalarTower R A₀ k] in
lemma map_mP_eq (hπ : Function.Surjective (algebraMap P A₀)) :
    Ideal.map (algebraMap P A₀) (mP P k) = mA A₀ k := by
  have : mP P k = Ideal.comap (algebraMap P A₀) (mA A₀ k) := by
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
  rw [this, Ideal.map_comap_of_surjective _ hπ]

variable (R) in
/-- The reduction `ExtRing → A₀ / m^N`, `(p, t) ↦ p mod m^N`. -/
def qE : ExtRing jQ φ N hN hjQ0 →ₐ[R] BaseRing A₀ k N :=
  Ideal.Quotient.liftₐ (extIdeal jQ φ N hN hjQ0)
    ((chiN R A₀ k N).comp ((IsScalarTower.toAlgHom R P A₀).comp (Thick.fstAlgHom R)))
    (by
      rintro _ ⟨x, m, hm, rfl⟩
      change Ideal.Quotient.mk _ (algebraMap P A₀ (jQ x + m - 0)) = 0
      rw [sub_zero, map_add, hjQ0, zero_add, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_right_mono (map_mP_le (k := k)) N
        (Ideal.map_pow (algebraMap P A₀) (mP P k) N ▸ Ideal.mem_map_of_mem _ hm))

omit [Algebra R k] [IsScalarTower R A₀ k] in
lemma qE_algebraMap (p : P) :
    qE R jQ φ N hN hjQ0 (algebraMap P (ExtRing jQ φ N hN hjQ0) p) =
      chiN R A₀ k N (algebraMap P A₀ p) := rfl

omit [Algebra R k] [IsScalarTower R A₀ k] in
lemma qE_ι (t : k) : qE R jQ φ N hN hjQ0 (ι jQ φ N hN hjQ0 t) = 0 := by
  change chiN R A₀ k N (algebraMap P A₀ 0) = 0
  rw [map_zero, map_zero]

omit [Algebra R k] [IsScalarTower R A₀ k] in
lemma qE_comp : (qE R jQ φ N hN hjQ0).comp (IsScalarTower.toAlgHom R P (ExtRing jQ φ N hN hjQ0)) =
    (chiN R A₀ k N).comp (IsScalarTower.toAlgHom R P A₀) := rfl

omit [Algebra R k] [IsScalarTower R A₀ k] in
lemma qE_surjective (hπ : Function.Surjective (algebraMap P A₀)) :
    Function.Surjective (qE R jQ φ N hN hjQ0) := by
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨p, rfl⟩ := hπ a
  exact ⟨algebraMap P _ p, rfl⟩

omit [Algebra R k] [IsScalarTower R A₀ k] in
lemma exists_ι_of_qE_eq_zero (hπ : Function.Surjective (algebraMap P A₀))
    (hJ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ x, jQ x = a)
    (a : ExtRing jQ φ N hN hjQ0) (ha : qE R jQ φ N hN hjQ0 a = 0) :
    ∃ t, ι jQ φ N hN hjQ0 t = a := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h1 : algebraMap P A₀ (Thick.fst y) ∈ mA A₀ k ^ N := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact ha
  rw [← map_mP_eq hπ, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ hπ] at h1
  obtain ⟨m, hm, hmy⟩ := h1
  obtain ⟨x, hx⟩ := (hJ (Thick.fst y - m)).mp (by
    rw [RingHom.mem_ker, map_sub, hmy, sub_self])
  refine ⟨Thick.snd y + φ x, ?_⟩
  rw [ι_apply]
  refine (Ideal.Quotient.eq.mpr (show y - Thick.inr (Thick.snd y + φ x) ∈
    extIdeal jQ φ N hN hjQ0 from ⟨x, m, hm, ?_⟩)).symm
  ext
  · simp only [Thick.fst_sub, Thick.fst_inr, Thick.fst_inl, hx]
    ring
  · simp only [Thick.snd_sub, Thick.snd_inr, Thick.snd_inl]
    abel

end Base

section Tests

variable (R) in
/-- The augmentation `A₀ / m^N → k`. -/
def augB : BaseRing A₀ k N →ₐ[R] k :=
  Ideal.Quotient.liftₐ _ (IsScalarTower.toAlgHom R A₀ k) (fun _ ha =>
    RingHom.mem_ker.mp (Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hN) ha))

omit [Algebra P A₀] [Algebra P k] [IsScalarTower P A₀ k] in
include hN in
lemma augB_surjective (hk : Function.Surjective (algebraMap A₀ k)) :
    Function.Surjective (augB R N hN (A₀ := A₀) (k := k)) := by
  intro t
  obtain ⟨a, rfl⟩ := hk t
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

omit [Algebra P A₀] [Algebra P k] [IsScalarTower P A₀ k] in
lemma augB_nil (b : BaseRing A₀ k N) (hb : b ∈ RingHom.ker (augB R N hN (A₀ := A₀) (k := k))) :
    IsNilpotent b := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  have ha : a ∈ mA A₀ k := hb
  exact ⟨N, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow ha N⟩

variable (R) in
/-- The augmentation of the extension ring. -/
def augE : ExtRing jQ φ N hN hjQ0 →ₐ[R] k := (augB R N hN).comp (qE R jQ φ N hN hjQ0)

omit [Algebra R k] [IsScalarTower R A₀ k] in
lemma algebraMap_mem_extIdeal (p : P) (hp : p ∈ mP P k ^ N) :
    Thick.inl p ∈ extIdeal jQ φ N hN hjQ0 :=
  ⟨0, p, hp, by ext <;> simp⟩

lemma augE_nil (a : ExtRing jQ φ N hN hjQ0) (ha : a ∈ RingHom.ker (augE R jQ φ N hN hjQ0)) :
    IsNilpotent a := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hp : Thick.fst y ∈ mP P k := by
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply P A₀ k]
    exact ha
  have hy : y = Thick.inl (Thick.fst y) + Thick.inr (Thick.snd y) := Thick.eq_inl_add_inr y
  rw [hy, map_add]
  refine (Commute.all _ _).isNilpotent_add ?_ ?_
  · refine ⟨N, ?_⟩
    rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact algebraMap_mem_extIdeal jQ φ N hN hjQ0 _ (Ideal.pow_mem_pow hp N)
  · refine ⟨2, ?_⟩
    rw [pow_two, ← map_mul, Thick.inr_mul_inr, map_zero]

lemma augE_surjective (hk : Function.Surjective (algebraMap A₀ k))
    (hπ : Function.Surjective (algebraMap P A₀)) :
    Function.Surjective (augE R jQ φ N hN hjQ0) :=
  (augB_surjective N hN hk).comp (qE_surjective jQ φ N hN hjQ0 hπ)

omit [Algebra R P] [IsScalarTower R P A₀] [Algebra R k] [IsScalarTower R A₀ k] in
lemma isNoetherianRing_thick [IsNoetherianRing P] (hk : Function.Surjective (algebraMap P k)) :
    IsNoetherianRing (Thick P k) := by
  let L : (P × P) →ₗ[P] Thick P k := LinearMap.coprod (Algebra.linearMap P (Thick P k))
    (LinearMap.toSpanSingleton P (Thick P k) (Thick.inr 1))
  have hL : Function.Surjective L := by
    intro y
    obtain ⟨b, hb⟩ := hk (Thick.snd y)
    refine ⟨(Thick.fst y, b), ?_⟩
    change algebraMap P (Thick P k) (Thick.fst y) + b • Thick.inr 1 = y
    ext
    · simp
    · simp [Algebra.smul_def, hb]
  have h1 : IsNoetherian P (Thick P k) :=
    isNoetherian_of_surjective L (LinearMap.range_eq_top.mpr hL)
  exact isNoetherian_of_tower P h1

end Tests

section TestObjects

variable [IsNoetherianRing P] [IsNoetherianRing A₀]
  (hk : Function.Surjective (algebraMap A₀ k)) (hπ : Function.Surjective (algebraMap P A₀))

variable (R) in
include R hN hk in
omit [Algebra P A₀] [Algebra P k] [IsScalarTower P A₀ k] [IsNoetherianRing P] in
lemma baseRing_localArtinian : IsLocalRing (BaseRing A₀ k N) ∧ IsArtinianRing (BaseRing A₀ k N) :=
  localArtinian_of_nil (augB R N hN (A₀ := A₀) (k := k)).toRingHom (augB_surjective N hN hk)
    (fun x hx => augB_nil N hN x hx)

variable (R) in
include hk in
/-- The Artinian test `A₀ / m^N`. -/
def baseTest : ArtinianTest R k := by
  have h := baseRing_localArtinian R N hN hk
  haveI := h.1
  haveI := h.2
  exact ArtinianTest.mk (BaseRing A₀ k N) (augB R N hN) (augB_surjective N hN hk)

variable (R) in
include R hk hπ in
omit [IsNoetherianRing A₀] in
lemma extRing_localArtinian :
    IsLocalRing (ExtRing jQ φ N hN hjQ0) ∧ IsArtinianRing (ExtRing jQ φ N hN hjQ0) := by
  have hkP : Function.Surjective (algebraMap P k) := by
    rw [IsScalarTower.algebraMap_eq P A₀ k]
    exact hk.comp hπ
  haveI := isNoetherianRing_thick hkP
  exact localArtinian_of_nil (augE R jQ φ N hN hjQ0).toRingHom
    (augE_surjective jQ φ N hN hjQ0 hk hπ) (fun x hx => augE_nil jQ φ N hN hjQ0 x hx)

variable (R) in
include hk hπ in
/-- The Artinian test given by the extension ring. -/
def extTest : ArtinianTest R k := by
  have h := extRing_localArtinian R jQ φ N hN hjQ0 hk hπ
  haveI := h.1
  haveI := h.2
  exact ArtinianTest.mk (ExtRing jQ φ N hN hjQ0) (augE R jQ φ N hN hjQ0)
    (augE_surjective jQ φ N hN hjQ0 hk hπ)

variable (R) in
/-- The test arrow `ExtRing → A₀ / m^N`. -/
def qTest : extTest R jQ φ N hN hjQ0 hk hπ ⟶ baseTest R N hN hk :=
  ArtinianTest.homMk (qE R jQ φ N hN hjQ0) rfl

lemma toAlgHom_qTest :
    ArtinianTest.toAlgHom (qTest R jQ φ N hN hjQ0 hk hπ) = qE R jQ φ N hN hjQ0 := rfl

end TestObjects

end Rings

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.NecessityRings
