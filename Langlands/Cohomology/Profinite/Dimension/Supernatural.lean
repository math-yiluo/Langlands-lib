import Langlands.Cohomology.Profinite.OpenNormal
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.Factorization.Basic

namespace Langlands.ProfiniteCohomology

def Supernatural : Type := Nat.Primes → ℕ∞

namespace Supernatural

def mk (f : Nat.Primes → ℕ∞) : Supernatural := f

def exp (a : Supernatural) (p : Nat.Primes) : ℕ∞ := a p

@[simp] theorem exp_mk (f : Nat.Primes → ℕ∞) (p : Nat.Primes) : (mk f).exp p = f p := rfl

@[ext] theorem ext {a b : Supernatural} (h : ∀ p, a.exp p = b.exp p) : a = b := funext h

noncomputable instance : CompleteLattice Supernatural := inferInstanceAs (CompleteLattice (Nat.Primes → ℕ∞))

theorem le_def {a b : Supernatural} : a ≤ b ↔ ∀ p, a.exp p ≤ b.exp p := Iff.rfl

@[simp] theorem exp_iSup {ι : Sort*} (f : ι → Supernatural) (p : Nat.Primes) :
    (⨆ i, f i).exp p = ⨆ i, (f i).exp p :=
  iSup_apply (f := fun i => (f i : Nat.Primes → ℕ∞)) (a := p)

instance : One Supernatural := ⟨mk fun _ => 0⟩

instance : Mul Supernatural := ⟨fun a b => mk fun p => a.exp p + b.exp p⟩

@[simp] theorem exp_one (p : Nat.Primes) : (1 : Supernatural).exp p = 0 := rfl

@[simp] theorem exp_mul (a b : Supernatural) (p : Nat.Primes) :
    (a * b).exp p = a.exp p + b.exp p := rfl

instance : CommMonoid Supernatural where
  mul_assoc a b c := by ext p; simp [add_assoc]
  one_mul a := by ext p; simp
  mul_one a := by ext p; simp
  mul_comm a b := by ext p; simp [add_comm]

theorem dvd_iff_le {a b : Supernatural} : a ∣ b ↔ a ≤ b := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [le_def]
    intro p
    simp
  · intro h
    refine ⟨mk fun p => b.exp p - a.exp p, ?_⟩
    ext p
    simp [add_tsub_cancel_of_le (le_def.mp h p)]

def ofNat (n : ℕ) : Supernatural := mk fun p => (n.factorization p : ℕ∞)

@[simp] theorem exp_ofNat (n : ℕ) (p : Nat.Primes) : (ofNat n).exp p = n.factorization p := rfl

@[simp] theorem ofNat_one : ofNat 1 = 1 := by ext p; simp

theorem ofNat_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : ofNat (m * n) = ofNat m * ofNat n := by
  ext p
  simp [Nat.factorization_mul hm hn]

theorem ofNat_dvd_ofNat {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : ofNat m ∣ ofNat n ↔ m ∣ n := by
  rw [dvd_iff_le, le_def, ← Nat.factorization_le_iff_dvd hm hn, Finsupp.le_def]
  constructor
  · intro h q
    by_cases hq : q.Prime
    · have h' : ((m.factorization q : ℕ) : ℕ∞) ≤ n.factorization q := h ⟨q, hq⟩
      exact_mod_cast h'
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  · intro h p
    show ((m.factorization p : ℕ) : ℕ∞) ≤ n.factorization p
    exact_mod_cast h p

theorem ofNat_injective {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : ofNat m = ofNat n ↔ m = n := by
  refine ⟨fun h => Nat.dvd_antisymm ?_ ?_, fun h => h ▸ rfl⟩
  · exact (ofNat_dvd_ofNat hm hn).mp (h ▸ dvd_rfl)
  · exact (ofNat_dvd_ofNat hn hm).mp (h ▸ dvd_rfl)

theorem ofNat_prime_dvd_iff (p : Nat.Primes) (a : Supernatural) :
    ofNat p ∣ a ↔ 1 ≤ a.exp p := by
  have h1 : (ofNat p).exp p = 1 := by
    rw [exp_ofNat]
    simp [p.prop.factorization_self]
  rw [dvd_iff_le, le_def]
  constructor
  · intro h
    exact h1 ▸ h p
  · intro h q
    by_cases hq : q = p
    · subst hq
      exact h1 ▸ h
    · have hq' : (p : ℕ) ≠ q := fun e => hq (Subtype.ext e.symm)
      simp [p.prop.factorization, hq']

theorem ofNat_prime_dvd_iSup_iff (p : Nat.Primes) {ι : Sort*} (f : ι → Supernatural) :
    ofNat p ∣ ⨆ i, f i ↔ ∃ i, ofNat p ∣ f i := by
  simp only [ofNat_prime_dvd_iff p, Order.one_le_iff_ne_zero]
  rw [exp_iSup]
  constructor
  · intro h
    by_contra h'
    simp only [not_exists, ne_eq, not_not] at h'
    exact h (le_antisymm (iSup_le fun i => (h' i).le) zero_le)
  · rintro ⟨i, hi⟩ h
    exact hi (le_antisymm (h ▸ le_iSup (fun i => (f i).exp p) i) zero_le)

theorem iSup_mul_iSup {ι : Sort*} {f g : ι → Supernatural}
    (h : ∀ i j, ∃ k, f i ≤ f k ∧ g j ≤ g k) :
    (⨆ i, f i) * (⨆ i, g i) = ⨆ i, f i * g i := by
  ext p
  simp only [exp_mul, exp_iSup]
  exact ENat.iSup_add_iSup fun i j => (h i j).imp fun k hk =>
    add_le_add (le_def.mp hk.1 p) (le_def.mp hk.2 p)

end Supernatural

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open Topology

variable {G : Type*} [Group G]

theorem inf_sup_normal_eq {X H U : Subgroup G} [U.Normal] (hUX : U ≤ X) :
    X ⊓ (H ⊔ U) = (X ⊓ H) ⊔ U := by
  refine le_antisymm (fun x hx => ?_) (sup_le (inf_le_inf_left _ le_sup_left) (le_inf hUX le_sup_right))
  obtain ⟨hxX, hxHU⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨h, hh, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxHU
  have hhX : h ∈ X := by
    have := X.mul_mem hxX (X.inv_mem (hUX hu))
    rwa [mul_inv_cancel_right] at this
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hhX, hh⟩) hu

theorem relIndex_sup_normal_eq {X H U : Subgroup G} [U.Normal] [U.FiniteIndex] (hUX : U ≤ X) :
    X.relIndex (H ⊔ U) = X.relIndex H := by
  have h1 := Subgroup.relIndex_inf_mul_relIndex U X (H ⊔ U)
  have h2 := Subgroup.relIndex_inf_mul_relIndex U X H
  rw [inf_eq_left.mpr hUX, Subgroup.relIndex_sup_right, inf_sup_normal_eq hUX,
    Subgroup.relIndex_sup_right] at h1
  rw [inf_eq_left.mpr hUX] at h2
  have hne : U.relIndex (X ⊓ H) ≠ 0 := fun h0 =>
    Subgroup.FiniteIndex.index_ne_zero (H := U)
      (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_index_of_normal U (X ⊓ H)))
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) (h1.trans h2.symm)

theorem index_sup_normal_eq_mul {K H U : Subgroup G} [U.Normal] [U.FiniteIndex] (hKH : K ≤ H) :
    (K ⊔ U).index = (H ⊔ U).index * (K ⊔ U).relIndex H := by
  rw [← Subgroup.relIndex_mul_index (sup_le_sup_right hKH U),
    relIndex_sup_normal_eq (le_sup_right : U ≤ K ⊔ U), mul_comm]

theorem sup_subgroupOf_eq {K H U : Subgroup G} [U.Normal] (hKH : K ≤ H) :
    (K ⊔ U).subgroupOf H = K.subgroupOf H ⊔ U.subgroupOf H := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le (fun x hx => Subgroup.mem_subgroupOf.mpr ((le_sup_left : K ≤ K ⊔ U) (Subgroup.mem_subgroupOf.mp hx)))
      (fun x hx => Subgroup.mem_subgroupOf.mpr ((le_sup_right : U ≤ K ⊔ U) (Subgroup.mem_subgroupOf.mp hx))))
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨k, hk, u, hu, hku⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  have hkH : k ∈ H := hKH hk
  have huH : u ∈ H := by
    have := H.mul_mem (H.inv_mem hkH) x.2
    rwa [← hku, inv_mul_cancel_left] at this
  have hx' : x = ⟨k, hkH⟩ * ⟨u, huH⟩ := Subtype.ext hku.symm
  rw [hx']
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hk) (Subgroup.mem_subgroupOf.mpr hu)

variable [TopologicalSpace G]

noncomputable def superIndex (H : Subgroup G) : Supernatural :=
  ⨆ U : OpenNormalSubgroup G, Supernatural.ofNat (H ⊔ (U : Subgroup G)).index

noncomputable def superRelIndex (K H : Subgroup G) : Supernatural :=
  superIndex (K.subgroupOf H)

variable [IsTopologicalGroup G] [CompactSpace G]

instance OpenNormalSubgroup.finiteIndex (U : OpenNormalSubgroup G) :
    (U : Subgroup G).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

theorem index_sup_ne_zero (H : Subgroup G) (U : OpenNormalSubgroup G) :
    (H ⊔ (U : Subgroup G)).index ≠ 0 :=
  fun h => Subgroup.FiniteIndex.index_ne_zero (H := (U : Subgroup G))
    (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le le_sup_right))

theorem relIndex_sup_ne_zero (K H : Subgroup G) (U : OpenNormalSubgroup G) :
    (K ⊔ (U : Subgroup G)).relIndex H ≠ 0 :=
  fun h => Subgroup.FiniteIndex.index_ne_zero (H := (U : Subgroup G))
    (Nat.eq_zero_of_zero_dvd (h ▸ (Subgroup.relIndex_dvd_of_le_left H le_sup_right).trans
      (Subgroup.relIndex_dvd_index_of_normal (U : Subgroup G) H)))

theorem ofNat_index_sup_antitone (H : Subgroup G) {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    Supernatural.ofNat (H ⊔ (V : Subgroup G)).index ≤
      Supernatural.ofNat (H ⊔ (U : Subgroup G)).index := by
  rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat (index_sup_ne_zero H V)
    (index_sup_ne_zero H U)]
  exact Subgroup.index_dvd_of_le (sup_le_sup_left (fun x hx => h hx) H)

theorem ofNat_relIndex_sup_antitone (K H : Subgroup G) {U V : OpenNormalSubgroup G}
    (h : U ≤ V) :
    Supernatural.ofNat ((K ⊔ (V : Subgroup G)).relIndex H) ≤
      Supernatural.ofNat ((K ⊔ (U : Subgroup G)).relIndex H) := by
  rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat (relIndex_sup_ne_zero K H V)
    (relIndex_sup_ne_zero K H U)]
  exact Subgroup.relIndex_dvd_of_le_left H (sup_le_sup_left (fun x hx => h hx) K)

theorem not_dvd_superIndex_iff (p : Nat.Primes) (H : Subgroup G) :
    ¬ Supernatural.ofNat p ∣ superIndex H ↔
      ∀ U : OpenNormalSubgroup G, ¬ (p : ℕ) ∣ (H ⊔ (U : Subgroup G)).index := by
  rw [superIndex, Supernatural.ofNat_prime_dvd_iSup_iff, not_exists]
  refine forall_congr' fun U => ?_
  rw [Supernatural.ofNat_dvd_ofNat p.prop.ne_zero (index_sup_ne_zero H U)]

theorem superRelIndex_eq_iSup [TotallyDisconnectedSpace G] {K H : Subgroup G} (hKH : K ≤ H) :
    superRelIndex K H =
      ⨆ U : OpenNormalSubgroup G, Supernatural.ofNat ((K ⊔ (U : Subgroup G)).relIndex H) := by

  let res : OpenNormalSubgroup G → OpenNormalSubgroup H := fun U =>
    { toSubgroup := (U : Subgroup G).subgroupOf H
      isOpen' := Subgroup.subgroupOf_isOpen H (U : Subgroup G) U.toOpenSubgroup.isOpen
      isNormal' := inferInstance }
  have hres : ∀ U : OpenNormalSubgroup G,
      K.subgroupOf H ⊔ ((res U : OpenNormalSubgroup H) : Subgroup H) =
        (K ⊔ (U : Subgroup G)).subgroupOf H :=
    fun U => (sup_subgroupOf_eq hKH).symm
  refine le_antisymm (iSup_le fun V => ?_) (iSup_le fun U => ?_)
  ·
    obtain ⟨W, hWo, hWV⟩ := isOpen_induced_iff.mp V.toOpenSubgroup.isOpen
    have h1W : (1 : G) ∈ W := by
      have : (1 : H) ∈ Subtype.val ⁻¹' W := hWV ▸ V.one_mem
      simpa using this
    obtain ⟨U, hUW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1W
    refine le_iSup_of_le U ?_
    have hle : (K ⊔ (U : Subgroup G)).subgroupOf H ≤ K.subgroupOf H ⊔ (V : Subgroup H) := by
      rw [← hres U]
      refine sup_le_sup_left (fun x hx => ?_) _
      have : (x : G) ∈ W := hUW hx
      have : x ∈ Subtype.val ⁻¹' W := this
      rw [hWV] at this
      exact this
    have hne : ((K ⊔ (U : Subgroup G)).subgroupOf H).index ≠ 0 := relIndex_sup_ne_zero K H U
    show Supernatural.ofNat _ ≤ Supernatural.ofNat ((K ⊔ (U : Subgroup G)).subgroupOf H).index
    rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat
      (fun h => hne (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hle))) hne]
    exact Subgroup.index_dvd_of_le hle
  · refine le_iSup_of_le (res U) ?_
    rw [hres U]
    exact le_rfl

theorem superIndex_of_isOpen [TotallyDisconnectedSpace G] {H : Subgroup G}
    (hH : IsOpen (H : Set G)) : superIndex H = Supernatural.ofNat H.index := by
  have : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hH H.one_mem
  refine le_antisymm (iSup_le fun V => ?_) (le_iSup_of_le U ?_)
  · rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat (index_sup_ne_zero H V) hne]
    exact Subgroup.index_dvd_of_le le_sup_left
  · rw [sup_eq_left.mpr (fun x hx => hU hx)]

theorem superIndex_eq_mul [TotallyDisconnectedSpace G] {K H : Subgroup G} (hKH : K ≤ H) :
    superIndex K = superIndex H * superRelIndex K H := by
  rw [superRelIndex_eq_iSup hKH, superIndex, superIndex,
    Supernatural.iSup_mul_iSup fun U V =>
      ⟨U ⊓ V, ofNat_index_sup_antitone H inf_le_left, ofNat_relIndex_sup_antitone K H inf_le_right⟩]
  refine iSup_congr fun U => ?_
  rw [index_sup_normal_eq_mul hKH, Supernatural.ofNat_mul (index_sup_ne_zero H U)
    (relIndex_sup_ne_zero K H U)]

theorem superIndex_dvd_of_le [TotallyDisconnectedSpace G] {K H : Subgroup G} (hKH : K ≤ H) :
    superIndex H ∣ superIndex K :=
  ⟨superRelIndex K H, superIndex_eq_mul hKH⟩

end Langlands.ProfiniteCohomology
