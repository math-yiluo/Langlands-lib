import Langlands.Representation.Aubert.General.CuspidalCoefficientVanishing
import Langlands.Representation.Aubert.General.CartanLatticeContraction

/-!
# Bounds on Cartan pairings from vanishing proper Jacquet modules

Finite genuine relation witnesses and the wall-contraction gap argument bound
all simple-root pairings on the nonzero set of an individual coefficient.
-/

noncomputable section

open Filter Topology

namespace Langlands.Aubert.General

universe uR uG uV uW uD uX

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  {Δ : Type uD} [Fintype Δ]
  {X : Type uX} [AddCommGroup X]
  {levi unipotent : Finset Δ → Subgroup G}
  {cartanSet : Finset Δ → Set G} {e : Multiplicative X →* G}
  {pair : Δ → X →+ ℤ} {F₀ : Set G}

namespace IsCartanLatticeModel

/-- If every proper wall kills `v` in its actual Jacquet quotient, then the
pairings of dominant lattice translates with nonzero image under `L` are bounded. -/
theorem exists_coefficient_pairing_bound
    (hM : IsCartanLatticeModel levi unipotent cartanSet e pair F₀)
    (htop : levi Finset.univ = ⊤)
    (ρ : Representation R G V) (K : OpenSubgroup G) (L : V →ₗ[R] W)
    (hL : ∀ k ∈ K, ∀ w : V, L (ρ k w) = L w) (v : V)
    (hv : ∀ J : Finset Δ, J ≠ Finset.univ → v ∈ Jacquet.relations ρ (unipotent J)) :
    ∃ B : ℤ, ∀ x : X, (∀ β, 0 ≤ pair β x) → ∀ f ∈ F₀,
      L (ρ (e (.ofAdd x) * f) v) ≠ 0 → ∀ β, pair β x ≤ B := by
  classical
  let I : Finset Δ := Finset.univ
  let s : (J : {J : Finset Δ // J ⊂ I}) → Finset (unipotent J.1) := fun J =>
    Jacquet.relationContractionWitness ρ (unipotent J.1) K.toSubgroup L hL
      (hv J.1 (by simpa [I, Finset.ssubset_univ_iff] using J.2))
  let S : {J : Finset Δ // J ⊂ I} → Finset G := fun J => (s J).image Subtype.val
  have hS : ∀ J, (S J : Set G) ⊆ unipotent J.1 ⊓ levi I := by
    intro J u hu
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨n.2, by rw [show levi I = ⊤ from htop]; trivial⟩
  have hvanish : ∀ J : {J : Finset Δ // J ⊂ I}, ∀ g : G,
      (∀ u ∈ S J, g * u * g⁻¹ ∈ K) → L (ρ g v) = 0 := by
    intro J g hg
    exact Jacquet.relationContractionWitness_spec ρ (unipotent J.1) K.toSubgroup L hL
      (hv J.1 (by simpa [I, Finset.ssubset_univ_iff] using J.2)) g
      (fun n hn => hg n (Finset.mem_image_of_mem _ hn))
  have hO : (K : Set G) ∈ 𝓝 (1 : G) := K.isOpen.mem_nhds K.one_mem
  have hstep : ∀ T : ℤ, ∃ T', T < T' ∧ ∀ J : {J : Finset Δ // J ⊂ I}, ∀ x : X,
      (∀ β ∈ J.1, 0 ≤ pair β x ∧ pair β x ≤ T) →
      (∀ β ∈ I, β ∉ J.1 → T' ≤ pair β x) →
      ∀ f ∈ F₀, ∀ u ∈ S J, e (.ofAdd x) * f * u * (e (.ofAdd x) * f)⁻¹ ∈ K := by
    intro T
    obtain ⟨T', hT', hcon⟩ := ((eventually_gt_atTop T).and
      (hM.eventually_wall_contraction I hO S hS 0 T)).exists
    refine ⟨T', hT', fun J x hx hy f hf u hu => ?_⟩
    exact hcon J x (by simpa only [neg_zero] using hx) hy f hf u hu
  choose next hnext_gt hnext using hstep
  let T : ℕ → ℤ := fun k => next^[k] 0
  have hTsucc : ∀ k, T (k + 1) = next (T k) := fun k =>
    Function.iterate_succ_apply' next k 0
  have hTmono : Monotone T := monotone_nat_of_le_succ fun k => by
    rw [hTsucc k]
    exact (hnext_gt (T k)).le
  refine ⟨T I.card, fun x hx f hf hnonzero β => ?_⟩
  let Jk : ℕ → Finset Δ := fun k => I.filter fun β => pair β x < T k
  have hJmono : ∀ k, Jk k ⊆ Jk (k + 1) := fun k β hβ => by
    simp only [Jk, Finset.mem_filter] at hβ ⊢
    exact ⟨hβ.1, hβ.2.trans_le (hTmono (Nat.le_succ k))⟩
  obtain ⟨k, hk, hsub⟩ : ∃ k ≤ I.card, Jk (k + 1) ⊆ Jk k := by
    by_contra hcon
    push Not at hcon
    have hcard : ∀ k ≤ I.card + 1, k ≤ (Jk k).card := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
        intro hk
        have hlt : (Jk k).card < (Jk (k + 1)).card :=
          Finset.card_lt_card ⟨hJmono k, hcon k (by omega)⟩
        have := ih (by omega)
        omega
    have h1 := hcard (I.card + 1) le_rfl
    have h2 : (Jk (I.card + 1)).card ≤ I.card := Finset.card_filter_le _ _
    omega
  by_cases hJI : Jk k = I
  · have hβk : β ∈ Jk k := hJI.symm ▸ Finset.mem_univ β
    simp only [Jk, Finset.mem_filter] at hβk
    exact (hβk.2.trans_le (hTmono hk)).le
  · exfalso
    apply hnonzero
    have hJssub : Jk k ⊂ I :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, hJI⟩
    apply hvanish ⟨Jk k, hJssub⟩
    apply hnext (T k) ⟨Jk k, hJssub⟩ x
    · intro β hβ
      simp only [Jk, Finset.mem_filter] at hβ
      exact ⟨hx β, hβ.2.le⟩
    · intro β hβI hβJ
      have hβ' : β ∉ Jk (k + 1) := fun h => hβJ (hsub h)
      simp only [Jk, Finset.mem_filter, not_and, not_lt] at hβ'
      rw [← hTsucc k]
      exact hβ' hβI
    · exact hf

/-- A chosen bound for dominant lattice parameters of a nonzero coefficient. -/
def coefficientPairingBound
    (hM : IsCartanLatticeModel levi unipotent cartanSet e pair F₀)
    (htop : levi Finset.univ = ⊤)
    (ρ : Representation R G V) (K : OpenSubgroup G) (L : V →ₗ[R] W)
    (hL : ∀ k ∈ K, ∀ w : V, L (ρ k w) = L w) (v : V)
    (hv : ∀ J : Finset Δ, J ≠ Finset.univ → v ∈ Jacquet.relations ρ (unipotent J)) : ℤ :=
  (hM.exists_coefficient_pairing_bound htop ρ K L hL v hv).choose

/-- The chosen coefficient bound controls every simple-root pairing. -/
theorem coefficientPairingBound_spec
    (hM : IsCartanLatticeModel levi unipotent cartanSet e pair F₀)
    (htop : levi Finset.univ = ⊤)
    (ρ : Representation R G V) (K : OpenSubgroup G) (L : V →ₗ[R] W)
    (hL : ∀ k ∈ K, ∀ w : V, L (ρ k w) = L w) (v : V)
    (hv : ∀ J : Finset Δ, J ≠ Finset.univ → v ∈ Jacquet.relations ρ (unipotent J))
    (x : X) (hx : ∀ β, 0 ≤ pair β x) (f : G) (hf : f ∈ F₀)
    (h : L (ρ (e (.ofAdd x) * f) v) ≠ 0) (β : Δ) :
    pair β x ≤ hM.coefficientPairingBound htop ρ K L hL v hv :=
  (hM.exists_coefficient_pairing_bound htop ρ K L hL v hv).choose_spec x hx f hf h β

end IsCartanLatticeModel

end Langlands.Aubert.General
