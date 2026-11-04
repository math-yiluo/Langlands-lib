import Langlands.Group.TitsSystemBruhat

/-!
# Parabolic double cosets across components

Internal algebraic transport from a Tits system in a subgroup and a full-group
Borel double-coset equivalence. No building realization is asserted.
-/

noncomputable section

namespace Langlands.Group.TitsSystem

universe u v

variable {G : Type u} [Group G] {W : Type v} [Group W]
  {B N K : Subgroup G} {W₀ : Subgroup W} {π : N →* W}
  {π₀ : N.subgroupOf K →* W₀} {S : Set W₀}
  (eB : W ≃ DoubleCoset.Quotient (B : Set G) B)
  (heB : ∀ n : N, eB (π n) = DoubleCoset.mk B B (n : G))

include eB heB

/-- The full-group Bruhat equivalence identifies the index of every cell. -/
theorem equiv_eq_doubleCoset_of_mem_cell {w : W} {g : G}
    (hg : g ∈ cell B π w) :
    eB w = DoubleCoset.mk B B g := by
  obtain ⟨n, hn, b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  rw [← hn, heB]
  exact DoubleCoset.eq.2 ⟨b₁, hb₁, b₂, hb₂, rfl⟩

/-- Full-group cell uniqueness follows from the given Bruhat equivalence. -/
theorem index_eq_of_mem_cell {v w : W} {g : G}
    (hv : g ∈ cell B π v) (hw : g ∈ cell B π w) : v = w :=
  eB.injective ((equiv_eq_doubleCoset_of_mem_cell eB heB hv).trans
    (equiv_eq_doubleCoset_of_mem_cell eB heB hw).symm)

variable (hB : B ≤ K)
  (hπ₀ : ∀ n : N.subgroupOf K,
    (π₀ n : W) = π ⟨((n : K) : G), n.property⟩)
  (h : IsTitsSystem (B.subgroupOf K) (N.subgroupOf K) π₀ S)

include hπ₀

omit eB heB in
/-- A cell in the subgroup is contained in the full-group cell of the same index. -/
theorem coe_mem_cell_of_mem_subgroup_cell {w : W₀} {g : K}
    (hg : g ∈ cell (B.subgroupOf K) π₀ w) :
    (g : G) ∈ cell B π (w : W) := by
  obtain ⟨n, hn, b₁, hb₁, b₂, hb₂, heq⟩ := hg
  exact ⟨⟨((n : K) : G), n.property⟩,
    (hπ₀ n).symm.trans (congrArg Subtype.val hn),
    b₁, hb₁, b₂, hb₂, congrArg Subtype.val heq⟩

include hB h

/-- Every full cell with an index in `W₀` comes from the subgroup cell. -/
theorem exists_subgroup_cell_of_mem_cell {w : W₀} {g : G}
    (hg : g ∈ cell B π (w : W)) :
    ∃ g₀ : K, (g₀ : G) = g ∧ g₀ ∈ cell (B.subgroupOf K) π₀ w := by
  obtain ⟨n, hn⟩ := h.surjective w
  let m : N := ⟨((n : K) : G), n.property⟩
  have hm : π m = (w : W) :=
    (hπ₀ n).symm.trans (congrArg Subtype.val hn)
  have hcos : DoubleCoset.mk B B (m : G) = DoubleCoset.mk B B g := by
    rw [← heB, hm]
    exact equiv_eq_doubleCoset_of_mem_cell eB heB hg
  obtain ⟨b₁, hb₁, b₂, hb₂, heq⟩ := DoubleCoset.eq.1 hcos
  let a : K := ⟨b₁, hB hb₁⟩
  let b : K := ⟨b₂, hB hb₂⟩
  refine ⟨a * (n : K) * b, heq.symm, ?_⟩
  exact ⟨n, hn, a, hb₁, b, hb₂, rfl⟩

omit eB heB hB hπ₀ h in
/-- Right multiplication by a representative normalizing `B` transports full cells. -/
theorem mul_normalizing_rep_mem_cell {w : W} {g : G}
    (hg : g ∈ cell B π w) (r : N)
    (hrB : (r : G) ∈ Subgroup.normalizer (B : Set G)) :
    g * (r : G) ∈ cell B π (w * π r) := by
  obtain ⟨n, hn, b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  have hb₂' : (r : G)⁻¹ * b₂ * (r : G) ∈ B := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.1
        ((Subgroup.normalizer (B : Set G)).inv_mem hrB) b₂).1 hb₂
  refine ⟨n * r, by simp [hn], b₁, hb₁, (r : G)⁻¹ * b₂ * (r : G), hb₂', ?_⟩
  simp [mul_assoc]

variable
  (hreps : ∀ g : G, ∃ r : N,
    g * (r : G)⁻¹ ∈ K ∧ (r : G) ∈ Subgroup.normalizer (B : Set G))

include hreps

/-- A parabolic cell in the subgroup acts on every full-group cell on the left. -/
theorem exists_subgroup_mul_mem_cell {X : Set W₀} (hX : X ⊆ S)
    {u : W₀} (hu : u ∈ Subgroup.closure X)
    {x : G} (hx : x ∈ cell B π (u : W))
    {v : W} {y : G} (hy : y ∈ cell B π v) :
    ∃ u' ∈ Subgroup.closure X, x * y ∈ cell B π ((u' : W) * v) := by
  obtain ⟨x₀, rfl, hx₀⟩ :=
    exists_subgroup_cell_of_mem_cell eB heB hB hπ₀ h hx
  obtain ⟨r, hyr, hrB⟩ := hreps y
  let y₀ : K := ⟨y * (r : G)⁻¹, hyr⟩
  obtain ⟨v₀, hy₀⟩ := h.exists_mem_cell y₀
  have hy' := mul_normalizing_rep_mem_cell
    (coe_mem_cell_of_mem_subgroup_cell hπ₀ hy₀) r hrB
  have hv : (v₀ : W) * π r = v := by
    apply index_eq_of_mem_cell eB heB _ hy
    simpa [y₀, mul_assoc] using hy'
  obtain ⟨u', hu', hc⟩ := h.exists_mul_mem_cell hX hu hx₀ hy₀
  refine ⟨u', hu', ?_⟩
  have hc' := mul_normalizing_rep_mem_cell
    (coe_mem_cell_of_mem_subgroup_cell hπ₀ hc) r hrB
  simpa [y₀, mul_assoc, hv] using hc'

/-- The corresponding right action, obtained by inversion. -/
theorem exists_subgroup_mul_mem_cell_right {Y : Set W₀} (hY : Y ⊆ S)
    {u : W₀} (hu : u ∈ Subgroup.closure Y)
    {y : G} (hy : y ∈ cell B π (u : W))
    {v : W} {x : G} (hx : x ∈ cell B π v) :
    ∃ u' ∈ Subgroup.closure Y, x * y ∈ cell B π (v * (u' : W)) := by
  obtain ⟨u', hu', hc⟩ :=
    exists_subgroup_mul_mem_cell eB heB hB hπ₀ h hreps hY
      (Subgroup.inv_mem _ hu) (by simpa using inv_mem_cell hy) (inv_mem_cell hx)
  refine ⟨u'⁻¹, Subgroup.inv_mem _ hu', ?_⟩
  rw [← mul_inv_rev] at hc
  simpa using inv_mem_cell hc

omit hreps in
/-- A standard parabolic comparison in the subgroup identifies its full-group
carrier with the union of the corresponding full cells. -/
theorem coe_eq_standardParabolic_of_subgroup {X : Set W₀} {P : Subgroup G}
    (hPK : P ≤ K)
    (hP : (P.subgroupOf K : Set K) = standardParabolic (B.subgroupOf K) π₀ X) :
    (P : Set G) = standardParabolic B π (W₀.subtype '' X) := by
  ext g
  constructor
  · intro hg
    have hg₀ : (⟨g, hPK hg⟩ : K) ∈ standardParabolic (B.subgroupOf K) π₀ X := by
      rw [← hP]
      exact hg
    obtain ⟨w, hw, hc⟩ := hg₀
    refine ⟨(w : W), ?_, coe_mem_cell_of_mem_subgroup_cell hπ₀ hc⟩
    rw [← MonoidHom.map_closure]
    exact Subgroup.mem_map_of_mem W₀.subtype hw
  · rintro ⟨w, hw, hc⟩
    rw [← MonoidHom.map_closure] at hw
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    obtain ⟨g₀, rfl, hg₀⟩ :=
      exists_subgroup_cell_of_mem_cell eB heB hB hπ₀ h hc
    have hgP : g₀ ∈ P.subgroupOf K := by
      rw [← SetLike.mem_coe, hP]
      exact ⟨w₀, hw₀, hg₀⟩
    exact hgP

/-- Full-component parabolic double cosets. The Tits system is only required
inside `K`; all normalizer representatives retain their prescribed values. -/
theorem exists_subgroup_parabolic_doubleCoset_equiv (hπ : Function.Surjective π)
    {X Y : Set W₀} (hX : X ⊆ S) (hY : Y ⊆ S) {V V' : Subgroup W}
    (hV : V = (Subgroup.closure X).map W₀.subtype)
    (hV' : V' = (Subgroup.closure Y).map W₀.subtype) {P Q : Subgroup G}
    (hP : (P : Set G) = standardParabolic B π (W₀.subtype '' X))
    (hQ : (Q : Set G) = standardParabolic B π (W₀.subtype '' Y)) :
    ∃ e : DoubleCoset.Quotient (V : Set W) V' ≃
        DoubleCoset.Quotient (P : Set G) Q,
      ∀ n : N, e (DoubleCoset.mk V V' (π n)) = DoubleCoset.mk P Q (n : G) := by
  subst hV hV'
  have hle : ∀ {R : Subgroup G} {Z : Set W},
      (R : Set G) = standardParabolic B π Z → B ≤ R := by
    intro R Z hR b hb
    rw [← SetLike.mem_coe, hR]
    exact ⟨1, Subgroup.one_mem _, 1, map_one π,
      1, B.one_mem, b, hb, by simp⟩
  have hBP := hle hP
  have hBQ := hle hQ
  let rep : W → N := Function.surjInv hπ
  have hrep : ∀ w, π (rep w) = w := Function.surjInv_eq hπ
  have hmk : ∀ n : N,
      DoubleCoset.mk P Q (rep (π n) : G) = DoubleCoset.mk P Q (n : G) := by
    intro n
    have hBn : DoubleCoset.mk B B (rep (π n) : G) = DoubleCoset.mk B B (n : G) := by
      rw [← heB (rep (π n)), hrep, heB]
    obtain ⟨b₁, hb₁, b₂, hb₂, hn⟩ := DoubleCoset.eq.1 hBn
    exact DoubleCoset.eq.2 ⟨b₁, hBP hb₁, b₂, hBQ hb₂, hn⟩
  let f : DoubleCoset.Quotient ((Subgroup.closure X).map W₀.subtype : Set W)
      ((Subgroup.closure Y).map W₀.subtype : Set W) →
      DoubleCoset.Quotient (P : Set G) Q :=
    Quotient.lift (fun w => DoubleCoset.mk P Q (rep w : G)) (by
      intro a b hab
      obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.rel_iff.1 hab
      have h1 : DoubleCoset.mk P Q (rep (x * a * y) : G) =
          DoubleCoset.mk P Q ((rep x * rep a * rep y : N) : G) := by
        rw [← hmk (rep x * rep a * rep y)]
        simp [hrep]
      show DoubleCoset.mk P Q (rep a : G) =
        DoubleCoset.mk P Q (rep (x * a * y) : G)
      rw [h1, DoubleCoset.eq]
      refine ⟨rep x, rep_mem_of_coe_eq hP ?_,
        rep y, rep_mem_of_coe_eq hQ ?_, ?_⟩
      · rw [hrep, ← MonoidHom.map_closure]
        exact hx
      · rw [hrep, ← MonoidHom.map_closure]
        exact hy
      · simp)
  have hf : ∀ n : N, f (DoubleCoset.mk _ _ (π n)) = DoubleCoset.mk P Q (n : G) :=
    hmk
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, hf⟩
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
    change DoubleCoset.mk P Q (rep a : G) = DoubleCoset.mk P Q (rep b : G) at hab
    obtain ⟨p, hp, q, hq, hpq⟩ := DoubleCoset.eq.1 hab
    rw [← SetLike.mem_coe, hP] at hp
    rw [← SetLike.mem_coe, hQ] at hq
    obtain ⟨u, hu, hpu⟩ := hp
    obtain ⟨u', hu', hqu⟩ := hq
    rw [← MonoidHom.map_closure] at hu hu'
    obtain ⟨u, hu, rfl⟩ := hu
    obtain ⟨u', hu', rfl⟩ := hu'
    obtain ⟨u₁, hu₁, h₁⟩ := exists_subgroup_mul_mem_cell
      eB heB hB hπ₀ h hreps hX hu hpu (mem_cell_of_eq (hrep a))
    obtain ⟨u₂, hu₂, h₂⟩ := exists_subgroup_mul_mem_cell_right
      eB heB hB hπ₀ h hreps hY hu' hqu h₁
    rw [← hpq] at h₂
    have heq := index_eq_of_mem_cell eB heB (mem_cell_of_eq (hrep b)) h₂
    apply Quotient.sound
    exact DoubleCoset.rel_iff.2 ⟨(u₁ : W), Subgroup.mem_map_of_mem W₀.subtype hu₁,
      (u₂ : W), Subgroup.mem_map_of_mem W₀.subtype hu₂, heq⟩
  · intro z
    induction z using Quotient.inductionOn with
    | h g =>
    obtain ⟨w, hw⟩ := eB.surjective (DoubleCoset.mk B B g)
    have hg : DoubleCoset.mk B B (rep w : G) = DoubleCoset.mk B B g := by
      rw [← heB, hrep]
      exact hw
    obtain ⟨b₁, hb₁, b₂, hb₂, hg⟩ := DoubleCoset.eq.1 hg
    refine ⟨DoubleCoset.mk _ _ w, ?_⟩
    change DoubleCoset.mk P Q (rep w : G) = DoubleCoset.mk P Q g
    exact DoubleCoset.eq.2 ⟨b₁, hBP hb₁, b₂, hBQ hb₂, hg⟩

/-- A chosen full-component parabolic double-coset equivalence. -/
def subgroupParabolicDoubleCosetEquiv (hπ : Function.Surjective π)
    {X Y : Set W₀} (hX : X ⊆ S) (hY : Y ⊆ S) {V V' : Subgroup W}
    (hV : V = (Subgroup.closure X).map W₀.subtype)
    (hV' : V' = (Subgroup.closure Y).map W₀.subtype) {P Q : Subgroup G}
    (hP : (P : Set G) = standardParabolic B π (W₀.subtype '' X))
    (hQ : (Q : Set G) = standardParabolic B π (W₀.subtype '' Y)) :
    DoubleCoset.Quotient (V : Set W) V' ≃ DoubleCoset.Quotient (P : Set G) Q :=
  Classical.choose (exists_subgroup_parabolic_doubleCoset_equiv
    eB heB hB hπ₀ h hreps hπ hX hY hV hV' hP hQ)

/-- The chosen equivalence has the required value on every normalizer representative. -/
theorem subgroupParabolicDoubleCosetEquiv_apply (hπ : Function.Surjective π)
    {X Y : Set W₀} (hX : X ⊆ S) (hY : Y ⊆ S) {V V' : Subgroup W}
    (hV : V = (Subgroup.closure X).map W₀.subtype)
    (hV' : V' = (Subgroup.closure Y).map W₀.subtype) {P Q : Subgroup G}
    (hP : (P : Set G) = standardParabolic B π (W₀.subtype '' X))
    (hQ : (Q : Set G) = standardParabolic B π (W₀.subtype '' Y)) (n : N) :
    subgroupParabolicDoubleCosetEquiv eB heB hB hπ₀ h hreps hπ hX hY hV hV' hP hQ
        (DoubleCoset.mk V V' (π n)) =
      DoubleCoset.mk P Q (n : G) :=
  Classical.choose_spec (exists_subgroup_parabolic_doubleCoset_equiv
    eB heB hB hπ₀ h hreps hπ hX hY hV hV' hP hQ) n

end Langlands.Group.TitsSystem
