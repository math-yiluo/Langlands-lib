import Langlands.Cohomology.H2RelativeNormalFormStatement
import Mathlib.Tactic.Abel

noncomputable section

open CategoryTheory Rep groupCohomology

namespace Langlands.Cohomology

universe u
variable {k G : Type u} [CommRing k] [Group G]

set_option backward.isDefEq.respectTransparency false

private lemma quotient_coordinates (S : Subgroup G) [S.Normal] :
    ∃ (r : G ⧸ S → G) (t : G → S),
      (∀ q, QuotientGroup.mk' S (r q) = q) ∧
      (∀ g, (t g : G) * r (QuotientGroup.mk' S g) = g) ∧
      (∀ (s : S) g, t (s * g) = s * t g) := by
  classical
  let π := QuotientGroup.mk' S
  let r : G ⧸ S → G := Quotient.out
  have hr : ∀ q, π (r q) = q := fun q => Quotient.out_eq' q
  have ht : ∀ g, g * (r (π g))⁻¹ ∈ S := by
    intro g
    apply (QuotientGroup.eq_one_iff _).mp
    change π (g * (r (π g))⁻¹) = 1
    simp only [map_mul, map_inv, hr, mul_inv_cancel]
  let t : G → S := fun g => ⟨g * (r (π g))⁻¹, ht g⟩
  refine ⟨r, t, hr, ?_, ?_⟩
  · intro g
    change (g * (r (π g))⁻¹) * r (π g) = g
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  · intro s g
    apply Subtype.ext
    have hs : π s = 1 := (QuotientGroup.eq_one_iff _).mpr s.property
    simp [t, map_mul, hs, mul_assoc]

private lemma kill_left (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (c : cocycles₂ A) (hc : ∀ s t : S, c (s, t) = 0) :
    ∃ b : G → A, ∀ (s : S) g, c (s, g) = d₁₂ A b (s, g) := by
  classical
  obtain ⟨r, t, hr, ht, hst⟩ := quotient_coordinates S
  let π := QuotientGroup.mk' S
  let b : G → A := fun g => -c (t g, r (π g))
  have hπ : ∀ s : S, π s = 1 := fun s => (QuotientGroup.eq_one_iff _).mpr s.property
  have hr1 : r 1 ∈ S := (QuotientGroup.eq_one_iff _).mp (hr 1)
  have hb : ∀ s : S, b s = 0 := by
    intro s
    dsimp [b]
    rw [hπ s]
    exact neg_eq_zero.mpr (hc (t s) ⟨r 1, hr1⟩)
  refine ⟨b, ?_⟩
  intro s g
  have he := (mem_cocycles₂_iff c).mp c.property (s : G) (t g) (r (π g))
  rw [hc s (t g), ht g, add_zero] at he
  change c (s, g) = A.ρ s (b g) - b (s * g) + b s
  rw [hb, add_zero]
  dsimp [b]
  rw [hst]
  have hπsg : π (s * g) = π g := by rw [map_mul, hπ, one_mul]
  rw [hπsg, map_neg]
  change c (s, g) = -A.ρ s (c (t g, r (π g))) - -c (s * t g, r (π g))
  rw [he]
  abel

private lemma left_zero_equivariance (A : Rep.{u} k G) (S : Subgroup G)
    (c : cocycles₂ A) (hc : ∀ (s : S) g, c (s, g) = 0)
    (s : S) (g h : G) : c (s * g, h) = A.ρ s (c (g, h)) := by
  have he := (mem_cocycles₂_iff c).mp c.property (s : G) g h
  simpa only [hc s g, hc s (g * h), add_zero] using he

private lemma conjugate_primitive (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (hA : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (c : cocycles₂ A) (hc : ∀ (s : S) g, c (s, g) = 0) (g : G) :
    ∃ x : A, ∀ s : S, c (g, g⁻¹ * s * g) = A.ρ s x - x := by
  let z : cocycles₁ (Rep.res S.subtype A) := ⟨fun s => c (g, g⁻¹ * s * g), by
    apply (mem_cocycles₁_iff _).mpr
    intro s t
    let a : S := ⟨g⁻¹ * s * g, Subgroup.Normal.conj_mem' ‹_› _ s.property _⟩
    let b : S := ⟨g⁻¹ * t * g, Subgroup.Normal.conj_mem' ‹_› _ t.property _⟩
    have hga : g * (a : G) = (s : G) * g := by dsimp [a]; group
    have hab : (a : G) * b = g⁻¹ * (s * t : S) * g := by dsimp [a, b]; group
    have he := (mem_cocycles₂_iff c).mp c.property g a b
    rw [hc a b, map_zero, zero_add, hga, hab,
      left_zero_equivariance A S c hc s g b] at he
    exact he.symm⟩
  have hz : H1π (Rep.res S.subtype A) z = 0 := hA.elim _ _
  obtain ⟨x, hx⟩ := (H1π_eq_zero_iff z).mp hz
  refine ⟨x, fun s => ?_⟩
  exact (congr_fun hx s).symm

private lemma kill_right (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (hA : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (c : cocycles₂ A) (hc : ∀ (s : S) g, c (s, g) = 0) :
    ∃ b : G → A, ∀ (s : S) g,
      d₁₂ A b (s, g) = 0 ∧ c (g, s) = d₁₂ A b (g, s) := by
  classical
  obtain ⟨r, t, hr, ht, hst⟩ := quotient_coordinates S
  let π := QuotientGroup.mk' S
  have hπ : ∀ s : S, π s = 1 := fun s => (QuotientGroup.eq_one_iff _).mpr s.property
  have hr1 : r 1 ∈ S := (QuotientGroup.eq_one_iff _).mp (hr 1)
  choose x hx using fun q => conjugate_primitive A S hA c hc (r q)
  have hx1 : ∀ s : S, A.ρ s (x 1) = x 1 := by
    intro s
    have he := hx 1 s
    rw [hc ⟨r 1, hr1⟩] at he
    exact sub_eq_zero.mp he.symm
  let b : G → A := fun g => -A.ρ (t g) (x (π g)) + x 1
  have hb : ∀ s : S, b s = 0 := by
    intro s
    dsimp [b]
    rw [hπ, hx1]
    abel
  have hbe : ∀ (s : S) g, b (s * g) = A.ρ s (b g) := by
    intro s g
    have hπsg : π (s * g) = π g := by rw [map_mul, hπ, one_mul]
    dsimp [b]
    rw [hst, hπsg]
    simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_add, map_neg, hx1]
  refine ⟨b, ?_⟩
  intro s g
  constructor
  · change A.ρ s (b g) - b (s * g) + b s = 0
    rw [hbe, hb, sub_self, add_zero]
  · let v : S := ⟨r (π g) * s * (r (π g))⁻¹,
        Subgroup.Normal.conj_mem ‹_› _ s.property _⟩
    have hgs : g * (s : G) = (t g : G) * v * r (π g) := by
      conv_lhs => rw [← ht g]
      dsimp [v]
      group
      rfl
    have hπgs : π (g * s) = π g := by rw [map_mul, hπ, mul_one]
    have htgs : t (g * s) = t g * v := by
      apply Subtype.ext
      apply mul_right_cancel (b := r (π g))
      rw [Subgroup.coe_mul, ← hgs, ← hπgs, ht]
    have hconj : (r (π g))⁻¹ * (v : G) * r (π g) = s := by dsimp [v]; group
    have he := hx (π g) v
    rw [hconj] at he
    have hcg : c (g, s) = A.ρ (t g) (c (r (π g), s)) := by
      conv_lhs => rw [← ht g]
      exact left_zero_equivariance A S c hc (t g) (r (π g)) s
    change c (g, s) = A.ρ g (b s) - b (g * s) + b g
    rw [hb, map_zero, zero_sub, hcg, he]
    dsimp [b]
    rw [htgs, hπgs]
    simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub]
    abel

/-- Every restricted-trivial two-cocycle admits one boundary matching both
mixed subgroup restrictions when subgroup first cohomology vanishes. -/
theorem h2RelativeCocycleNormalForm : H2RelativeCocycleNormalForm.{u} := by
  intro k _ G _ A S _ hA c hc
  classical
  obtain ⟨a, ha⟩ := hc
  let e : G → A := fun g => if hg : g ∈ S then a ⟨g, hg⟩ else 0
  have he : ∀ s : S, e s = a s := by intro s; simp [e, s.property]
  let c₀ : cocycles₂ A := c - ⟨d₁₂ A e, d₁₂_apply_mem_cocycles₂ e⟩
  have hc₀ : ∀ s t : S, c₀ (s, t) = 0 := by
    intro s t
    change c (s, t) - d₁₂ A e (s, t) = 0
    apply sub_eq_zero.mpr
    rw [ha]
    change A.ρ s (a t) - a (s * t) + a s = A.ρ s (e t) - e (s * t : S) + e s
    rw [he, he, he]
  obtain ⟨b, hb⟩ := kill_left A S c₀ hc₀
  let c₁ : cocycles₂ A := c₀ - ⟨d₁₂ A b, d₁₂_apply_mem_cocycles₂ b⟩
  have hc₁ : ∀ (s : S) g, c₁ (s, g) = 0 := by
    intro s g
    change c₀ (s, g) - d₁₂ A b (s, g) = 0
    exact sub_eq_zero.mpr (hb s g)
  obtain ⟨d, hd⟩ := kill_right A S hA c₁ hc₁
  refine ⟨e + b + d, ?_⟩
  intro s g
  have hadd : ∀ p : G × G,
      d₁₂ A (e + b + d) p = d₁₂ A e p + d₁₂ A b p + d₁₂ A d p := by
    intro p
    simp only [map_add, Pi.add_apply]
  constructor
  · have hl := hb s g
    change c (s, g) - d₁₂ A e (s, g) = d₁₂ A b (s, g) at hl
    rw [hadd, (hd s g).1, add_zero]
    exact (sub_eq_iff_eq_add.mp hl).trans (add_comm _ _)
  · have hr := (hd s g).2
    change c (g, s) - d₁₂ A e (g, s) - d₁₂ A b (g, s) = d₁₂ A d (g, s) at hr
    rw [hadd]
    have hh := sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp hr)
    rw [hh]
    abel

end Langlands.Cohomology
