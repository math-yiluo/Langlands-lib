import Langlands.Cohomology.H2RelativeNormalFormStatement

noncomputable section

open CategoryTheory Rep groupCohomology

namespace Langlands.Cohomology

universe u
variable {k G : Type u} [CommRing k] [Group G]

set_option backward.isDefEq.respectTransparency false

/-- Vanishing of first cohomology makes each one-cocycle principal. -/
lemma h1_cocycle_principal (A : Rep.{u} k G)
    (hA : Subsingleton (groupCohomology A 1)) (z : cocycles₁ A) :
    ∃ a : A, ∀ g : G, z g = A.ρ g a - a := by
  have hz : H1π A z = 0 := hA.elim _ _
  obtain ⟨a, ha⟩ := (H1π_eq_zero_iff z).mp hz
  exact ⟨a, fun g => (congr_fun ha g).symm⟩

/-- The restriction of a primitive of an inflated two-cocycle becomes a
one-cocycle after subtracting its value at the identity. -/
lemma h2_primitive_restriction (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (c : cocycles₂ (A.quotientToInvariants S)) (b : G → A)
    (hb : ∀ g h : G, A.ρ g (b h) - b (g * h) + b g =
      (c ((QuotientGroup.mk' S) g, (QuotientGroup.mk' S) h) : A)) :
    (fun s : S => b s - b 1) ∈ cocycles₁ (Rep.res S.subtype A) := by
  have hb1 : b 1 = (c (1, 1) : A) := by simpa using hb 1 1
  rw [mem_cocycles₁_iff]
  intro s t
  have hst := hb s t
  have hinv : A.ρ s (b 1) = b 1 := by
    rw [hb1]
    exact (c (1, 1)).property s
  have hs : (QuotientGroup.mk' S) s = 1 := (QuotientGroup.eq_one_iff s.1).mpr s.property
  have ht : (QuotientGroup.mk' S) t = 1 := (QuotientGroup.eq_one_iff t.1).mpr t.property
  simp only [hs, ht, ← hb1] at hst
  change b (s * t : S) - b 1 = _
  change b ((s : G) * (t : G)) - b 1 = A.ρ s (b t - b 1) + (b s - b 1)
  rw [map_sub, hinv]
  rw [← hst]
  abel

/-- A cochain whose differential is inflated can be adjusted so that its
restriction is constant. -/
lemma h2_adjust_primitive (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (hS : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (c : cocycles₂ (A.quotientToInvariants S)) (b : G → A)
    (hb : ∀ g h : G, A.ρ g (b h) - b (g * h) + b g =
      (c ((QuotientGroup.mk' S) g, (QuotientGroup.mk' S) h) : A)) :
    ∃ b' : G → A,
      (∀ s : S, b' s = (c (1, 1) : A)) ∧
      (∀ g h : G, A.ρ g (b' h) - b' (g * h) + b' g =
        (c ((QuotientGroup.mk' S) g, (QuotientGroup.mk' S) h) : A)) := by
  obtain ⟨a, ha⟩ := h1_cocycle_principal (Rep.res S.subtype A) hS
    ⟨_, h2_primitive_restriction A S c b hb⟩
  have hb1 : b 1 = (c (1, 1) : A) := by simpa using hb 1 1
  refine ⟨fun g => b g - (A.ρ g a - a), ?_, ?_⟩
  · intro s
    have hs : b s - b 1 = A.ρ s a - a := ha s
    dsimp only
    rw [← hs, ← hb1]
    abel
  · intro g h
    dsimp
    rw [map_sub, map_sub, map_mul, Module.End.mul_apply]
    calc
      _ = A.ρ g (b h) - b (g * h) + b g := by abel
      _ = _ := hb g h

/-- A primitive with constant subgroup restriction takes invariant values
and is constant on quotient classes. -/
lemma h2_primitive_invariant (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (c : cocycles₂ (A.quotientToInvariants S)) (b : G → A)
    (hbS : ∀ s : S, b s = (c (1, 1) : A))
    (hb : ∀ g h : G, A.ρ g (b h) - b (g * h) + b g =
      (c ((QuotientGroup.mk' S) g, (QuotientGroup.mk' S) h) : A)) :
    (∀ (g : G) (s : S), b (g * s) = b g) ∧
    (∀ (g : G) (s : S), A.ρ s (b g) = b g) := by
  have hr : ∀ (g : G) (s : S), b (g * s) = b g := by
    intro g s
    have h := hb g s
    have hs : (QuotientGroup.mk' S) s = 1 := (QuotientGroup.eq_one_iff s.1).mpr s.property
    have hc : (c ((QuotientGroup.mk' S) g, 1) : A) = A.ρ g (c (1, 1) : A) := by
      exact congrArg Subtype.val (cocycles₂_map_one_snd c ((QuotientGroup.mk' S) g))
    rw [hs, hbS s, hc] at h
    have h' : A.ρ g (c (1, 1) : A) + b g = A.ρ g (c (1, 1) : A) + b (g * s) :=
      sub_eq_iff_eq_add.mp (by simpa only [sub_add_eq_add_sub] using h)
    exact (add_left_cancel h').symm
  refine ⟨hr, ?_⟩
  intro g s
  have h := hb s g
  have hs : (QuotientGroup.mk' S) s = 1 := (QuotientGroup.eq_one_iff s.1).mpr s.property
  rw [hs, cocycles₂_map_one_fst, hbS s] at h
  have hsg : b ((s : G) * g) = b g := by
    let t : S := ⟨g⁻¹ * s * g, Subgroup.Normal.conj_mem' ‹_› _ s.property _⟩
    simpa [t, mul_assoc] using hr g t
  rw [hsg] at h
  exact sub_eq_zero.mp (add_eq_right.mp h)

/-- A primitive of an inflated two-cocycle descends to the quotient after
subtracting a principal one-cocycle. -/
lemma h2_inflated_boundary_descends (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (hS : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (c : cocycles₂ (A.quotientToInvariants S))
    (b : G → A)
    (hb : ∀ g h : G, A.ρ g (b h) - b (g * h) + b g =
      (c ((QuotientGroup.mk' S) g, (QuotientGroup.mk' S) h) : A)) :
    ⇑c ∈ coboundaries₂ (A.quotientToInvariants S) := by
  obtain ⟨b, hbS, hb⟩ := h2_adjust_primitive A S hS c b hb
  obtain ⟨hr, hi⟩ := h2_primitive_invariant A S c b hbS hb
  let bq : G ⧸ S → A.quotientToInvariants S := fun q =>
    Quotient.liftOn' q (fun g => ⟨b g, hi g⟩) (by
      intro g h hgh
      apply Subtype.ext
      have hm : g⁻¹ * h ∈ S := QuotientGroup.leftRel_apply.mp hgh
      simpa using (hr g ⟨g⁻¹ * h, hm⟩).symm)
  refine ⟨bq, ?_⟩
  funext qr
  rcases qr with ⟨q, r⟩
  induction q using QuotientGroup.induction_on with | H g =>
  induction r using QuotientGroup.induction_on with | H h =>
  apply Subtype.ext
  exact hb g h

/-- Inflation in degree two is injective when the subgroup's first
cohomology vanishes. -/
lemma h2_inflation_injective (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (hS : Subsingleton (groupCohomology (Rep.res S.subtype A) 1)) :
    Function.Injective (HInfRes A S 2).f := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using H2_induction_on with | h c =>
  change (map (QuotientGroup.mk' S) (ofHom (A.ρ.quotientToInvariants_lift S)) 2)
    (H2π (A.quotientToInvariants S) c) = 0 at hx
  rw [H2π_comp_map_apply] at hx
  obtain ⟨b, hb⟩ := (H2π_eq_zero_iff _).mp hx
  apply (H2π_eq_zero_iff c).mpr
  apply h2_inflated_boundary_descends A S hS c b
  intro g h
  exact congr_fun hb (g, h)

/-- The exact published degree-two inflation injectivity proposition. -/
theorem h2InflationInjectivity : H2InflationInjectivity.{u} := by
  intro k _ G _ A S _ hS
  exact h2_inflation_injective A S hS

end Langlands.Cohomology
