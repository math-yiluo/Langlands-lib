import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

noncomputable section

open CategoryTheory Rep groupCohomology

namespace Langlands.Cohomology

universe u
variable {k G : Type u} [CommRing k] [Group G]

set_option backward.isDefEq.respectTransparency false

/-- A two-cocycle vanishing on both mixed subgroup products is constant
on each quotient variable and takes subgroup-invariant values. -/
lemma relativeCocycle_properties (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (c : cocycles₂ A)
    (hc : ∀ (s : S) (g : G), c (s.1, g) = 0 ∧ c (g, s.1) = 0) :
    (∀ (g h : G) (s : S), c (g, h * s) = c (g, h)) ∧
    (∀ (g h : G) (s : S), c (g * s, h) = c (g, h)) ∧
    (∀ (g h : G) (s : S), A.ρ s (c (g, h)) = c (g, h)) := by
  have hz := (mem_cocycles₂_iff c).mp c.property
  have hr : ∀ (g h : G) (s : S), c (g, h * s) = c (g, h) := by
    intro g h s
    have he := hz g h s
    simpa only [(hc s (g * h)).2, (hc s h).2, map_zero, zero_add] using he.symm
  have hl : ∀ (g h : G) (s : S), c (g * s, h) = c (g, h) := by
    intro g h s
    have he := hz g s h
    simp only [(hc s g).2, (hc s h).1, map_zero, add_zero, zero_add] at he
    rw [he]
    let t : S := ⟨h⁻¹ * s * h, Subgroup.Normal.conj_mem' ‹_› _ s.property _⟩
    simpa [t, mul_assoc] using hr g h t
  refine ⟨hr, hl, ?_⟩
  intro g h s
  have he := hz s g h
  simp only [(hc s g).1, (hc s (g * h)).1, add_zero] at he
  rw [← he]
  let t : S := ⟨g⁻¹ * s * g, Subgroup.Normal.conj_mem' ‹_› _ s.property _⟩
  simpa [t, mul_assoc] using hl g h t

/-- Descend an adapted two-cocycle to the quotient group with its actual
representation on invariant coefficients. -/
def descendRelativeCocycle (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (c : cocycles₂ A)
    (hc : ∀ (s : S) (g : G), c (s.1, g) = 0 ∧ c (g, s.1) = 0) :
    cocycles₂ (A.quotientToInvariants S) := by
  have hr := (relativeCocycle_properties A S c hc).1
  have hl := (relativeCocycle_properties A S c hc).2.1
  have hi := (relativeCocycle_properties A S c hc).2.2
  let F : G → G ⧸ S → A.quotientToInvariants S := fun g q =>
    Quotient.liftOn' q (fun h => ⟨c (g, h), hi g h⟩) (by
      intro h j hhj
      apply Subtype.ext
      have hm : h⁻¹ * j ∈ S := QuotientGroup.leftRel_apply.mp hhj
      simpa using (hr g h ⟨h⁻¹ * j, hm⟩).symm)
  let cq : (G ⧸ S) × (G ⧸ S) → A.quotientToInvariants S := fun q =>
    Quotient.liftOn' q.1 (fun g => F g q.2) (by
      intro g h hgh
      induction q.2 using QuotientGroup.induction_on with | H j =>
      apply Subtype.ext
      have hm : g⁻¹ * h ∈ S := QuotientGroup.leftRel_apply.mp hgh
      simpa [F] using (hl g j ⟨g⁻¹ * h, hm⟩).symm)
  refine ⟨cq, (mem_cocycles₂_iff cq).mpr ?_⟩
  intro g h j
  induction g using QuotientGroup.induction_on with | H g =>
  induction h using QuotientGroup.induction_on with | H h =>
  induction j using QuotientGroup.induction_on with | H j =>
  apply Subtype.ext
  exact (mem_cocycles₂_iff c).mp c.property g h j

@[simp]
lemma descendRelativeCocycle_apply (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (c : cocycles₂ A)
    (hc : ∀ (s : S) (g : G), c (s.1, g) = 0 ∧ c (g, s.1) = 0)
    (g h : G) :
    (descendRelativeCocycle A S c hc
      ((QuotientGroup.mk' S) g, (QuotientGroup.mk' S) h) : A) = c (g, h) := rfl

/-- Inflation of the descended cocycle recovers the adapted cocycle. -/
lemma inflate_descendRelativeCocycle (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (c : cocycles₂ A)
    (hc : ∀ (s : S) (g : G), c (s.1, g) = 0 ∧ c (g, s.1) = 0) :
    mapCocycles₂ (QuotientGroup.mk' S) (ofHom (A.ρ.quotientToInvariants_lift S))
      (descendRelativeCocycle A S c hc) = c := by
  apply Subtype.ext
  rfl

end Langlands.Cohomology
