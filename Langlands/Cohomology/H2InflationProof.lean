import Langlands.Cohomology.H2InflationStatement
import Langlands.Cohomology.H2InflationInjectivityProof
import Langlands.Cohomology.H2QuotientCocycle
import Langlands.Cohomology.H2RelativeNormalForm

noncomputable section

open CategoryTheory Rep groupCohomology

namespace Langlands.Cohomology

universe u
variable {k G : Type u} [CommRing k] [Group G]

set_option backward.isDefEq.respectTransparency false

/-- The cocycle normal form gives exactness of inflation and restriction. -/
lemma h2_inflation_exact_of_normalForm (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (hnorm : ∀ c : cocycles₂ A,
      (∃ a : S → A, ∀ s t : S,
        c (s.1, t.1) = (d₁₂ (Rep.res S.subtype A) a) (s, t)) →
      ∃ b : G → A, ∀ (s : S) (g : G),
        c (s.1, g) = (d₁₂ A b) (s.1, g) ∧
        c (g, s.1) = (d₁₂ A b) (g, s.1)) :
    LinearMap.range (HInfRes A S 2).f.hom =
      LinearMap.ker (HInfRes A S 2).g.hom := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    change (HInfRes A S 2).g ((HInfRes A S 2).f y) = 0
    exact congrArg (fun f : (HInfRes A S 2).X₁ ⟶ (HInfRes A S 2).X₃ => f y)
      (HInfRes A S 2).zero
  · intro x hx
    change (HInfRes A S 2).g x = 0 at hx
    induction x using H2_induction_on with | h c =>
    change (map S.subtype (𝟙 _) 2) (H2π A c) = 0 at hx
    rw [H2π_comp_map_apply] at hx
    obtain ⟨a, ha⟩ := (H2π_eq_zero_iff _).mp hx
    obtain ⟨b, hb⟩ := hnorm c ⟨a, fun s t => (congr_fun ha (s, t)).symm⟩
    let c' : cocycles₂ A := c - ⟨d₁₂ A b, d₁₂_apply_mem_cocycles₂ b⟩
    have hc' : ∀ (s : S) (g : G), c' (s.1, g) = 0 ∧ c' (g, s.1) = 0 := by
      intro s g
      exact ⟨sub_eq_zero.mpr (hb s g).1, sub_eq_zero.mpr (hb s g).2⟩
    refine ⟨H2π _ (descendRelativeCocycle A S c' hc'), ?_⟩
    change (map (QuotientGroup.mk' S) (ofHom (A.ρ.quotientToInvariants_lift S)) 2)
      (H2π _ (descendRelativeCocycle A S c' hc')) = H2π A c
    rw [H2π_comp_map_apply, inflate_descendRelativeCocycle]
    apply (H2π_eq_iff c' c).mpr
    refine ⟨-b, ?_⟩
    ext gh
    change (d₁₂ A (-b)) gh = (c gh - (d₁₂ A b) gh) - c gh
    rw [map_neg]
    change -(d₁₂ A b) gh = _
    abel

/-- Assembly of the parent target from the relative normal-form proposition. -/
theorem h2InflationRestrictionExactness_of_normalForm
    (hnorm : H2RelativeCocycleNormalForm.{u}) : H2InflationRestrictionExactness.{u} := by
  intro k _ G _ A S _ hS
  exact ⟨h2InflationInjectivity k G A S hS,
    h2_inflation_exact_of_normalForm A S (hnorm k G A S hS)⟩

/-- Degree-two inflation is injective and its range is the kernel of restriction
when the normal subgroup's first cohomology vanishes. -/
theorem h2InflationRestrictionExactness : H2InflationRestrictionExactness.{u} :=
  h2InflationRestrictionExactness_of_normalForm h2RelativeCocycleNormalForm

end Langlands.Cohomology
