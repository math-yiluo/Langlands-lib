import Langlands.ClassFieldTheory.Local.RelativeH1Statement

namespace Langlands.ClassFieldTheory.Local

universe u v

open groupCohomology

theorem finiteRelativeH1Vanishing : FiniteRelativeH1Vanishing.{u,v} := by
  intro K L _ _ _ _
  have hz : ∀ a : relativeCohomology K L 1, a = 0 := by
    intro a
    refine H1_induction_on a fun x => (H1π_eq_zero_iff x).2 ?_
    let f : Gal(L/K) → Lˣ := fun g => Additive.toMul (show Additive Lˣ from x g)
    have hc : IsMulCocycle₁ f := by
      intro g h
      exact congrArg (Additive.toMul : Additive Lˣ → Lˣ)
        ((mem_cocycles₁_iff x).1 x.2 g h)
    obtain ⟨β, hβ⟩ :=
      isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hc
    refine ⟨Additive.ofMul β, ?_⟩
    funext g
    exact hβ g
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end Langlands.ClassFieldTheory.Local
