import Langlands.Representation.RankinSelberg.TemperedLFactorStatement

/-! # Irreducible components from injective intertwiners -/

noncomputable section

namespace Langlands.RankinSelberg

universe uG uX uY

variable {G : Type uG} [Group G] {X : Type uX} {Y : Type uY}
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

/-- An irreducible representation that embeds in `ξ` is a component of `ξ`: the
image of the embedding is the subrepresentation, and the inverse of the
embedding onto its image is the surjection. -/
theorem isIrreducibleComponent_of_injective {ξ : Representation ℂ G X}
    {π : Representation ℂ G Y} (hπ : Representation.IsIrreducible π)
    (j : π.IntertwiningMap ξ) (hj : Function.Injective j) :
    IsIrreducibleComponent ξ π := by
  let e := LinearEquiv.ofInjective j.toLinearMap hj
  have he : ∀ x : j.range.toSubmodule, j (e.symm x) = (x : X) := fun x =>
    LinearEquiv.ofInjective_symm_apply (f := j.toLinearMap) (h := hj) x
  refine ⟨hπ, j.range, ⟨e.symm.toLinearMap, fun g => ?_⟩, e.symm.surjective⟩
  apply LinearMap.ext
  intro u
  apply hj
  refine (he _).trans ?_
  refine Eq.trans ?_ (Representation.IntertwiningMap.isIntertwining _ _ j g (e.symm u)).symm
  refine Eq.trans ?_ (congrArg (ξ g) (he u)).symm
  rfl


end Langlands.RankinSelberg
