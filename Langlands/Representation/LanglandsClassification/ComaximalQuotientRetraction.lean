import Langlands.Representation.LanglandsClassification.SimpleBlockQuotient
import Langlands.Representation.Intertwining.ComaximalRestriction

/-! # Retractions in quotients from comaximal central kernels

If a subrepresentation is an irreducible `τ` and the central kernels on `τ`
and the complementary quotient are comaximal, every nonzero copy of `τ` in
an equivariant quotient admits a retraction.
-/

noncomputable section

namespace Langlands.Classification

universe uG uB uV uW uX

variable {G : Type uG} [Group G] {B : Type uB} [Monoid B]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]
  {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
  {χ : Representation ℂ G X}

/-- Comaximality separates the retained simple subrepresentation even after
an equivariant quotient. All carrier universes are independent. -/
theorem quotient_retraction_of_comaximal
    (hτ : τ.IsIrreducible) (S : Subrepresentation ρ)
    (e : S.toRepresentation.Equiv τ)
    (a : B →* G) (ha : ∀ b g, a b * g = g * a b)
    (h : groupAlgebraKernel τ a ⊔
      groupAlgebraKernel (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) a = ⊤)
    (q : ρ.IntertwiningMap χ) (hq : Function.Surjective q)
    (j : τ.IntertwiningMap χ) (hj : j ≠ 0) :
    ∃ r : χ.IntertwiningMap τ, r.comp j = Representation.IntertwiningMap.id τ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp
    ((Ideal.eq_top_iff_one _).mp h)
  have hx0 := (mem_groupAlgebraKernel_iff _ _ _).mp hx
  have hy1 : Representation.asAlgebraHom (τ.comp a) y = 1 := by
    have hsum := congrArg (Representation.asAlgebraHom (τ.comp a)) hxy
    simpa [hx0] using hsum
  let c : ρ.IntertwiningMap S.toRepresentation :=
    { toLinearMap := (Intertwining.centralAction (ρ := ρ) a ha y).toLinearMap.codRestrict
        S.toSubmodule (Intertwining.algebraAction_mem_of_quotientKernel S a y hy)
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact congrArg (fun t : V →ₗ[ℂ] V => t v)
          ((Intertwining.centralAction (ρ := ρ) a ha y).isIntertwining' g) }
  let s := (Intertwining.subtypeIntertwiner S).comp e.symm.toIntertwiningMap
  let p := e.toIntertwiningMap.comp c
  apply simpleBlockQuotient_retraction hτ q hq s p
    (Intertwining.centralAction a ha y) ?_ j hj ?_
  · intro v
    have hsp : s (p v) = Representation.asAlgebraHom (ρ.comp a) y v := by
      change ((e.symm (e (c v)) : S) : V) = _
      rw [e.symm_apply_apply]
      rfl
    rw [hsp]
    exact (Intertwining.algebraAction_natural q a y v).symm
  · intro w
    change Representation.asAlgebraHom (χ.comp a) y (j w) = j w
    rw [← Intertwining.algebraAction_natural, hy1]
    rfl

/-- Choose an actual retraction using comaximal central kernels. -/
def quotientRetractionOfComaximal
    (hτ : τ.IsIrreducible) (S : Subrepresentation ρ)
    (e : S.toRepresentation.Equiv τ)
    (a : B →* G) (ha : ∀ b g, a b * g = g * a b)
    (h : groupAlgebraKernel τ a ⊔
      groupAlgebraKernel (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) a = ⊤)
    (q : ρ.IntertwiningMap χ) (hq : Function.Surjective q)
    (j : τ.IntertwiningMap χ) (hj : j ≠ 0) :
    χ.IntertwiningMap τ :=
  (quotient_retraction_of_comaximal hτ S e a ha h q hq j hj).choose

/-- The chosen retraction is a left inverse of the specified nonzero map. -/
theorem quotientRetractionOfComaximal_comp
    (hτ : τ.IsIrreducible) (S : Subrepresentation ρ)
    (e : S.toRepresentation.Equiv τ)
    (a : B →* G) (ha : ∀ b g, a b * g = g * a b)
    (h : groupAlgebraKernel τ a ⊔
      groupAlgebraKernel (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) a = ⊤)
    (q : ρ.IntertwiningMap χ) (hq : Function.Surjective q)
    (j : τ.IntertwiningMap χ) (hj : j ≠ 0) :
    (quotientRetractionOfComaximal hτ S e a ha h q hq j hj).comp j =
      Representation.IntertwiningMap.id τ :=
  (quotient_retraction_of_comaximal hτ S e a ha h q hq j hj).choose_spec

end Langlands.Classification
