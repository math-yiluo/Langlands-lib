import Langlands.Representation.Whittaker.SubquotientCoefficientModelInclusionStatement

/-!
# Coefficient-model inclusion for actual smooth subquotients

Pull back the functional through the quotient map and extend it along the
inclusion of the invariant subspace. Surjectivity of the quotient map then
identifies each coefficient function with an ambient coefficient.
-/

noncomputable section

namespace Langlands.Whittaker

universe uG uV uW

/-- An actual smooth subquotient has an ambient coefficient model containing
the model of each specified equivariant functional. -/
theorem subquotientCoefficientModelInclusion :
    SubquotientCoefficientModelInclusionStatement.{uG, uV, uW} := by
  intro G _ _ _ N hN θ hθ V _ _ W _ _ ρ σ hρ U q hq ℓ
  let i : U.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := U.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  obtain ⟨L, hL⟩ := functionalsComap_surjective_of_smooth N hN θ hθ i
    Subtype.val_injective hρ (functionalsComap (N := N) (θ := θ) q ℓ)
  have hext (v : U.toSubmodule) : L.val v.val = ℓ.val (q v) :=
    congrArg (fun f : functionals N θ U.toRepresentation => f.val v) hL
  refine ⟨L, hext, ?_, ?_⟩
  · intro hℓ hzero
    apply hℓ
    ext w
    obtain ⟨v, rfl⟩ := hq w
    rw [← hext, hzero]
    rfl
  · rintro f ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := hq w
    refine ⟨v.val, ?_⟩
    apply Subtype.ext
    funext g
    change L.val (ρ g v.val) = ℓ.val (σ g (q v))
    rw [← q.isIntertwining]
    exact hext (U.toRepresentation g v)

end Langlands.Whittaker
