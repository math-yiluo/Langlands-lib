import Langlands.Shimura.PEL.Similitudes

/-! # Transport of form-compatible frames and their value modules -/

universe u v w z z' t t'

namespace Langlands.Shimura.PEL.FormIso

variable {R : Type u} {B : Type v} {V : Type w} {W : Type z} {W' : Type z'}
  {L : Type t} {L' : Type t'} [CommRing R] [Ring B]
  [AddCommGroup V] [Module R V] [Module B V]
  [AddCommGroup W] [Module R W] [Module B W]
  [AddCommGroup W'] [Module R W'] [Module B W']
  [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
  {ψ : V →ₗ[R] V →ₗ[R] R} {φ : W →ₗ[R] W →ₗ[R] L}
  {φ' : W' →ₗ[R] W' →ₗ[R] L'}

/-- A simultaneous transport of the target and value module restricts to an
 equivalence of compatible frames. The value trivialization remains existential. -/
def transport (e : W ≃ₗ[B] W') (c : L ≃ₗ[R] L')
    (hc : ∀ x y, φ' (e x) (e y) = c (φ x y)) :
    FormIso B ψ φ ≃ FormIso B ψ φ' where
  toFun eta := ⟨eta.1.trans e, by
    obtain ⟨a, ha⟩ := eta.2
    refine ⟨a.trans c, ?_⟩
    intro x y
    exact (hc (eta.1 x) (eta.1 y)).trans (congrArg c (ha x y))⟩
  invFun eta := ⟨eta.1.trans e.symm, by
    obtain ⟨a, ha⟩ := eta.2
    refine ⟨a.trans c.symm, ?_⟩
    intro x y
    apply c.injective
    change c (φ (e.symm (eta.1 x)) (e.symm (eta.1 y))) = c (c.symm (a (ψ x y)))
    rw [← hc, e.apply_symm_apply, e.apply_symm_apply, c.apply_symm_apply, ha]⟩
  left_inv eta := by
    apply Subtype.ext
    ext x
    exact e.symm_apply_apply (eta.1 x)
  right_inv eta := by
    apply Subtype.ext
    ext x
    exact e.apply_symm_apply (eta.1 x)

@[simp] theorem transport_apply (e : W ≃ₗ[B] W') (c : L ≃ₗ[R] L')
    (hc : ∀ x y, φ' (e x) (e y) = c (φ x y)) (eta : FormIso B ψ φ) (x : V) :
    (transport e c hc eta).1 x = e (eta.1 x) := rfl

/-- Transport commutes with the right source-similitude action. -/
theorem transport_precomp (e : W ≃ₗ[B] W') (c : L ≃ₗ[R] L')
    (hc : ∀ x y, φ' (e x) (e y) = c (φ x y))
    (eta : FormIso B ψ φ) (g : bilinearSimilitudes B ψ) :
    transport e c hc (precomp eta g) = precomp (transport e c hc eta) g := by
  apply Subtype.ext
  ext x
  rfl

end Langlands.Shimura.PEL.FormIso
