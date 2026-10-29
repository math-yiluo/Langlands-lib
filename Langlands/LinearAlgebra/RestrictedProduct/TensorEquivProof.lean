/-
Derived by Worker 963 (2026): prove the published grouped inverse-law target
`RestrictedProduct.TensorEquivInverseLaws`. It concerns the published
adaptations of the equivalences of Imperial FLT, commit
923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean:234-244
(Copyright (c) 2025 Matthew Jasper, Apache-2.0, author Matthew Jasper).
No source code is copied: the original does not state or prove this target.
The proof uses only Mathlib's `LinearEquiv.symm_apply_apply` and
`LinearEquiv.apply_symm_apply`, after identifying each canonical forward map
with its equivalence's forward function by `rfl`.
The upstream license is retained at licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.LinearAlgebra.RestrictedProduct.TensorEquivStatement

namespace RestrictedProduct

universe uR uM uι uN

/-- Both inverse laws for each published restricted-product tensor
equivalence and its canonical forward map. -/
theorem tensorEquivInverseLaws_proof : TensorEquivInverseLaws.{uR, uM, uι, uN} := by
  constructor
  · intro R M _ _ _ _ _ ι N _ _ ℱ L e f
    have hf : ∀ x, f x = e x := fun _ ↦ rfl
    exact ⟨fun x ↦ by rw [hf]; exact e.symm_apply_apply x,
      fun y ↦ by rw [hf]; exact e.apply_symm_apply y⟩
  · intro R M _ _ _ ι N _ _ L ℱ _ _ e f
    have hf : ∀ x, f x = e x := fun _ ↦ rfl
    exact ⟨fun x ↦ by rw [hf]; exact e.symm_apply_apply x,
      fun y ↦ by rw [hf]; exact e.apply_symm_apply y⟩

end RestrictedProduct
