/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierTensorEigenmaps
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierIsotypicRecognition
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierTraceTensorAddDescent

/-! # Tensor addition of condensed Artin–Schreier sheaves

Source: latest blueprint, sec-fourier-transform/sk-lem-as-properties,
lemma-artin-schreier-character-sheaf, proof Step 5, root addition (blueprint:
lem-fd-as-trace-tensor-add).

Stated for any condensed coefficient ring in which `q = #k` is a unit and any nontrivial
character of `k`; the Qbar trace-character case is the tensor clause of
`qlbar_artinSchreier_trace_tensor_properties`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ArtinSchreierTrace

/-- `L_{ψ,f} ⊗ L_{ψ,g} ≅ L_{ψ,f+g}` for condensed Artin–Schreier sheaves.
Source: blueprint lemma-artin-schreier-character-sheaf, proof Step 5 (blueprint:
lem-fd-as-trace-tensor-add).

Proof: on the product of the finite etale root covers of `f` and `g`, root addition
constructs eigenmaps from the tensor sheaf and the sum-function sheaf to the same regular
direct image. Both have character `(a,b) ↦ ψ(a)ψ(b)` and invertible adjoints. Normalized
averaging fixes each map. Evaluation on the character-projector image is monic by
transitivity, and either invertible adjoint splits that evaluation, making it an
isomorphism. Thus each map followed by the projector image factor is locally invertible.
Cover conservativity gives two global isomorphisms to the same image; compose the first
with the inverse of the second. The empty base and `p = 2` need no change. -/
theorem condensedArtinSchreier_tensor_add_generic
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]
    (ψ : AddChar k (MonObj.Γ Λ)) (hψ : ψ ≠ 1)
    (hq : IsUnit (Fintype.card k : MonObj.Γ Λ))
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f g : Γ(X, ⊤)) :
    Nonempty (ProEtale.condensedArtinSchreierSheafOf Λ k X ψ f ⊗
      ProEtale.condensedArtinSchreierSheafOf Λ k X ψ g ≅
      ProEtale.condensedArtinSchreierSheafOf Λ k X ψ (f + g)) := by
  obtain ⟨Y, hfin, het, hsurj, σ, htrans, φ₁, φ₂, hφ₁, hφ₂⟩ :=
    condensed_artinSchreier_tensor_eigenmaps Λ k ψ hψ hq X f g
  have : IsFinite Y.hom := hfin
  have : Etale Y.hom := het
  have hq' : IsUnit (Fintype.card (k × k) : MonObj.Γ Λ) := by
    simpa only [Fintype.card_prod, Nat.cast_mul] using hq.mul hq
  obtain ⟨U₁, hU₁⟩ := condensed_isotypic_recognition Λ Y hsurj (k × k)
    σ (tensorAddCharacter ψ) hq' htrans φ₁ hφ₁
  obtain ⟨U₂, hU₂⟩ := condensed_isotypic_recognition Λ Y hsurj (k × k)
    σ (tensorAddCharacter ψ) hq' htrans φ₂ hφ₂
  obtain ⟨e₁⟩ := condensedArtinSchreier_tensor_add_of_local_map Λ _ U₁ hU₁
  obtain ⟨e₂⟩ := condensedArtinSchreier_tensor_add_of_local_map Λ _ U₂ hU₂
  exact ⟨e₁ ≪≫ e₂.symm⟩

end AlgebraicGeometry.ArtinSchreierTrace
