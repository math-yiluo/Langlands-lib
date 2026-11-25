/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FinitePushforward

/-!
# Finite-pushforward embeddings over a field

A constructible sheaf of modules over a finite ring `Λ` on a scheme of finite type over a field
embeds into a finite direct sum of pushforwards of constant sheaves with finite values along
finite morphisms (`proposition-proper-direct-image-finite-coefficients`). A scheme of finite type
over a field is Noetherian, so this is the Noetherian case
`AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_isNoetherian`; a finitely generated
module over a finite ring is finite.

## Main statements

- `AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_locallyOfFiniteType`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Finite-pushforward embeddings
over a field.

Let `X` be of finite type over a field `k` and `F` a constructible sheaf of `Λ`-modules on
`X_ét`, for a finite ring `Λ`. There are finitely many finite morphisms `hᵢ : Yᵢ ⟶ X`, finite
`Λ`-modules `Mᵢ` and a monomorphism `F ⟶ ⨁ᵢ (hᵢ)_* Mᵢ`. The blueprint states this for
`Λ = ℤ/N`, where the `Mᵢ` are finite abelian groups killed by `N`. -/
theorem Etale.exists_mono_biproduct_lowerStar_of_locallyOfFiniteType {k : Type u} [Field k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    ∃ (r : ℕ) (Y : Fin r → Scheme.{u}) (h : ∀ i, Y i ⟶ X) (_ : ∀ i, IsFinite (h i))
      (M : Fin r → ModuleCat.{u + 1} Λ) (_ : ∀ i, Finite (M i))
      (φ : F ⟶ ⨁ fun i ↦ ((h i)_*[ModuleCat.{u + 1} Λ]).obj
        ((constantSheaf (Y i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))), Mono φ := by
  have := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  obtain ⟨r, Y, h, hh, M, hM, φ, hφ⟩ := exists_mono_biproduct_lowerStar_of_isNoetherian Λ F
  exact ⟨r, Y, h, hh, M, fun i ↦ Module.finite_of_finite Λ, φ, hφ⟩

end AlgebraicGeometry
