/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Lisse sheaves of rank one

A sheaf `L` of `Λ`-modules on the small étale site of a scheme `X` is *lisse of rank one* if
there is an étale cover `{u_α : X_α ⟶ X}` such that every pullback `u_α^* L` is isomorphic to
the constant sheaf `Λ_{X_α}`.

## Main definitions

- `AlgebraicGeometry.Scheme.IsLisseRankOneSheaf`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `definition-lisse-sheaves--1`: Lisse sheaf of rank one.

A sheaf `L` of `Λ`-modules on `X_ét` is *lisse of rank one* if there is an étale cover
`{u_α : X_α ⟶ X}` of `X` such that each étale pullback `u_α^* L`
(`AlgebraicGeometry.Etale.upperStar`) is isomorphic to the constant sheaf `Λ_{X_α}` with
value `Λ`. -/
def IsLisseRankOneSheaf (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
    Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj L ≅
      (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))

/-- Being lisse of rank one is invariant under isomorphism. -/
lemma IsLisseRankOneSheaf.of_iso {L L' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (e : L ≅ L') (hL : IsLisseRankOneSheaf L) : IsLisseRankOneSheaf L' := by
  obtain ⟨𝒰, h⟩ := hL
  exact ⟨𝒰, fun i ↦ (h i).map fun f ↦ (Etale.upperStar _ (𝒰.f i)).mapIso e.symm ≪≫ f⟩

end AlgebraicGeometry.Scheme
