/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafModule

/-!
# Morphisms of constant étale sheaves of modules on a connected scheme

On a connected scheme `X`, the constant sheaf functor `M ↦ M_X` on étale sheaves of
`Λ`-modules is fully faithful, as the unit `M ⟶ Γ(X, M_X)` of the adjunction with global
sections is an isomorphism. Hence a morphism `N_X ⟶ M_X` is `f_X` for a linear map `f`, which is
injective as soon as the morphism is injective on global sections.

## Main statements

- `AlgebraicGeometry.Scheme.exists_injective_constantSheaf_map_eq`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [ConnectedSpace X] {Λ : Type (u + 1)} [CommRing Λ]

/-- On a connected scheme, a morphism of constant étale sheaves of modules `N_X ⟶ M_X` which is
injective on global sections is the constant sheaf morphism of an injective linear map
`N ⟶ M`. -/
theorem exists_injective_constantSheaf_map_eq {M N : ModuleCat.{u + 1} Λ}
    (χ : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
    (hχ : Function.Injective (χ.hom.app (op (⊤_ X.Etale)))) :
    ∃ f : N ⟶ M, Function.Injective f ∧
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map f = χ := by
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal
  have : Mono (χ.hom.app (op (⊤_ X.Etale))) := (ModuleCat.mono_iff_injective _).2 hχ
  refine ⟨adj.unit.app N ≫ χ.hom.app (op (⊤_ X.Etale)) ≫ inv (adj.unit.app M),
    (ModuleCat.mono_iff_injective _).1 inferInstance, (adj.homEquiv _ _).injective ?_⟩
  rw [adj.homEquiv_unit, adj.homEquiv_unit, adj.unit_naturality]
  simp

end AlgebraicGeometry.Scheme
