/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite modules over a noetherian ring as cokernels in `ModuleCat`

A finite module `M` over a noetherian ring `R` is finitely presented: it is the cokernel of a
morphism `Rᵐ ⟶ Rⁿ` between finite biproducts of copies of `R` in `ModuleCat R`
(`ModuleCat.exists_iso_cokernel_of_finite`).
-/

@[expose] public section

universe v

open CategoryTheory Limits

namespace ModuleCat

variable {R : Type v} [CommRing R] [IsNoetherianRing R]

/-- A finite module over a noetherian ring `R` is the cokernel of a morphism `Rᵐ ⟶ Rⁿ` between
finite biproducts of copies of `R`: choose a surjection `π : Rⁿ ⟶ M`; its kernel is finite, `R`
being noetherian, hence the image of some `Rᵐ`. -/
lemma exists_iso_cokernel_of_finite (M : ModuleCat.{v} R) [Module.Finite R M] :
    ∃ (m n : ℕ) (f : (⨁ fun _ : Fin m ↦ ModuleCat.of R R) ⟶ ⨁ fun _ : Fin n ↦ ModuleCat.of R R),
      Nonempty (M ≅ cokernel f) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  obtain ⟨m, σ, hσ⟩ := Module.Finite.exists_fin' R (LinearMap.ker π)
  let g : (Fin m → R) →ₗ[R] (Fin n → R) := (LinearMap.ker π).subtype ∘ₗ σ
  have hg : LinearMap.range g = LinearMap.ker π := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.2 hσ, Submodule.map_top,
      Submodule.range_subtype]
  let e₁ := biproductIsoPi (fun _ : Fin m ↦ ModuleCat.of R R)
  let e₂ := biproductIsoPi (fun _ : Fin n ↦ ModuleCat.of R R)
  refine ⟨m, n, e₁.hom ≫ ofHom g ≫ e₂.inv, ⟨?_⟩⟩
  exact ((π.quotKerEquivOfSurjective hπ).toModuleIso.symm ≪≫
    (Submodule.quotEquivOfEq _ _ hg).toModuleIso.symm ≪≫
    (cokernelIsoRangeQuotient (ofHom g)).symm ≪≫
    (cokernel.mapIso (e₁.hom ≫ ofHom g ≫ e₂.inv) (ofHom g) e₁ e₂ (by simp)).symm)

end ModuleCat
