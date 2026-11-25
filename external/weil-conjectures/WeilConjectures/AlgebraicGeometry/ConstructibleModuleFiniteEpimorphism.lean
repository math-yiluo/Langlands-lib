/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteZeroCokernel

/-!
# Finite affine free covers of constructible module sheaves

Source: Stacks Project, Etale Cohomology, Tag 095N, proof of the finite surjection.
(blueprint: lem-weil-pbc-constructible-module-finite-epimorphism).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A zero cokernel map is epi.
(blueprint: lem-weil-pbc-constructible-module-finite-epimorphism) -/
theorem exists_affine_free_etale_epimorphism
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W =>
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
    ∃ (n : ℕ) (U : Fin n → X.Etale), (∀ i, IsAffine (U i).left) ∧
      ∃ g : (∐ fun i : Fin n => P (U i)) ⟶ F, Epi g := by
  classical
  dsimp
  obtain ⟨n, U, hU, g, hg⟩ := exists_affine_free_etale_zero_cokernel X Λ F hF
  obtain ⟨hzero⟩ := hg
  exact ⟨n, U, hU, g, (Preadditive.epi_of_isZero_cokernel g) hzero⟩

end AlgebraicGeometry.Scheme
