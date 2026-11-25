/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.QuasiAffineFiniteFreeQuotient
import WeilConjectures.AlgebraicGeometry.Modules.DualFiniteFreeQuotientEmbedding

/-! # Universal finite free embeddings on Noetherian affine opens

## References

* Stacks Project, Tag 0EKP, the dual-surjection construction in (2) to (3)
* Stacks Project, Tag 0EKP, first dual-surjection construction in (2) to (3), with the ample
  invertible module equal to the structure sheaf
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

/-- A finite locally free module on an open of a Noetherian affine scheme embeds into
finite free with finite locally free cokernel, and this embedding remains mono after
arbitrary scheme pullback. -/
theorem exists_universally_mono_free
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (V : (Spec (.of R)).Opens) (M : V.toScheme.Modules) [M.IsFiniteLocallyFree] :
    ∃ (r : ℕ) (α : M ⟶ free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r))),
      Mono α ∧ (cokernel α).IsFiniteLocallyFree ∧
      ∀ (Y : Scheme.{u}) (g : Y ⟶ V.toScheme), Mono ((Modules.pullback g).map α) := by
  have := IsFiniteLocallyFree.dual M
  obtain ⟨r, β, hβ⟩ := exists_epi_free_of_isFiniteLocallyFree V (dual M)
  have : Epi β := hβ
  refine ⟨r, SheafOfModules.bidual (R := V.toScheme.sheaf) M ≫ dualMap β ≫
    (SheafOfModules.homObjFreeUnitIso (R := V.toScheme.sheaf) (ULift.{u} (Fin r))).hom, ?_⟩
  exact dual_free_quotient_embedding M β

end AlgebraicGeometry.Scheme.Modules
