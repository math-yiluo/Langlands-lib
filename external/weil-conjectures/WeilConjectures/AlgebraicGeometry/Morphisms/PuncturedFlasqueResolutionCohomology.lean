/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedSectionsComplex
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedFlasqueResolutionComparison
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Flasque associated-module resolutions compute cohomology on an open

## References

* Stacks Project, Tag 09T2, Lemma 36.8.1, and Tag 0A6T, Lemma 51.2.1
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The sections complex of an associated injective-module resolution computes the
cohomology of the structure sheaf on any open of a Noetherian affine scheme. -/
theorem nonempty_open_h_addEquiv_injective_sections
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (W : (Spec (.of R)).Opens)
    (I : InjectiveResolution (ModuleCat.of R R : ModuleCat.{u} R)) (n : ℕ) :
    Nonempty (Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) n ≃+
      ((puncturedSectionsComplex R W I.cocomplex).homology n).carrier) := by
  obtain ⟨f, g, hgf, hfg⟩ := punctured_flasque_resolution_comparison_maps R W I n
  let e : Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) n ≃+
      ((puncturedSectionsComplex R W I.cocomplex).homology n).carrier :=
    { toEquiv :=
        { toFun := f
          invFun := g
          left_inv := hgf
          right_inv := hfg }
      map_add' := f.map_add }
  exact ⟨e⟩

end AlgebraicGeometry.Scheme
