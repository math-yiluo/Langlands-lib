/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality

/-! # Restriction of scalars of locally free internal modules

`ProEtale.IsLocallyFree` is preserved by restriction along an invertible coefficient map.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Tag 03DO.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Restriction along an invertible coefficient map preserves local finite freeness.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Modules on Sites, Tag 03DO.
(auxiliary; not a blueprint node)

Use the same cover. On each member apply the existing free_comap and
free_of_iso to the mapModComapIso comparison. -/
lemma IsLocallyFree.comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) T}
    (hP : IsLocallyFree T P) : IsLocallyFree R ((Mod.comap φ).obj P) := by
  obtain ⟨C, hC⟩ := hP
  refine ⟨C, fun s ↦ ?_⟩
  let G := ProEtale.upperStar Ab.{u + 1} (C.f s)
  exact ProEtale.free_of_iso (ProEtale.free_comap (G.map φ) (hC s))
    ((G.mapModComapIso φ).app P).symm

end AlgebraicGeometry.ProEtale
