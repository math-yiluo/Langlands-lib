/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import WeilConjectures.ConstructibleSheaf.FilteredColimitStabilization

/-!
# Constructible sheaves are noetherian objects

Let `X` be a Noetherian scheme and `Λ` a finite commutative ring. A constructible étale sheaf
`F` of `Λ`-modules on `X` is a noetherian object of the category of sheaves: every ascending
chain of subsheaves of `F` stabilizes
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.isNoetherianObject`).

Given a chain `f : ℕ →o Subobject F`, the colimit of the subsheaves `f n` maps monomorphically
to `F`, filtered colimits being exact in the Grothendieck abelian category of sheaves; it is
therefore constructible (`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_mono`), and one of
the legs of the colimit cocone is an epimorphism
(`AlgebraicGeometry.Etale.exists_epi_ι_app_of_isConstructibleSheaf`). The corresponding stage
then contains all the others.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace IsConstructibleSheaf

/-- **Constructible sheaves are noetherian objects.** A constructible étale sheaf of modules
over a finite ring on a Noetherian scheme is a noetherian object: ascending chains of subsheaves
stabilize. -/
theorem isNoetherianObject {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X : Scheme.{u}}
    [IsNoetherian X] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] : IsNoetherianObject F := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  let D : ℕ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    f.monotone.functor ⋙ Subobject.underlying
  let α : D ⟶ (Functor.const _).obj F :=
    { app n := (f n).arrow
      naturality n m h := by
        simp only [D, Functor.comp_obj, Functor.comp_map, Functor.const_obj_obj,
          Functor.const_obj_map, Category.comp_id]
        exact Subobject.ofLE_arrow _ }
  have : Mono α :=
    have (n : ℕ) : Mono (α.app n) := Subobject.arrow_mono (f n)
    NatTrans.mono_of_mono_app _
  let c := colimit.cocone D
  let hc := colimit.isColimit D
  let d : c.pt ⟶ F := hc.desc (Cocone.mk F α)
  have hd (n : ℕ) : c.ι.app n ≫ d = (f n).arrow := hc.fac _ n
  have : HasExactColimitsOfShape ℕ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    have : IsFiltered (AsSmall.{u + 1} ℕ) := IsFiltered.of_equivalence AsSmall.equiv
    HasExactColimitsOfShape.of_domain_equivalence _ AsSmall.equiv.symm
  have : Mono d := colim.map_mono' α hc (isColimitConstCocone _ F) d
    (fun n ↦ (hd n).trans (by simp [α]))
  have hmono (n : ℕ) : Mono (c.ι.app n) :=
    have : Mono (c.ι.app n ≫ d) := by rw [hd]; infer_instance
    mono_of_mono _ d
  have : IsConstructibleSheaf c.pt := IsConstructibleSheaf.of_mono d
  obtain ⟨n, hn⟩ := Etale.exists_epi_ι_app_of_isConstructibleSheaf hc hmono this
  have : IsIso (c.ι.app n) := isIso_of_mono_of_epi _
  refine ⟨n, fun m hm ↦ le_antisymm (f.monotone hm) ?_⟩
  refine Subobject.le_of_comm (c.ι.app m ≫ inv (c.ι.app n) : D.obj m ⟶ D.obj n) ?_
  rw [← hd n, Category.assoc, IsIso.inv_hom_id_assoc, hd m]

end IsConstructibleSheaf

end Scheme

end AlgebraicGeometry
