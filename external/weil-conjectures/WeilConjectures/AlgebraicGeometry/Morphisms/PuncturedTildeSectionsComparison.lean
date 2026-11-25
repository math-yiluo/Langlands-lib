/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedTildeResolutionExact
public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedSectionsComplex

/-! # Sections of restricted associated-sheaf complexes

## References

* Stacks Project, Tag 0A6T (proof of Lemma 51.2.1)
-/

@[expose] public noncomputable section

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- Sections on the whole of `W` of a restricted associated-sheaf complex are
its associated `R`-module sections on `W`, after forgetting scalars. -/
theorem punctured_tilde_sections_comparison
    (R : Type u) [CommRing R] (W : (Spec (.of R)).Opens)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    let Γ := sheafToPresheaf
      (Opens.grothendieckTopology W.toScheme.carrier)
        AddCommGrpCat.{u} ⋙ (evaluation _ _).obj (op ⊤)
    Nonempty (((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (((puncturedRestrictedAbelianFunctor R W).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K)) ≅
      (((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (puncturedSectionsComplex R W K))) := by
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun n ↦ ?_) ?_⟩
  · exact (((SheafOfModules.toSheaf (Spec (.of R)).ringCatSheaf).obj
      ((tilde.functor (.of R)).obj (K.X n))).obj.mapIso
        (eqToIso (congrArg op W.ι_image_top)))
  · intro i j h
    exact (((SheafOfModules.toSheaf (Spec (.of R)).ringCatSheaf).map
      ((tilde.functor (.of R)).map (K.d i j))).hom.naturality
        (eqToHom (congrArg op W.ι_image_top))).symm

end AlgebraicGeometry.Scheme
