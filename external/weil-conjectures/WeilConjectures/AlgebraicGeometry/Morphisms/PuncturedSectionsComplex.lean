/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # The complex of sections of associated module sheaves on an open

## References

* Stacks Project, Tags 0A6T and 09T2
-/

@[expose] public noncomputable section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Associate a sheaf to an R-module and take sections on W. -/
def puncturedSectionsFunctor (R : Type u) [CommRing R] (W : (Spec (.of R)).Opens) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  tilde.functor (.of R) ⋙ modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙
    (evaluation _ _).obj (.op W)

/-- Taking sections of the associated sheaf sends a zero module map to zero. -/
instance puncturedSectionsFunctor_preservesZeroMorphisms
    (R : Type u) [CommRing R] (W : (Spec (.of R)).Opens) :
    (puncturedSectionsFunctor R W).PreservesZeroMorphisms where
  map_zero := by
    intro M N
    change (modulesSpecToSheaf.map (tilde.map (0 : M ⟶ N))).hom.app (.op W) = 0
    rw [tilde.map_zero]
    rfl

/-- Apply the associated-sheaf sections functor degreewise to a cochain complex. -/
def puncturedSectionsComplex (R : Type u) [CommRing R] (W : (Spec (.of R)).Opens)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  ((puncturedSectionsFunctor R W).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

set_option backward.isDefEq.respectTransparency false in
/-- Restrict a complex of modules to sections of its associated sheaves on W. -/
def puncturedSectionsRestriction (R : Type u) [CommRing R] (W : (Spec (.of R)).Opens)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    K ⟶ puncturedSectionsComplex R W K where
  f n := tilde.toOpen (K.X n) W
  comm' i j _ := by
    dsimp only [puncturedSectionsComplex, Functor.mapHomologicalComplex,
      puncturedSectionsFunctor, Functor.comp_map, TopCat.Sheaf.forget, evaluation]
    exact tilde.toOpen_map_app (R := CommRingCat.of R) (K.d i j) W

end AlgebraicGeometry.Scheme
