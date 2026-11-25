/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Exact evaluation at weakly contractible objects

## References

* Stacks Project, Tags 0946, 03DA, 03CN and 00WN
* Stacks Project, Tag 0946 (1), with the module sheaf epimorphism criterion 03DA
-/

@[expose] public section


universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

local instance (X : Scheme.{u}) (R : Sheaf (topology X) RingCat.{u + 1}) (W : X.ProEt) :
    (SheafOfModules.evaluation.{u + 1} R (op W)).Additive :=
  inferInstanceAs ((SheafOfModules.forget R ⋙
    PresheafOfModules.evaluation R.obj (op W)).Additive)

/-- Evaluation at a weakly contractible object preserves homology of module complexes. -/
theorem weaklyContractible_evaluation_preservesHomology
    (X : Scheme.{u}) (R : Sheaf (topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (hW : ∀ (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op W))) :
    (SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)).PreservesHomology := by
  let A := (sheafCompose (topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let ev := SheafOfModules.evaluation.{u + 1} A (op W)
  have : ev.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    let g := (SheafOfModules.toSheaf A).map f
    have : Epi g := inferInstance
    have : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} g).mpr inferInstance
    let g' := (sheafCompose (topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})).map g
    have : Epi g' := inferInstance
    exact (ModuleCat.epi_iff_surjective (ev.map f)).mpr (hW _ _ g' inferInstance)
  exact Functor.preservesHomology_of_preservesEpis_and_kernels ev

end AlgebraicGeometry.Scheme.ProEt
