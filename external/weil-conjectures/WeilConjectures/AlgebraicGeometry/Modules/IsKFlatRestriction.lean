/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso

/-! # K-flatness under open restriction

## References

* Stacks Project, Tag 06YB, applied to open restriction
* Stacks Project, Cohomology, Tag 06YB
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Open restriction preserves K-flat complexes of module sheaves. -/
theorem isKFlat_restrict {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K) :
    CochainComplex.IsKFlatTensor (R := X.sheaf)
      (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj K) := by
  have hstalk :=
    (RingedSpace.isKFlat_iff_stalk_isKFlat Y.toRingedSpace K).mp hK
  apply (RingedSpace.isKFlat_iff_stalk_isKFlat X.toRingedSpace _).mpr
  intro x F hF
  obtain ⟨e⟩ := nonempty_restriction_stalk_extension_iso j x K
  have h := CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat
    (j.stalkMap x).hom _ (hstalk (j x)) F hF
  let T := ((MonoidalCategory.curriedTensor
    (ModuleCat.{u} (X.presheaf.stalk x))).map₂CochainComplex).obj F
  intro i
  exact (h i).of_iso (T.mapIso e)

end AlgebraicGeometry
