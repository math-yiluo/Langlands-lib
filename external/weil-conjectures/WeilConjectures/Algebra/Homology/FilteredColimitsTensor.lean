/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.Algebra.Homology.FilteredColimitsTensorTotal
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions

/-!
# Filtered colimits and tensor complexes of sheaves of modules

Source: Stacks Project, Modules on Sites, Lemmas 03DB and 03EP
(blueprint: lem-pc-module-filtered-colimits-tensor).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

set_option hygiene false in
local notation "Mod" R => SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- Filtered colimits of sheaves of modules are exact, and commute with tensor
complexes and their direct-sum totalizations. Source: Stacks Project, Modules
on Sites, Lemmas 03DB and 03EP (blueprint: lem-pc-module-filtered-colimits-tensor).

Proof: (1) `prop-pur-kinjective-resolutions-exist` supplies the Grothendieck
abelian property and exact filtered colimits; consequently they preserve kernels,
cokernels and cohomology. (2) By `lem-pc-sheaf-modules-tensor-closed`, tensoring
is a left adjoint and preserves colimits termwise, compatibly with differentials.
(3) In each degree, the direct-sum totalization of `def-pc-tensor-complex-sheaves`
is a colimit indexed by pairs of degrees of fixed sum. Colimits commute with
these colimits, and functoriality makes the isomorphisms commute with the signed
differentials. Preservation states that the canonical comparison is invertible,
not merely that the two total complexes happen to be isomorphic. -/
theorem filteredColimitsTensorComplex
    (C : Type u) [Category.{u} C] (J : GrothendieckTopology C)
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (I : Type u) [Category.{u} I] [IsFiltered I] :
    HasExactColimitsOfShape I (Mod R) ∧
      ∀ P : CochainComplex (Mod R) ℤ,
        PreservesColimitsOfShape I
          ((((@curriedTensor (Mod R) _ (monoidalCategory R)).mapBifunctorHomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj P) ⋙
            HomologicalComplex₂.totalFunctor (Mod R) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ) (ComplexShape.up ℤ)) := by
  let := (grothendieckAbelian_and_functorial_kInjective_resolutions J R).1
  constructor
  · exact AB5OfSize.ofShape I
  · exact preservesFilteredColimitsTensorTotal C J R I

end SheafOfModules
