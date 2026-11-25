/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.SixFunctorOperationDatumStages
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerDefinitions
public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteSupportCandidateComposition

/-! # The specified candidate compact-support compositor

## Implementation details

The four-factor construction is shared by the Cartesian assembly and its canonical site square,
so both use one declaration without unfolding the four comparison factors.

## References

* Stacks Project, Tags 0F7J and 0F7K
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.ProjectionTriangleAssembly

/-- The canonical origin compositor at three specified candidates, with the canonical
candidate comparisons inserted on both ends. This extends the existing tower component
notation to an arbitrary retained origin object; it chooses no comparison maps. -/
def candidateCompositor (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).FullSubcategory) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cg).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cf).obj K.obj) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cfg).obj K.obj :=
  letI := cf.hasCompactification
  letI := cg.hasCompactification
  letI := cfg.hasCompactification
  (WeilConjectures.CompactSupportFiniteProjection.finiteSupportCandidateCompositionCore
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Y).ι
    (originCompactSupport Λ f)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cf)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cg)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cfg)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (f ≫ g))
    (towerCandidateComparison Λ cf (HasCompactification.compactification f))
    (towerCandidateComparison Λ cg (HasCompactification.compactification g))
    (originCompositionAmbient Λ f g)
    (towerCandidateComparison Λ (HasCompactification.compactification (f ≫ g)) cfg).symm).hom.app K

end AlgebraicGeometry.ProEtale.ProjectionTriangleAssembly
