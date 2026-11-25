/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement

/-! # Closed support over the intrinsic constant coefficient sheaf

The canonical coefficient map, obtained by applying inverse image to constant sections,
identifies the pulled-back constant ring with the constant ring on the source. All module
operations below use that map. No replacement of the small pro-etale site is made.

## References

* Stacks 09A5
* Stacks 03D2
* Stacks 03D6
* Stacks 03D7
* Stacks 09AH
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical constant-ring identification; its data is the recorded structure map. -/
noncomputable def sfConstantCoefficientIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A] :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing Y A) ≅
      proEtaleConstantRing X A :=
  letI : TopologicalSpace (ULift.{u + 1, u} A) := ⊥
  letI : DiscreteTopology (ULift.{u + 1, u} A) := ⟨rfl⟩
  letI := ProEtale.finiteCoefficientCommRingMap_isIso
    f (ULift.{u + 1, u} A)
  asIso (proEtaleCoefficientInverseImageMap f A)

/-- Module inverse image along the canonical constant-ring identification. -/
noncomputable abbrev sfConstantModulePullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A] :=
  proEtaleRingModulePullback f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (sfConstantCoefficientIso f A)

/-- Direct image with its constant-section scalar map, adjoint to the canonical coefficient
identification. -/
noncomputable abbrev sfConstantModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A] :=
  proEtaleRingModuleDirectImage f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (sfConstantCoefficientIso f A)

/-- The canonical inverse/direct-image adjunction over constant coefficients. -/
noncomputable abbrev sfConstantModuleAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A] :=
  proEtaleRingModuleAdjunction f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (sfConstantCoefficientIso f A)

/-- The kernel of the open adjunction unit, with morphisms induced by its naturality. -/
noncomputable def sfIntrinsicSectionsWithSupport {U T : Scheme.{u}} (j : U ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleRingModules T (proEtaleConstantRing T A) ⥤
      proEtaleRingModules T (proEtaleConstantRing T A) where
  obj N := kernel ((sfConstantModuleAdjunction j A).unit.app N)
  map φ := kernel.map _ _ φ
    ((sfConstantModuleDirectImage j A).map ((sfConstantModulePullback j A).map φ))
    ((sfConstantModuleAdjunction j A).unit.naturality φ).symm
  map_id N := equalizer.hom_ext (by simp)
  map_comp φ ψ := equalizer.hom_ext (by simp)

end AlgebraicGeometry.Scheme
