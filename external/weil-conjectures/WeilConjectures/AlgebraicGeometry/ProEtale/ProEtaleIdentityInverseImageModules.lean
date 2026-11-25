/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # Identity inverse image with its actual inverse-image coefficient sheaf

## References

* Stacks Project, Tags 09A5 and 03D2
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtaleTensorComparison

private def restrictIdentityIso (X : Scheme.{u})
    (S : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    SheafOfModules.restrictScalars.{u + 1} (𝟙 S) ≅
      𝟭 (SheafOfModules.{u + 1} S) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact { hom := { val := 𝟙 _ }, inv := { val := 𝟙 _ } }
  · intro M N f
    ext U x
    rfl

private def inverseIdentityIso (X : Scheme.{u}) (R : Rings X) :
    inverse (𝟙 X) R ≅ AlgebraicGeometry.ProEtaleTensorComparison.restrict (ringId R).hom := by
  refine NatIso.ofComponents (fun M ↦ moduleId R M) ?_
  intro M N f
  apply inverseModule_hom_ext (𝟙 X)
  intro V s
  change (moduleId R N).hom.val.app _
      (((inverse (𝟙 X) R).map f).val.app _ (inverseSection (𝟙 X) M V s)) =
    f.val.app _ ((moduleId R M).hom.val.app _ (inverseSection (𝟙 X) M V s))
  rw [inverseSection_map, moduleId_sections, moduleId_sections]
  exact (PresheafOfModules.naturality_apply f.val
    ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).op s).symm

/-- The raw identity pullback differs from the identity only by restriction of scalars
along the canonical identity ring isomorphism. This retains exactly the coefficient
sheaf appearing in integral local models. -/
theorem proEtaleRawIdentityPullback_comparison (X : Scheme.{u}) (R : Rings X) :
    Nonempty (proEtaleRingModulePullback (𝟙 X) R (inverseRing (𝟙 X) R) (Iso.refl _) ≅
      AlgebraicGeometry.ProEtaleTensorComparison.restrict (ringId R).hom) := by
  let S := inverseRing (𝟙 X) R
  let E := proEtaleRingExtension (𝟙 X) R S (Iso.refl _)
  let a := proEtaleRingExtensionAdjunction (𝟙 X) R S (Iso.refl _)
  let b : 𝟭 (Modules S) ⊣ SheafOfModules.restrictScalars
      (𝟙 ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) :=
    Adjunction.id.ofNatIsoRight (restrictIdentityIso X _).symm
  let e : E ≅ 𝟭 (Modules S) := a.leftAdjointUniq b
  let e' : proEtaleRingModulePullback (𝟙 X) R S (Iso.refl _) ≅ inverse (𝟙 X) R :=
    Functor.isoWhiskerLeft (inverse (𝟙 X) R) e ≪≫ Functor.rightUnitor _
  exact ⟨e' ≪≫ inverseIdentityIso X R⟩

end AlgebraicGeometry.Scheme
