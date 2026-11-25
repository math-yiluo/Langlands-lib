/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact

/-!
# Data for scalar restriction and open adjunction normalization

The comparisons are `sfOpenRestriction` and its exact termwise
localization. Normalization is expressed on the open adjunction unit: on each
nonzero summand of the defining extension presheaf it is the identity; maps from
all remaining values, which are zero, are unique. Thus this unit equation is
precisely the pre-sheafification normalization, without a choice of stalks.

## References

* Tag 015F
* Tag 04VG
* Stacks Tags 03DI and 03CY
* Stacks Tags 03CY and 03DA
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare

namespace AlgebraicGeometry.Scheme

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]

/-- The sectionwise coefficient square for restriction to an open, transported by the
canonical realization equivalences; its fixed-scalar middle square is the identity. -/
def sfOpenRestrictionCoefficientSquare {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    proEtaleCoefficientRestrictScalars Z φ ⋙ sfIntrinsicOpenRestriction j A ≅
      sfIntrinsicOpenRestriction j B ⋙ proEtaleCoefficientRestrictScalars U φ :=
  Functor.isoWhiskerRight (sfInverseRealizationRestriction Z φ)
      (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        (sfIntrinsicModuleEquivalence U A).functor) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Z B).inverse
      (Functor.isoWhiskerRight (Iso.refl
        (sfFixedRestriction Z φ ⋙
          ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j))
        (sfIntrinsicModuleEquivalence U A).functor) ≪≫
    Functor.isoWhiskerLeft
      ((sfIntrinsicModuleEquivalence Z B).inverse ⋙
        ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
      (sfRealizationRestriction U φ).symm

/-- Identity coefficient restriction in fixed-scalar coordinates, with the identity
on every section. -/
def sfOpenFixedRestrictionId (T : Scheme.{u}) (R : Type u) [CommRing R] :
    sfFixedRestriction T (RingHom.id R) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M ↦
    (fullyFaithfulSheafToPresheaf (ProEt.topology T) _).preimageIso
      (Functor.isoWhiskerLeft M.obj
        (ModuleCat.restrictScalarsId' (RingHom.id R).ulift rfl)))
    (fun f ↦ by ext V x; rfl)

/-- The canonical identity coefficient comparison in intrinsic coordinates. It is
transported from the sectionwise identity, using the already section-normalized
realization comparison and the realization counit. -/
def sfOpenCoefficientRestrictionId (T : Scheme.{u}) (R : Type u)
    [CommRing R] [Finite R] :
    proEtaleCoefficientRestrictScalars T (RingHom.id R) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence T R).counitIso.symm
      (proEtaleCoefficientRestrictScalars T (RingHom.id R)) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence T R).inverse
      (sfRealizationRestriction T (RingHom.id R)) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence T R).inverse
      (Functor.isoWhiskerRight (sfOpenFixedRestrictionId T R)
        (sfIntrinsicModuleEquivalence T R).functor) ≪≫
    (sfIntrinsicModuleEquivalence T R).counitIso

/-- The identity on the extension presheaf, expressed by its generators over the
open. The unit of the recorded adjunction is the sheafification map on those
generators. Every other presheaf value is zero, so this equation includes all its
components. The coefficient square uses only the canonical realization maps. -/
def SfOpenRestrictionNormalized {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B)
    (e : proEtaleCoefficientRestrictScalars U φ ⋙ sfIntrinsicExtensionByZero j A ≅
      sfIntrinsicExtensionByZero j B ⋙ proEtaleCoefficientRestrictScalars Z φ) : Prop :=
  ∀ M : proEtaleRingModules U (proEtaleConstantRing U B),
    (sfIntrinsicExtensionByZeroAdjunction j A).unit.app
        ((proEtaleCoefficientRestrictScalars U φ).obj M) ≫
      (sfIntrinsicOpenRestriction j A).map (e.hom.app M) ≫
      (sfOpenRestrictionCoefficientSquare j φ).hom.app
        ((sfIntrinsicExtensionByZero j B).obj M) =
    (proEtaleCoefficientRestrictScalars U φ).map
      ((sfIntrinsicExtensionByZeroAdjunction j B).unit.app M)

end AlgebraicGeometry.Scheme
