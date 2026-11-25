/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Canonical intrinsic finite-coefficient inverse image

The existing arbitrary-ring and continuous-function interfaces are reexported.
Here the canonical fixed-scalar inverse image is transported through the intrinsic constant-ring
realization, without choosing a coefficient identification.

## References

* Stacks Project, Modules on Sites
* Stacks, Tag 00YV
* Stacks, Tag 04JC
* Stacks, Modules on Sites
* Stacks, Section 0735
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- The realization equivalence has its additive functor. -/
noncomputable instance sfIntrinsicModuleEquivalence_functor_additive (X : Scheme.{u}) :
    (sfIntrinsicModuleEquivalence X A).functor.Additive :=
  inferInstanceAs (ProEtale.finiteCoefficientIntrinsicRealization X A).Additive

/-- Transport a fixed-scalar functor through the canonical realization equivalences. -/
noncomputable def sfIntrinsicTransport {X Y : Scheme.{u}}
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      proEtaleRingModules Y (proEtaleConstantRing Y A) :=
  (sfIntrinsicModuleEquivalence X A).inverse ⋙ F ⋙
    (sfIntrinsicModuleEquivalence Y A).functor

/-- Transport natural isomorphisms by the same coefficient realization. -/
noncomputable def sfIntrinsicTransportIso {X Y : Scheme.{u}}
    {F G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))} (e : F ≅ G) :
    sfIntrinsicTransport A F ≅ sfIntrinsicTransport A G :=
  isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
    (isoWhiskerRight e (sfIntrinsicModuleEquivalence Y A).functor)

/-- The composition comparison inserts the realization unit at the middle scheme. -/
noncomputable def sfIntrinsicTransportComp {X Y Z : Scheme.{u}}
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (G : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    sfIntrinsicTransport A (F ⋙ G) ≅ sfIntrinsicTransport A F ⋙ sfIntrinsicTransport A G :=
  isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
    (isoWhiskerRight
      (isoWhiskerLeft F ((sfIntrinsicModuleEquivalence Y A).funInvIdAssoc G).symm)
      (sfIntrinsicModuleEquivalence Z A).functor)

/-- Exact inverse image with the intrinsic constant scalar action. -/
noncomputable def sfIntrinsicPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  sfIntrinsicTransport A (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)

/-- Additivity of this canonical transport. -/
noncomputable instance sfIntrinsicPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sfIntrinsicPullback A f).Additive :=
  inferInstanceAs ((sfIntrinsicModuleEquivalence Y A).inverse ⋙
    ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
    (sfIntrinsicModuleEquivalence X A).functor).Additive

/-- Left exactness is preserved by the two realization equivalences. -/
noncomputable instance sfIntrinsicPullback_preservesFiniteLimits {X Y : Scheme.{u}}
    (f : X ⟶ Y) : PreservesFiniteLimits (sfIntrinsicPullback A f) :=
  inferInstanceAs (PreservesFiniteLimits ((sfIntrinsicModuleEquivalence Y A).inverse ⋙
    ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
    (sfIntrinsicModuleEquivalence X A).functor))

/-- Right exactness is preserved by the two realization equivalences. -/
noncomputable instance sfIntrinsicPullback_preservesFiniteColimits {X Y : Scheme.{u}}
    (f : X ⟶ Y) : PreservesFiniteColimits (sfIntrinsicPullback A f) :=
  inferInstanceAs (PreservesFiniteColimits ((sfIntrinsicModuleEquivalence Y A).inverse ⋙
    ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
    (sfIntrinsicModuleEquivalence X A).functor))

/-- Canonical pullback composition, with its actual coefficient transports. -/
noncomputable def sfIntrinsicPullbackComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sfIntrinsicPullback A (f ≫ g) ≅ sfIntrinsicPullback A g ⋙ sfIntrinsicPullback A f :=
  sfIntrinsicTransportIso A
    (ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g) ≪≫
    sfIntrinsicTransportComp A _ _

/-- Identity pullback, using the realization counit. -/
noncomputable def sfIntrinsicPullbackId (X : Scheme.{u}) :
    sfIntrinsicPullback A (𝟙 X) ≅ 𝟭 _ :=
  sfIntrinsicTransportIso A
    (ProEtale.upperStarId (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X) ≪≫
    (sfIntrinsicModuleEquivalence X A).counitIso

/-- The ordinary uncompleted unbounded derived inverse image, by exact termwise descent. -/
noncomputable abbrev sfIntrinsicDerivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory X A :=
  (sfIntrinsicPullback A f).mapDerivedCategory

end AlgebraicGeometry.Scheme
