/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicOpenUnit
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
import WeilConjectures.RingTheory.ProperBaseChange.WContractibleClosedLocalization
import WeilConjectures.AlgebraicGeometry.Affine.AffineClosedSpecializationLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleShriekSpecializationZero
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenCounitMono
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenCounitEpi

/-!
# Proper/open comparison for all pro-etale module sheaves

The comparison uses sectionwise open restriction and the inverse open unit, followed
by the counit of the specified open extension adjunction. No etale-origin condition
is imposed on the sheaf.

## References

* Stacks Project, Tags 09AE and 09BN (open functors), with etale analogue Tag 0F7B
* Stacks, Tags 00YV and 03D1
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- Reexpress the existing sectionwise direct image in canonical realization coordinates.
The comparison is fixed on scalar-unit sections, so this introduces no arbitrary map. -/
noncomputable def sfProperOpenDirectImageCoordinates {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantModuleDirectImage f A ≅
      sfIntrinsicTransport A (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f) :=
  (isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
      (sfIntrinsicDirectImageComparison f A).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (sfIntrinsicModuleEquivalence X A).counitIso _ ≪≫
    Functor.leftUnitor _).symm

/-- Open restriction of a direct image, in fixed-scalar coordinates, induced by the
canonical map `Q ×_W U → Q ×_T V`. For a Cartesian square this map is an isomorphism.
Thus the comparison is exactly evaluation on the same fibre product, including maps. -/
noncomputable def sfProperOpenFixedRestrictionIso {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p ⋙
        ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i ≅
      ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) r :=
  letI := Functor.isContinuous_comp
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r)
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale k))
    (ProEt.topology W) (ProEt.topology U) (ProEt.topology V)
  letI := Functor.isContinuous_comp
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale i))
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ p)
    (ProEt.topology W) (ProEt.topology T) (ProEt.topology V)
  letI := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (inferInstance : WeaklyEtale i) (inferInstance : WeaklyEtale k) sq
  asIso (Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison
      (inferInstance : WeaklyEtale i) (inferInstance : WeaklyEtale k) sq.toCommSq)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (ProEt.topology W) (ProEt.topology V))

/-- The same sectionwise open-restriction isomorphism with the intrinsic constant-ring
module actions. Only the canonical realization unit, counit and scalar-normalized
comparison of direct images are inserted. -/
noncomputable def sfProperOpenRestrictionIso {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    proEtaleConstantModuleDirectImage p A ⋙ sfIntrinsicOpenRestriction i A ≅
      sfIntrinsicOpenRestriction k A ⋙ proEtaleConstantModuleDirectImage r A :=
  isoWhiskerRight (sfProperOpenDirectImageCoordinates A p) (sfIntrinsicOpenRestriction i A) ≪≫
    (sfIntrinsicTransportComp A _ _).symm ≪≫
    sfIntrinsicTransportIso A (sfProperOpenFixedRestrictionIso A r k i p sq) ≪≫
    sfIntrinsicTransportComp A _ _ ≪≫
    isoWhiskerLeft (sfIntrinsicOpenRestriction k A) (sfProperOpenDirectImageCoordinates A r).symm

/-- The open unit as a natural isomorphism, using the already recorded open-unit theorem. -/
noncomputable def sfProperOpenUnitIso {U V : Scheme.{u}} (k : U ⟶ V)
    [IsOpenImmersion k] : 𝟭 _ ≅ sfIntrinsicExtensionByZero k A ⋙
      sfIntrinsicOpenRestriction k A :=
  NatIso.ofComponents (fun M ↦
    letI := sfIntrinsicOpenUnit_isIso k A M
    asIso ((sfIntrinsicExtensionByZeroAdjunction k A).unit.app M))
    (fun {_ _} f ↦ (sfIntrinsicExtensionByZeroAdjunction k A).unit.naturality f)

/-- The specified `λ`: open restriction followed by the inverse of the open unit. -/
noncomputable def sfProperOpenLambda {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    sfIntrinsicExtensionByZero k A ⋙ proEtaleConstantModuleDirectImage p A ⋙
        sfIntrinsicOpenRestriction i A ≅ proEtaleConstantModuleDirectImage r A :=
  isoWhiskerLeft (sfIntrinsicExtensionByZero k A) (sfProperOpenRestrictionIso A r k i p sq) ≪≫
    isoWhiskerRight (sfProperOpenUnitIso A k).symm (proEtaleConstantModuleDirectImage r A)

/-- The specified `γ`, the transpose of `λ⁻¹` under `i_! ⊣ i^*`.
Its component is `i_!(λ_M⁻¹)` followed by the open counit at `p_* k_! M`. -/
noncomputable def sfProperOpenSheafComparison {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    proEtaleConstantModuleDirectImage r A ⋙ sfIntrinsicExtensionByZero i A ⟶
      sfIntrinsicExtensionByZero k A ⋙ proEtaleConstantModuleDirectImage p A :=
  whiskerRight (sfProperOpenLambda A r k i p sq).inv (sfIntrinsicExtensionByZero i A) ≫
    whiskerLeft (sfIntrinsicExtensionByZero k A ⋙ proEtaleConstantModuleDirectImage p A)
      (sfIntrinsicExtensionByZeroAdjunction i A).counit

/-- For `p` proper and `i` an open immersion, the counit of the extension-by-zero adjunction
for `i` at `p_* i'_! M` is an isomorphism, where `i'` is the base change of `i`. -/
theorem sfProperOpenCounit_isIso {V W T : Scheme.{u}} (p : V ⟶ T) [IsProper p]
    (i : W ⟶ T) [IsOpenImmersion i] (M :
      proEtaleRingModules (pullback p i)
        (proEtaleConstantRing (pullback p i) A)) :
    IsIso ((sfIntrinsicExtensionByZeroAdjunction i A).counit.app
      ((sfIntrinsicExtensionByZero (pullback.fst p i) A ⋙
        proEtaleConstantModuleDirectImage p A).obj M)) := by
  let f := (sfIntrinsicExtensionByZeroAdjunction i A).counit.app
    ((sfIntrinsicExtensionByZero (pullback.fst p i) A ⋙
      proEtaleConstantModuleDirectImage p A).obj M)
  letI : Mono f := sfProperOpenCounit_mono A p i M
  letI : Epi f := sfProperOpenCounit_epi A p i M
  exact isIso_of_mono_of_epi f

/-- Proper direct image commutes with open extension by zero for every pro-etale module
sheaf over a finite commutative constant ring, with its canonical comparison and naturality.
There is no quasi-compactness condition on the open immersion and no boundedness or
etale-origin restriction on the module sheaf. -/
theorem sfProperOpenSheafComparison_isIso {V W T : Scheme.{u}} (p : V ⟶ T) [IsProper p]
    (i : W ⟶ T) [IsOpenImmersion i] :
    IsIso (sfProperOpenSheafComparison A (pullback.snd p i) (pullback.fst p i) i p
      (IsPullback.of_hasPullback p i).flip) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro M
  dsimp only [sfProperOpenSheafComparison]
  have hc := sfProperOpenCounit_isIso A p i M
  letI : IsIso ((sfIntrinsicExtensionByZeroAdjunction i A).counit.app
      ((sfIntrinsicExtensionByZero (pullback.fst p i) A ⋙
        proEtaleConstantModuleDirectImage p A).obj M)) := hc
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

end AlgebraicGeometry.Scheme
