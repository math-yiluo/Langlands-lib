/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.Compactification.Defs

import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison

/-!
# Compact-support image on ringed pro-etale sites
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ S)

-- Construct an exact left adjoint using the slice presentation of the open site.
set_option backward.isDefEq.respectTransparency false in
private theorem openRestriction_exactLeftAdjoint :
    ∃ L : proEtaleRingModules X S ⥤ proEtaleRingModules Z R,
      Nonempty (L ⊣ proEtaleRingModulePullback j R S c) ∧ PreservesFiniteLimits L := by
  let U := ProEt.mk j
  have : IsOpenImmersion U.hom := inferInstanceAs (IsOpenImmersion j)
  let A := (sheafCompose (ProEt.topology Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  obtain ⟨q, ⟨eq⟩⟩ := proEtale_ringed_open_comparison U R
  have : (SheafOfModules.overFunctor.{u + 1} A U).Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  obtain ⟨L, hL, _, ⟨a⟩⟩ :=
    CategoryTheory.localized_restriction_extension_exists A U inferInstance
  have := hL
  let ef : proEtaleModuleInverseImage j R ≅
      SheafOfModules.overFunctor A U ⋙ q.inverse :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ q.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eq q.inverse
  let af : q.functor ⋙ L ⊣ proEtaleModuleInverseImage j R :=
    (q.toAdjunction.comp a).ofNatIsoRight ef.symm
  let rc := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let e := proEtaleScalarEquivalence X rc
  let ae := proEtaleRingExtensionAdjunction j R S c
  let ei := ae.leftAdjointUniq e.symm.toAdjunction
  let ae' : e.functor ⊣ proEtaleRingExtension j R S c :=
    e.toAdjunction.ofNatIsoRight ei.symm
  let ap : e.functor ⋙ q.functor ⋙ L ⊣ proEtaleRingModulePullback j R S c :=
    ae'.comp af
  exact ⟨_, ⟨ap⟩, inferInstance⟩

/-- Restriction along an open immersion has extension by zero as its left adjoint.
This universal property determines extension by zero up to its unique adjoint isomorphism. -/
@[instance] theorem proEtaleOpenRestriction_isRightAdjoint :
    (proEtaleRingModulePullback j R S c).IsRightAdjoint := by
  obtain ⟨L, ⟨a⟩, _⟩ := openRestriction_exactLeftAdjoint j R S c
  exact a.isRightAdjoint

/-- Extension by zero, specified by its adjoint universal property to actual restriction. -/
def proEtaleRingOpenExtension : proEtaleRingModules X S ⥤ proEtaleRingModules Z R :=
  (proEtaleRingModulePullback j R S c).leftAdjoint

/-- Extension by zero is additive and exact. -/
theorem proEtaleRingOpenExtension_exact :
    (proEtaleRingOpenExtension j R S c).Additive ∧
      PreservesFiniteLimits (proEtaleRingOpenExtension j R S c) ∧
      PreservesFiniteColimits (proEtaleRingOpenExtension j R S c) := by
  let a := Adjunction.ofIsRightAdjoint (proEtaleRingModulePullback j R S c)
  obtain ⟨L, ⟨b⟩, hL⟩ := openRestriction_exactLeftAdjoint j R S c
  have := hL
  have hlim : PreservesFiniteLimits (proEtaleRingOpenExtension j R S c) :=
    preservesFiniteLimits_of_natIso (b.leftAdjointUniq a)
  have : PreservesColimitsOfSize.{0, 0} (proEtaleRingOpenExtension j R S c) :=
    a.leftAdjoint_preservesColimits
  exact ⟨a.left_adjoint_additive, hlim, inferInstance⟩

/-- Additivity of extension by zero. -/
instance proEtaleRingOpenExtension_additive :
    (proEtaleRingOpenExtension j R S c).Additive :=
  (proEtaleRingOpenExtension_exact j R S c).1

/-- Left exactness of extension by zero. -/
instance proEtaleRingOpenExtension_limits :
    PreservesFiniteLimits (proEtaleRingOpenExtension j R S c) :=
  (proEtaleRingOpenExtension_exact j R S c).2.1

/-- Right exactness of extension by zero. -/
instance proEtaleRingOpenExtension_colimits :
    PreservesFiniteColimits (proEtaleRingOpenExtension j R S c) :=
  (proEtaleRingOpenExtension_exact j R S c).2.2

/-- Exact termwise extension by zero on the full unbounded derived category. -/
abbrev proEtaleRingDerivedOpenExtension :=
  (proEtaleRingOpenExtension j R S c).mapDerivedCategory

/-- Compact-support image for the chosen quasi-compact open / proper factorization.
For proper f, Compactification.ofIsProper f is its identity compactification. -/
def proEtaleRingCompactSupportImage {Y : Scheme.{u}} {f : X ⟶ Y}
    (d : Compactification f) [QuasiCompact d.i]
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology d.Z) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (cp : (proEtaleSheafInverseImage d.g CommRingCat.{u + 1}).obj RY ≅ RZ)
    (cj : (proEtaleSheafInverseImage d.i CommRingCat.{u + 1}).obj RZ ≅ RX) :
    DerivedCategory (proEtaleRingModules X RX) ⥤ DerivedCategory (proEtaleRingModules Y RY) :=
  proEtaleRingDerivedOpenExtension d.i RZ RX cj ⋙ proEtaleRingDerivedDirectImage d.g RY RZ cp

end AlgebraicGeometry.Scheme
