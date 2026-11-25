/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Unbounded derived direct image on ringed spaces

Source: Stacks Project, Cohomology, Section 20.28 (Tag 079V), construction preceding
Tag 079W (blueprint: def-pc-ringed-spaces-derived-direct-image).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-- The Grothendieck structure supplied by the small-site resolution theorem.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image). -/
instance moduleGrothendieckAbelian (X : RingedSpace.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X)) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
    (Opens.grothendieckTopology X) X.sheaf).1

/-- Specialization of Mathlib's module pushforward to a ringed-space morphism.
Its sections on V are the sections on the inverse image of V, with scalar action
through g-sharp, and its map on morphisms is the component on that inverse image.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image). -/
def moduleDirectImage {X Y : RingedSpace.{u}} (g : X ⟶ Y) :
    SheafOfModules.{u} (moduleRings X) ⥤ SheafOfModules.{u} (moduleRings Y) :=
  SheafOfModules.pushforward (F := Opens.map g.hom.base)
    (R := moduleRings X) (S := moduleRings Y)
    ⟨Functor.whiskerRight g.hom.c (forget₂ CommRingCat RingCat)⟩

/-- Additivity of module direct image. Source: Stacks, Tag 079V
(blueprint: def-pc-ringed-spaces-derived-direct-image). -/
instance moduleDirectImage_additive {X Y : RingedSpace.{u}} (g : X ⟶ Y) :
    (moduleDirectImage g).Additive := by
  constructor
  intro A B f h
  rfl

variable {X Y : RingedSpace.{u}}
  [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
  [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]

/-- Resolve functorially, apply direct image termwise, and localize on the target.
The resolution functor and its natural quasi-isomorphism are the existing
`CochainComplex.kInjectiveResolutionFunctor` and `toKInjectiveResolution`.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image). -/
def resolvedModuleDirectImage (g : X ⟶ Y) :
    CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings Y)) :=
  CochainComplex.kInjectiveResolutionFunctor.{u} (SheafOfModules.{u} (moduleRings X)) ⋙
    (moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- Resolved direct image inverts quasi-isomorphisms.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image).
Proof: naturality of the resolution map and two-out-of-three show that I(s) is a
quasi-isomorphism when s is one. Both its endpoints are K-injective. By
`CochainComplex.IsKInjective.quasiIso_iff` (lem-weil-pbc-kinjective-hom-derived),
I(s) is a homotopy equivalence. Additive direct image preserves this equivalence,
and the target localization therefore sends it to an isomorphism. -/
theorem resolvedModuleDirectImage_inverts (g : X ⟶ Y) :
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (moduleRings X))
      (ComplexShape.up ℤ)).IsInvertedBy (resolvedModuleDirectImage g) := by
  intro K L s hs
  let C := SheafOfModules.{u} (moduleRings X)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} C
  let η := CochainComplex.toKInjectiveResolution.{u} C
  have hη (M : CochainComplex C ℤ) : QuasiIso (η.app M) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C M).2
  have : QuasiIso s := hs
  have : IsIso (DerivedCategory.Q.map s) := inferInstance
  have : QuasiIso (η.app K ≫ I.map s) := by
    rw [← η.naturality s]
    let _ := hη L
    change QuasiIso (s ≫ η.app L)
    infer_instance
  let _ := hη K
  have : QuasiIso (I.map s) := by
    exact (quasiIso_iff_comp_left (η.app K) (I.map s)).mp inferInstance
  have hi : IsIso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (I.map s)) :=
    HomotopyCategory.quotient_inverts_homotopyEquivalences _ _ _
      ((CochainComplex.IsKInjective.quasiIso_iff (I.map s)).mp inferInstance)
  change IsIso (DerivedCategory.Q.map
    (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).map (I.map s)))
  have : IsIso ((DerivedCategory.Qh).map
    (((moduleDirectImage g).mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (I.map s)))) := by
    infer_instance
  exact (NatIso.isIso_map_iff
    (DerivedCategory.quotientCompQhIso _)
    (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).map (I.map s))).mp
      this

/-- The unbounded derived direct image: the right derived functor
`CategoryTheory.Functor.rightDerivedFunctor` (the landed unbounded right derived functor
of an additive functor on a category with K-injective resolutions) of the module direct
image. It is computed by K-injective resolutions: its unit is an isomorphism on every
K-injective complex. The K-injective resolutions come from `moduleGrothendieckAbelian`.
Source: Stacks, Tag 079V, preceding Tag 079W
(blueprint: def-pc-ringed-spaces-derived-direct-image). -/
abbrev derivedModuleDirectImage (g : X ⟶ Y) :
    DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings Y)) :=
  (moduleDirectImage g).rightDerivedFunctor

/-- The defining comparison: Q followed by Rg-star is isomorphic to the functorial
K-injective resolution followed by termwise g-star and Q, so Rg-star(QK) = Q(g-star I(K))
and Rg-star(Q f) = Q(g-star I(f)) up to this natural isomorphism.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image).
Proof: the unit of the right derived functor is an isomorphism on the K-injective
complexes I(K); compose it with Rg-star applied to the inverse of Q of the natural
quasi-isomorphism K to I(K), which is natural in K. -/
theorem derivedModuleDirectImageFactorization (g : X ⟶ Y) :
    Nonempty (DerivedCategory.Q ⋙ derivedModuleDirectImage g ≅ resolvedModuleDirectImage g) := by
  let C := SheafOfModules.{u} (moduleRings X)
  let D := SheafOfModules.{u} (moduleRings Y)
  let F := moduleDirectImage g
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} C
  let η := CochainComplex.toKInjectiveResolution.{u} C
  let γ : DerivedCategory.Q ⟶ I ⋙ DerivedCategory.Q :=
    Functor.whiskerRight η DerivedCategory.Q
  have hγ : IsIso γ := by
    have (K : CochainComplex C ℤ) : IsIso (γ.app K) := by
      have : QuasiIso (η.app K) :=
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C K).2
      change IsIso (DerivedCategory.Q.map (η.app K))
      infer_instance
    exact NatIso.isIso_of_isIso_app γ
  let β : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    (Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso D)).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ))
      F.rightDerivedFunctorUnit ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C) F.rightDerivedFunctor).hom
  have hβ : IsIso (Functor.whiskerLeft I β) := by
    have (K : CochainComplex C ℤ) : IsIso ((Functor.whiskerLeft I β).app K) := by
      dsimp [β]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact ⟨asIso (Functor.whiskerRight γ F.rightDerivedFunctor) ≪≫
    (asIso (Functor.whiskerLeft I β)).symm⟩

/-- Any K-injective resolution computes the same derived direct image.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image).
Proof: the bijection `CochainComplex.IsKInjective.Qh_map_bijective` lifts the
isomorphism QI(K) to QJ to a homotopy class I(K) to J. Its representative is a
quasi-isomorphism and therefore a homotopy equivalence by `quasiIso_iff`.
Apply additive direct image and Q, and compose with the defining factorization
(equivalently: the unit of the right derived functor is an isomorphism at J). -/
theorem derivedModuleDirectImage_computed_by_resolution (g : X ⟶ Y)
    {K J : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ}
    (s : K ⟶ J) [QuasiIso s] [J.IsKInjective] :
    Nonempty ((derivedModuleDirectImage g).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) := by
  exact ⟨(derivedModuleDirectImage g).mapIso (asIso (DerivedCategory.Q.map s)) ≪≫
    (moduleDirectImage g).rightDerivedFunctorObjQIso J⟩

end AlgebraicGeometry.RingedSpace
