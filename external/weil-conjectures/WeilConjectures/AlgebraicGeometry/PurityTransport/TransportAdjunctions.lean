/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Smooth purity on the condensed finite-Tor categories
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport

variable (ell : ℕ) [Fact ell.Prime]

/-- The object property defining Dctf: bounded constructible with finite Tor amplitude. -/
abbrev property (c : Coefficient ell) (X : Scheme.{u}) :
    ObjectProperty (c.derived ell X) :=
  constantModelBoundedConstructible (c.obj ell) X ⊓
    (fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K)

/-- The localizing closure of the constructible objects on the pro-étale site of `X`. -/
abbrev localizing (c : Coefficient ell) (X : Scheme.{u}) :=
  localizingClosureProEtale (c.obj ell) X

/-- The canonical full inclusion into the localizing constructible closure. -/
def inclusion (c : Coefficient ell) (X : Scheme.{u}) :
    c.ctf ell X ⥤ (localizing ell c X).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _P _hP hS ↦ hS K hK)

/-- The compact-support functor `Rp_* j_!` restricted to Dctf. -/
def support (c : Coefficient ell) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (compactification : Compactification f)
    (preserves : ∀ K, property ell c X K → property ell c Y
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) compactification).obj K)) :
    c.ctf ell X ⥤ c.ctf ell Y :=
  (property ell c Y).lift
    ((property ell c X).ι ⋙
      CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) compactification)
    (fun K ↦ preserves K.obj K.property)

/-- Restrict the literal twisted and shifted inverse image to Dctf. -/
def source (c : Coefficient ell) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (preserves : ∀ K, property ell c Y K → property ell c X
      ((c.smoothSource ell f d).obj K)) : c.ctf ell Y ⥤ c.ctf ell X :=
  (property ell c X).lift ((property ell c Y).ι ⋙ c.smoothSource ell f d)
    (fun K ↦ preserves K.obj K.property)

/-- The exceptional inverse image: the restriction of a localizing right adjoint to Dctf,
through the canonical full inclusion. -/
def exceptional (c : Coefficient ell) {X Y : Scheme.{u}}
    (G : (localizing ell c Y).FullSubcategory ⥤ (localizing ell c X).FullSubcategory)
    (preserves : ∀ K : c.ctf ell Y,
      property ell c X (G.obj ((inclusion ell c Y).obj K)).obj) :
    c.ctf ell Y ⥤ c.ctf ell X :=
  (property ell c X).lift
    (inclusion ell c Y ⋙ G ⋙ (localizing ell c X).ι) preserves

/-- The counit equation selecting gamma, in Lean's diagrammatic order. -/
def CounitCompatible {A B : Type (u + 2)} [Category A] [Category B]
    {F : A ⥤ B} {J G : B ⥤ A} (a : F ⊣ J) (b : F ⊣ G)
    (gamma : J ≅ G) : Prop :=
  ∀ K : B, F.map (gamma.hom.app K) ≫ b.counit.app K = a.counit.app K

end AlgebraicGeometry.ProEtale.PurityTransport
