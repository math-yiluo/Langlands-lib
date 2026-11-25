/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctor

/-!
# Adic-lisse modules over completed constant coefficients

Source: Stacks Project, proetale.tex, Tag 09BT, Definition `definition-adic`, clause (3)
(auxiliary; not a blueprint node).

The index `n : ℕ` denotes exponent `n + 1`. All limits are genuine limits of sheaves.
Linearity over completed coefficients is expressed on the quotient projections, locally
lifting a scalar in a quotient to a section of the constant coefficient ring. This also
works over inverse-image coefficients without commuting inverse image with infinite limits.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The constant coefficient ring, with coefficients in the site universe.
Source: Tag 09BT (auxiliary; not a blueprint node). -/
abbrev adicLisseConstantRing (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A)

/-- Forget commutativity while retaining the actual constant coefficient sheaf.
Source: Tag 09BT (auxiliary; not a blueprint node). -/
abbrev adicLisseRing (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (adicLisseConstantRing X A)

/-- The constant-ring sheafification unit, used by module sheafification.
Source: Tag 09BT (auxiliary; not a blueprint node). -/
def adicLisseConstantUnit (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of A) ⟶ (adicLisseRing X A).obj :=
  Functor.whiskerRight (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- Forgetting commutativity leaves the underlying local injectivity condition unchanged.
Source: constant sheafification in Tag 09BT (auxiliary; not a blueprint node). -/
instance adicLisseConstantUnit_locallyInjective (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] : Presheaf.IsLocallyInjective (ProEt.topology X)
      (adicLisseConstantUnit X A) :=
  (Presheaf.isLocallyInjective_forget_iff (ProEt.topology X)
    (adicLisseConstantUnit X A)).mp
      (inferInstanceAs (Presheaf.IsLocallyInjective (ProEt.topology X)
        (Functor.whiskerRight (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))
          (CategoryTheory.forget CommRingCat.{u + 1}))))

/-- Forgetting commutativity leaves the underlying local surjectivity condition unchanged.
Source: constant sheafification in Tag 09BT (auxiliary; not a blueprint node). -/
instance adicLisseConstantUnit_locallySurjective (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] : Presheaf.IsLocallySurjective (ProEt.topology X)
      (adicLisseConstantUnit X A) :=
  (Presheaf.isLocallySurjective_iff_whisker_forget (ProEt.topology X)
    (adicLisseConstantUnit X A)).mpr
      (inferInstanceAs (Presheaf.IsLocallySurjective (ProEt.topology X)
        (Functor.whiskerRight (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))
          (CategoryTheory.forget CommRingCat.{u + 1}))))

/-- Pull the existing constant module presheaf on the one-object category back to the
actual small pro-etale site, then sheafify. This retains unequal site object/Hom universes.
Source: Tag 09BT (auxiliary; not a blueprint node). -/
def adicLisseConstantModules (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    ModuleCat.{u + 1} A ⥤ ringedSiteModules.{u + 1} (adicLisseRing X A) :=
  siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A)) ⋙
    PresheafOfModules.sheafification (adicLisseConstantUnit X A)

/-- Constant quotient ring sheaves with the actual quotient transition maps.
Source: Tag 09BT (auxiliary; not a blueprint node). -/
def adicLisseRingSystem (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n : ℕ ↦
    adicLisseConstantRing X (A ⧸ I ^ (n + 1))) (fun n : ℕ ↦
    (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1))))

/-- The completed coefficient ring is the inverse limit, computed sectionwise.
Source: Tag 09BT (auxiliary; not a blueprint node). -/
abbrev adicLisseCompletedRing (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) := limit (adicLisseRingSystem X I)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Forget commutativity for any coefficient sheaf and its maps.
Source: Tag 09BT (auxiliary; not a blueprint node). -/
abbrev adicLisseForget (X : Scheme.{u}) :=
  sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

end AlgebraicGeometry.Scheme
