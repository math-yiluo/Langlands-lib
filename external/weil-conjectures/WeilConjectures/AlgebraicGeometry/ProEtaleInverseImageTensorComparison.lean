/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullback
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence

/-!
# Normalized tensor comparison for pro-etale inverse image

Source: Stacks Project, Tags 03EK, 03EL and 09A5
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme SheafOfModules

namespace AlgebraicGeometry.ProEtaleTensorComparison

/-- The original small pro-etale ring sheaves, without changing either site universe.
Source: Stacks, Tag 09A5 (auxiliary; not a blueprint node). -/
abbrev Rings (X : Scheme.{u}) := Sheaf (ProEt.topology X) CommRingCat.{u + 1}

/-- The recorded category of modules over the underlying ring sheaf.
Source: Stacks, Section 03EK (auxiliary; not a blueprint node). -/
abbrev Modules {X : Scheme.{u}} (R : Rings X) :=
  ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The recorded inverse-image ring, computed by Kan extension and sheafification.
Source: Stacks, Tags 09A5 and 03D2
(auxiliary; not a blueprint node). -/
noncomputable abbrev inverseRing {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Rings Y) : Rings X :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R

/-- The recorded inverse image on module sheaves; no new module data are chosen.
Source: Stacks, Tag 03D2 (auxiliary; not a blueprint node). -/
noncomputable abbrev inverse {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Rings Y) :=
  proEtaleModuleInverseImage f R

/-- The actual adjunction-unit image of a module section. The small model is used only
inside the already recorded construction; evaluation returns to the original small site.
Source: Stacks, Tags 00VE and 03D2
(auxiliary; not a blueprint node). -/
noncomputable def inverseSection {X Y : Scheme.{u}} (f : X ⟶ Y) {R : Rings Y}
    (M : Modules R) (V : Y.ProEt) (s : M.val.obj (op V)) :
    ((inverse f R).obj M).val.obj (op ((proEtaleBaseChange f).obj V)) :=
  (((pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).unit.app
    ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)).val.app
        (op ((AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).obj V))) s

private theorem inverseSection_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Rings Y) (M : Modules R) (U : Y.ProEtᵒᵖ) (s : M.val.obj U) :
    ((AlgebraicGeometry.Scheme.canonicalAdjunction f R).unit.app M).val.app U s =
      inverseSection f (R := R) M U.unop s := by
  exact AlgebraicGeometry.Scheme.canonicalUnit_sections f R M U s

-- Use the canonical-unit API without unfolding the small-model module construction.
attribute [local irreducible] proEtaleModuleInverseImage inverseSection

/-- The underlying set sheaf of a commutative ring sheaf.
Source: Stacks, Tag 00YV (auxiliary; not a blueprint node). -/
noncomputable abbrev ringSets {X : Scheme.{u}} (R : Rings X) :=
  (sheafCompose (ProEt.topology X) (CategoryTheory.forget CommRingCat.{u + 1})).obj R

/-- The underlying set sheaf of a module sheaf, using the existing forgetful functors.
Source: Stacks, Tag 03D2 (auxiliary; not a blueprint node). -/
noncomputable abbrev moduleSets {X : Scheme.{u}} {R : Rings X} (M : Modules R) :=
  ((toSheaf _ ⋙ sheafCompose (ProEt.topology X)
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj M)

/-- The underlying-set identification of ring inverse image is uniquely unit-normalized.
Source: Stacks, Tag 00YV; the operation transport in clause 3
(auxiliary; not a blueprint node).
Proof: lift the finite-product-preserving set inverse image to commutative ring objects.
The original operation maps give the ring identities after applying this functor.
The lifted adjunction identifies the ring unit with the set unit. Uniqueness follows
by taking adjuncts: the displayed formula identifies the adjunct with the ring unit
on every object and every section. -/
theorem ringSetsIdentification_exists {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Rings Y) :
    ∃! e : (AlgebraicGeometry.ProEtale.setPullback f).obj (ringSets R) ≅
        ringSets (inverseRing f R),
      ∀ (V : Y.ProEt) (r : R.obj.obj (op V)),
        e.hom.hom.app (op ((proEtaleBaseChange f).obj V))
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
            (ringSets R)).hom.app (op V) r) =
        ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app (op V) r := by
  let : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  let : PreservesFilteredColimitsOfSize.{u, u + 1}
      (CategoryTheory.forget CommRingCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  let c := sheafPullbackForgetIso (ProEt.topology Y) (ProEt.topology X)
    (proEtaleBaseChange f) (CategoryTheory.forget CommRingCat.{u + 1})
  have hc := sheafPullbackForgetIso_unit (ProEt.topology Y) (ProEt.topology X)
    (proEtaleBaseChange f) (CategoryTheory.forget CommRingCat.{u + 1}) R
  have hp : ∀ (V : Y.ProEt) (r : R.obj.obj (op V)),
      (c.inv.app R).hom.app (op ((proEtaleBaseChange f).obj V))
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
          (ringSets R)).hom.app (op V) r) =
        ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app (op V) r := by
    intro V r
    have h := congrArg (fun z ↦ z.hom.app (op V) r) hc
    change (c.inv.app R).hom.app (op ((proEtaleBaseChange f).obj V)) _ = _
    change (c.hom.app R).hom.app (op ((proEtaleBaseChange f).obj V))
      (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app (op V) r) =
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
          (ringSets R)).hom.app (op V) r) at h
    rw [← h]
    exact congrArg (fun z ↦ z.hom.app (op ((proEtaleBaseChange f).obj V))
      (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app (op V) r))
        (c.hom_inv_id_app R)
  clear_value c
  refine ⟨(c.app R).symm, hp, ?_⟩
  intro e he
  apply Iso.ext
  apply ((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext V r
  exact (he V.unop r).trans (hp V.unop r).symm

/-- The determined underlying-set identification for inverse-image rings.
Source: Stacks, Tag 00YV (auxiliary; not a blueprint node). -/
noncomputable def ringSetsIdentification {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Rings Y) :
    (AlgebraicGeometry.ProEtale.setPullback f).obj (ringSets R) ≅
      ringSets (inverseRing f R) :=
  Classical.choose (ringSetsIdentification_exists f R)

/-- The underlying-set identification of module inverse image is uniquely unit-normalized.
Source: Stacks, Tag 03D2; the operation transport in clause 3
(auxiliary; not a blueprint node).
Proof: addition and the scalar action are transported through finite-product comparisons.
They define the same module inverse image as the recorded small-model construction.
Its adjunction identifies its unit with the set unit. Any second identification has the
same adjunct on every section, and hence is equal by the set-sheaf adjunction. -/
theorem moduleSetsIdentification_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} (M : Modules R) :
    ∃! e : (AlgebraicGeometry.ProEtale.setPullback f).obj (moduleSets M) ≅
        moduleSets ((inverse f R).obj M),
      ∀ (V : Y.ProEt) (s : M.val.obj (op V)),
        e.hom.hom.app (op ((proEtaleBaseChange f).obj V))
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
            (moduleSets M)).hom.app (op V) s) = inverseSection f M V s := by
  let adj := proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}
  let P := toSheaf ((sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let Q := toSheaf ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (inverseRing f R))
  let ai := AlgebraicGeometry.Scheme.canonicalAdjunction f R
  let α := (adj.homEquiv (P.obj M) (Q.obj ((inverse f R).obj M))).symm
    (P.map (ai.unit.app M))
  let : IsIso α := proEtaleModuleInverseImage_unitComparison_isIso f R ai M
  let : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  let : PreservesFilteredColimitsOfSize.{u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  let c := sheafPullbackForgetIso (ProEt.topology Y) (ProEt.topology X)
    (proEtaleBaseChange f) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let e := (c.app (P.obj M)).symm ≪≫
    (sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso
      (asIso α)
  have he : ∀ (V : Y.ProEt) (s : M.val.obj (op V)),
      e.hom.hom.app (op ((proEtaleBaseChange f).obj V))
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
          (moduleSets M)).hom.app (op V) s) = inverseSection f M V s := by
    intro V s
    have hc := congrArg (fun z ↦ z.hom.app (op V) s)
      (sheafPullbackForgetIso_unit (ProEt.topology Y) (ProEt.topology X)
        (proEtaleBaseChange f) (CategoryTheory.forget AddCommGrpCat.{u + 1}) (P.obj M))
    have hα := (adj.homEquiv (P.obj M) (Q.obj ((inverse f R).obj M))).apply_symm_apply
      (P.map (ai.unit.app M))
    rw [Adjunction.homEquiv_unit] at hα
    have hα' := congrArg (fun z ↦ z.hom.app (op V) s) hα
    change (c.hom.app (P.obj M)).hom.app (op ((proEtaleBaseChange f).obj V))
      ((adj.unit.app (P.obj M)).hom.app (op V) s) =
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
          (moduleSets M)).hom.app (op V) s) at hc
    change α.hom.app (op ((proEtaleBaseChange f).obj V))
      ((c.inv.app (P.obj M)).hom.app (op ((proEtaleBaseChange f).obj V)) _) = _
    rw [← hc]
    have hi := congrArg (fun z ↦ z.hom.app (op ((proEtaleBaseChange f).obj V))
      ((adj.unit.app (P.obj M)).hom.app (op V) s)) (c.hom_inv_id_app (P.obj M))
    change (c.inv.app (P.obj M)).hom.app _
      ((c.hom.app (P.obj M)).hom.app _ _) = _ at hi
    rw [hi]
    exact hα'.trans (inverseSection_unit f R M (op V) s)
  clear_value e
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply ((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext V s
  exact (he' V.unop s).trans (he V.unop s).symm

/-- The determined underlying-set identification for inverse-image modules.
Source: Stacks, Tag 03D2 (auxiliary; not a blueprint node). -/
noncomputable def moduleSetsIdentification {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} (M : Modules R) :
    (AlgebraicGeometry.ProEtale.setPullback f).obj (moduleSets M) ≅
      moduleSets ((inverse f R).obj M) :=
  Classical.choose (moduleSetsIdentification_exists f M)

section TensorPairing

universe uC vC uD vD r

end TensorPairing

section IdentityScalars
universe c h r
variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  (A : Sheaf J CommRingCat.{r})
  (P : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))

open scoped ChangeOfRings

end IdentityScalars

-- Keep Kan-extension data abstract after the unit identifications.
attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
  AlgebraicGeometry.ProEtale.setPullback
  AlgebraicGeometry.ProEtale.setPullbackAdjunction
  AlgebraicGeometry.ProEtale.setPullbackComp

/-- Forget a module morphism to its actual underlying sheaf map.
Source: Stacks, Tag 03D2 (auxiliary; not a blueprint node). -/
noncomputable abbrev moduleMapSets {X : Scheme.{u}} {R : Rings X}
    {M N : Modules R} (a : M ⟶ N) :=
  (toSheaf _ ⋙ sheafCompose (ProEt.topology X)
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).map a

section AlgebraicLift
universe v w

end AlgebraicLift

-- Use normalization and adjunction equations without expanding their constructions.
attribute [local irreducible] monoidalCategory tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction

section TensorPresentation
universe c h r
variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  (A : Sheaf J CommRingCat.{r})
  [(J.W.inverseImage (PresheafOfModules.toPresheaf.{r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)).IsMonoidal]
  (P Q : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))

end TensorPresentation

section ScalarFunctor
universe c h r
variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]

end ScalarFunctor

end AlgebraicGeometry.ProEtaleTensorComparison
