/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Functor.OfSequence
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryRestrictionPullbackSquare

/-!
# Finite open exchange and coefficient restriction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/
lem-cbc-completed-extension-zero-comparison.proof.md, finite exchange before derived limits;
Stacks Project, Tag 03DI, direct-sum adjunction construction
(blueprint: lem-cbc-finite-open-exchange-scalars).

We use the recorded constant-ring module coordinates and the recorded inverse open-unit
transpose. All complex functors below are termwise, before derived localization.
-/

@[expose] public noncomputable section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars

attribute [local irreducible] Functor.leftAdjoint

variable {B C : Type (u + 1)} [CommRing B] [CommRing C]

/-- The map of constant coefficient sheaves induced by a ring homomorphism.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev coefficientMap (a : B →+* C) (X : Scheme.{u}) :
    coefficients B X ⟶ coefficients C X :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom a)

/-- The underlying ring sheaf of the recorded commutative constant coefficients.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev ringCoefficients (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients A X)

/-- The same coefficient homomorphism after forgetting commutativity.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev ringCoefficientMap (a : B →+* C) (X : Scheme.{u}) :
    ringCoefficients B X ⟶ ringCoefficients C X :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (coefficientMap a X)

/-- The recorded restriction of scalars, leaving the abelian sheaf unchanged.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev res (a : B →+* C) (X : Scheme.{u}) : Modules C X ⥤ Modules B X :=
  Scheme.proEtaleRingRestrictScalars (coefficientMap a X)

set_option backward.isDefEq.respectTransparency false in
private theorem scalarUnit_naturality (a : B →+* C) (X : Scheme.{u})
    (V : X.ProEtᵒᵖ) (b : B) :
    ((ringCoefficientMap a X).hom.app V) ((scalarUnit B X).app V b) =
      (scalarUnit C X).app V (a b) := by
  have h := congr_app ((toSheafification (Scheme.ProEt.topology X)
    CommRingCat.{u + 1}).naturality
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom a))) V
  exact (ConcreteCategory.congr_hom h b).symm

set_option backward.isDefEq.respectTransparency false in
-- Change of constant-ring coordinates, with identity underlying section maps.
private def resFixed (a : B →+* C) (X : Scheme.{u}) :
    res a X ⋙ fixedRestriction B X ≅
      fixedRestriction C X ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology X) a :=
  ringUnitLinearizeIso B (Scheme.ProEt.topology X) _ (scalarUnit B X)
    C a (res a X) (fixedRestriction C X) (Iso.refl _) (by
      intro M V b m
      change ((ringCoefficientMap a X).hom.app V) ((scalarUnit B X).app V b) •
          (show M.val.obj V from m) =
        (scalarUnit C X).app V (a b) • (show M.val.obj V from m)
      rw [scalarUnit_naturality])

/-- The constant-preserving coefficient maps commute with a coefficient homomorphism.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: transpose under the ring-sheaf adjunction. Both maps send each constant b to
the constant section a(b). The constant-presheaf sheafification property gives equality. -/
theorem coefficientSquare (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (constantRingIso B f).hom ≫ coefficientMap a Y =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (coefficientMap a X) ≫
        (constantRingIso C f).hom := by
  exact (Scheme.proEtaleConstantInverseImageMap_naturality f (CommRingCat.ofHom a)).symm

/-- Canonical pullback/scalar identification, the mate of identity on direct-image sections.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def pullRes (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    res a X ⋙ modulePullback B f ≅ modulePullback C f ⋙ res a Y :=
  @asIso _ _ _ _ (Scheme.proEtaleRingRestrictionPullbackInv f
    (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
    (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
    (coefficientSquare a f))
    (Scheme.proEtaleRingRestrictionPullbackInv_isIso f
      (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
      (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
      (coefficientSquare a f))

/-- Canonical direct-image/scalar identification, identity on every section.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def pushRes (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    moduleDirectImage C f ⋙ res a X ≅ res a Y ⋙ moduleDirectImage B f :=
  Scheme.proEtaleRingRestrictionDirectImage f
    (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
    (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
    (coefficientSquare a f)

set_option backward.isDefEq.respectTransparency false in
private theorem pushRes_apply {B C : Type (u + 1)} [CommRing B] [CommRing C]
    (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) (N : Modules C Y)
    (W : X.ProEtᵒᵖ) (m : N.val.obj ((Scheme.proEtaleBaseChange f).op.obj W)) :
    ((pushRes a f).hom.app N).val.app W m = m :=
  (Classical.choose_spec (Scheme.proEtaleRingRestrictionDirectImage_existsUnique f
    (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
    (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
    (coefficientSquare a f))).1 N W m

set_option backward.isDefEq.respectTransparency false in
private theorem pullRes_mate (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (mateEquiv (Scheme.proEtaleRingModuleAdjunction f
        (coefficients C X) (coefficients C Y) (constantRingIso C f))
      (Scheme.proEtaleRingModuleAdjunction f
        (coefficients B X) (coefficients B Y) (constantRingIso B f))
      (TwoSquare.mk _ _ _ _ (pullRes a f).hom)) = (pushRes a f).hom := by
  change (mateEquiv (Scheme.proEtaleRingModuleAdjunction f
      (coefficients C X) (coefficients C Y) (constantRingIso C f))
    (Scheme.proEtaleRingModuleAdjunction f
      (coefficients B X) (coefficients B Y) (constantRingIso B f)))
      (TwoSquare.mk _ _ _ _ (pullRes a f).hom) =
    TwoSquare.mk _ _ _ _ (pushRes a f).hom
  rw [← Equiv.eq_symm_apply]
  refine NatTrans.ext (funext fun M ↦ ?_)
  simp only [mateEquiv_symm_apply, pullRes, asIso_hom,
    Scheme.proEtaleRingRestrictionPullbackInv,
    Scheme.proEtaleRingRestrictionPullbackApp, pushRes, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_map, Category.id_comp]
  simp only [TwoSquare.mk, CategoryTheory.Functor.map_id]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp]
  exact congrArg (fun k ↦ _ ≫ _ ≫ k) (Category.comp_id _).symm

section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] fixedRestriction_equivalence

private def fixedPull {A : Type (u + 1)} [CommRing A]
    {Y X : Scheme.{u}} (f : Y ⟶ X) :
    TwoSquare (fixedRestriction A X) (modulePullback A f)
      (upperStar (ModuleCat.{u + 1} A) f) (fixedRestriction A Y) :=
  (mateEquiv (Scheme.proEtaleRingModuleAdjunction f
    (coefficients A X) (coefficients A Y) (constantRingIso A f))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)).symm
    (TwoSquare.mk _ _ _ _ (fixedDirect A f).hom)

private instance fixedPull_isIso {A : Type (u + 1)} [CommRing A]
    {Y X : Scheme.{u}} (f : Y ⟶ X) : IsIso (fixedPull (A := A) f) :=
  inverseMate_isIso_of_equivalences _ _ _

-- The pullback square can be checked on the identity-on-sections direct-image mates.
private theorem resPull_fixed (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    TwoSquare.hComp (TwoSquare.mk _ _ _ _ (pullRes a f).hom)
        (fixedPull (A := B) f) =
      ((TwoSquare.hComp (fixedPull (A := C) f)
        (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso a f).hom)).whiskerTop
          (resFixed a X).hom).whiskerBottom (resFixed a Y).inv := by
  let adjC : modulePullback C f ⊣ moduleDirectImage C f :=
    Scheme.proEtaleRingModuleAdjunction f
    (coefficients C X) (coefficients C Y) (constantRingIso C f)
  let adjB : modulePullback B f ⊣ moduleDirectImage B f :=
    Scheme.proEtaleRingModuleAdjunction f
    (coefficients B X) (coefficients B Y) (constantRingIso B f)
  let ordC := upperStarLowerStarAdjunction (ModuleCat.{u + 1} C) f
  let ordB := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  apply (mateEquiv adjC ordB).injective
  rw [mateEquiv_vcomp adjC adjB ordB, mateEquiv_whiskerTop_whiskerBottom adjC ordB,
    mateEquiv_vcomp adjC ordC ordB]
  have hp := pullRes_mate a f
  change (mateEquiv adjC adjB (TwoSquare.mk _ _ _ _ (pullRes a f).hom)) =
    (pushRes a f).hom at hp
  have hp' : mateEquiv adjC adjB (TwoSquare.mk _ _ _ _ (pullRes a f).hom) =
      TwoSquare.mk _ _ _ _ (pushRes a f).hom := by
    exact hp
  rw [hp', show mateEquiv adjB ordB (fixedPull (A := B) f) =
      TwoSquare.mk _ _ _ _ (fixedDirect B f).hom from Equiv.apply_symm_apply _ _,
    show mateEquiv adjC ordC (fixedPull (A := C) f) =
      TwoSquare.mk _ _ _ _ (fixedDirect C f).hom from Equiv.apply_symm_apply _ _]
  have hs := scalar_direct_mate a f
  change (mateEquiv ordC ordB
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso a f).hom)) = 𝟙 _ at hs
  rw [show mateEquiv ordC ordB
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso a f).hom) =
      TwoSquare.mk _ _ _ _ (𝟙 _) from hs]
  apply (cancel_mono (Functor.whiskerRight (resFixed a Y).hom
    (lowerStar (ModuleCat.{u + 1} B) f))).mp
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.mk,
    Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id,
    Functor.whiskerRight_id', Category.comp_id]
  ext M V m
  change ((pushRes a f).hom.app M).val.app V m = m
  exact (Classical.choose_spec (Scheme.proEtaleRingRestrictionDirectImage_existsUnique
    f (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
    (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
    (coefficientSquare a f))).1 M V m

end

section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private abbrev pullAdj (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (f : Y ⟶ X) : modulePullback A f ⊣ moduleDirectImage A f :=
  Scheme.proEtaleRingModuleAdjunction f
    (coefficients A X) (coefficients A Y) (constantRingIso A f)

attribute [local irreducible] Scheme.proEtaleRingModulePullback

-- Compare compositors on direct images, where their section formulas are explicit.
private theorem pullRes_comp (a : B →+* C) {V W Z : Scheme.{u}}
    (f : V ⟶ W) (g : W ⟶ Z) (M : Modules C Z) :
    (moduleGComp B f g).hom.app ((res a Z).obj M) ≫
        (modulePullback B f).map ((pullRes a g).hom.app M) ≫
        (pullRes a f).hom.app ((modulePullback C g).obj M) =
      (pullRes a (f ≫ g)).hom.app M ≫
        (res a V).map ((moduleGComp C f g).hom.app M) := by
  let q := (TwoSquare.mk _ _ _ _ (pullRes a g).hom).vComp
    (TwoSquare.mk _ _ _ _ (pullRes a f).hom)
  have hp {Y X : Scheme.{u}} (k : Y ⟶ X) :
      mateEquiv (pullAdj C k) (pullAdj B k)
          (TwoSquare.mk _ _ _ _ (pullRes a k).hom) =
        TwoSquare.mk _ _ _ _ (pushRes a k).hom :=
    (pullRes_mate a k)
  have hc : q.whiskerRight (moduleGComp B f g).hom =
      (TwoSquare.mk _ _ _ _ (pullRes a (f ≫ g)).hom).whiskerLeft
        (moduleGComp C f g).hom := by
    apply mateSquare ((pullAdj C g).comp (pullAdj C f)) (pullAdj C (f ≫ g))
      ((pullAdj B g).comp (pullAdj B f)) (pullAdj B (f ≫ g))
    dsimp only [q]
    rw [mateEquiv_hcomp, hp, hp, hp]
    have hG (A : Type (u + 1)) [CommRing A] :
        conjugateEquiv ((pullAdj A g).comp (pullAdj A f)) (pullAdj A (f ≫ g))
            (moduleGComp A f g).hom = (moduleRComp A f g).hom :=
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
    rw [hG B, hG C]
    refine NatTrans.ext (funext fun N ↦ ?_)
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro Y
    ext n
    simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, SheafOfModules.comp_val, PresheafOfModules.comp_app]
    simp only [ModuleCat.comp_apply]
    erw [pushRes_apply a g ((moduleDirectImage C f).obj N) Y n]
    change ((moduleRComp B f g).hom.app ((res a V).obj N)).val.app Y
        (((pushRes a f).hom.app N).val.app ((Scheme.proEtaleBaseChange g).op.obj Y) n) =
      ((pushRes a (f ≫ g)).hom.app N).val.app Y
        (((moduleRComp C f g).hom.app N).val.app Y n)
    rw [pushRes_apply, pushRes_apply]
    exact ((Classical.choose_spec (moduleRComp_existsUnique B f g)).1
      ((res a V).obj N) Y.unop n).trans
        ((Classical.choose_spec (moduleRComp_existsUnique C f g)).1 N Y.unop n).symm
  have hm := congrArg (fun z ↦ z.app M) hc
  simpa only [q, TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] using hm

end

/-- The scalar comparison for extension is the mate of the inverse pullback comparison.
Source: Stacks Tag 03DI, direct-sum adjunction construction
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def openResMap (a : B →+* C) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    res a U ⋙ moduleJ B j ⟶ moduleJ C j ⋙ res a X :=
  (mateEquiv (moduleJAdj C j) (moduleJAdj B j)).symm (pullRes a j).inv

section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The normalized open scalar mate is invertible, including for the empty open.
Source: Stacks Tag 03DI (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: transport the pullback comparison through the equivalence between constant-ring
module sheaves and sheaves of modules over the coefficient ring. Its direct-image mate
is identity on sections, so it agrees with the ordinary scalar comparison. The ordinary
open mate is invertible. Inverse-mate pasting transports this fact back through the
coordinate equivalences and identifies the resulting mate with openResMap. -/
theorem openResMap_isIso [Finite B] [Finite C] (a : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : IsIso (openResMap a j) := by
  -- Paste through fixed coefficient coordinates, then take open inverse mates.
  let α := TwoSquare.mk _ _ _ _ (pullRes a j).hom
  let β := fixedPull (A := B) j
  let γ := fixedPull (A := C) j
  let δ := TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso a j).hom
  have : IsIso α := by dsimp only [α, TwoSquare.mk]; infer_instance
  have : IsIso β := fixedPull_isIso j
  have : IsIso γ := fixedPull_isIso j
  have : IsIso δ := by dsimp only [δ, TwoSquare.mk]; infer_instance
  have : IsIso (TwoSquare.hComp γ δ) := by
    dsimp only [TwoSquare.hComp, TwoSquare.mk]
    infer_instance
  let oa := moduleJAdj C j
  let ob := moduleJAdj B j
  let oc := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let od := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} C) j
  have := fixedRestriction_equivalence B U
  have := fixedRestriction_equivalence B X
  have := fixedRestriction_equivalence C U
  have := fixedRestriction_equivalence C X
  have : IsIso ((mateEquiv oa od).symm
      (TwoSquare.mk _ _ _ _ (CategoryTheory.inv γ))) :=
    inverseMate_isIso_of_equivalences oa od _
  have : IsIso ((mateEquiv od oc).symm
      (TwoSquare.mk _ _ _ _ (CategoryTheory.inv δ))) := by
    simp only [δ, TwoSquare.mk, IsIso.Iso.inv_hom]
    rw [← scalarPullbackModel_eq B j C a]
    exact scalarOpenModel_isIso B j C a
  have hw : IsIso ((mateEquiv oa oc).symm
      (TwoSquare.mk _ _ _ _
        (CategoryTheory.inv (TwoSquare.hComp γ δ)))) := by
    rw [inv_hComp, inverseMate_vComp oa od oc]
    dsimp only [TwoSquare.hComp, TwoSquare.mk]
    infer_instance
  let w := TwoSquare.mk _ _ _ _ (CategoryTheory.inv (TwoSquare.hComp γ δ))
  let t := TwoSquare.hComp α β
  have : IsIso t := by
    dsimp only [t, TwoSquare.hComp, TwoSquare.mk]
    infer_instance
  let z := Functor.isoWhiskerRight (resFixed a X) _ ≪≫
    asIso (TwoSquare.hComp γ δ) ≪≫
    Functor.isoWhiskerLeft (modulePullback C j) (resFixed a U).symm
  have ht : CategoryTheory.inv t =
      ((w.whiskerRight (resFixed a U).hom).whiskerLeft (resFixed a X).inv) := by
    have hz : t = z.hom := (resPull_fixed a j)
    calc
      CategoryTheory.inv t = CategoryTheory.inv z.hom :=
        IsIso.inv_eq_inv.mpr hz
      _ = _ := by
        simp only [IsIso.Iso.inv_hom, z, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
          Functor.isoWhiskerRight_inv, Iso.symm_inv, asIso_inv, w,
          TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.mk, Category.assoc]
  have hi : IsIso ((mateEquiv oa oc).symm
      (TwoSquare.mk _ _ _ _ (CategoryTheory.inv t))) := by
    rw [ht]
    exact inverseMate_iso_edges oa oc (resFixed a U) (resFixed a X).symm w
  let x := (mateEquiv oa ob).symm (TwoSquare.mk _ _ _ _ (pullRes a j).inv)
  let y := (mateEquiv ob oc).symm
    (TwoSquare.mk _ _ _ _ (CategoryTheory.inv β))
  have : IsIso y := inverseMate_isIso_of_equivalences ob oc _
  have he : (mateEquiv oa oc).symm
      (TwoSquare.mk _ _ _ _ (CategoryTheory.inv t)) = TwoSquare.hComp x y := by
    dsimp only [t]
    rw [inv_hComp]
    exact inverseMate_vComp oa ob oc _ _
  rw [he] at hi
  exact isIso_of_hComp x y

end

/-- The canonical scalar-restriction identification for open extension.
Source: Stacks Tag 03DI (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def openRes [Finite B] [Finite C] (a : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    res a U ⋙ moduleJ B j ≅ moduleJ C j ⋙ res a X :=
  @asIso _ _ _ _ (openResMap a j) (openResMap_isIso a j)

/-- The recorded canonical open exchange on sheaves, before degreewise extension.
Its inverse is exactly singleBetaInv, the pulled-back open-unit transpose.
Source: Stacks Tag 09AE (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def beta (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) :
    moduleJ A j ⋙ modulePullback A g ≅ modulePullback A gU ⋙ moduleJ A j' :=
  (@asIso _ _ _ _ (singleBetaInv A gU j' j g h)
    (singleBetaInv_isIso A gU j' j g h hsq)).symm

/-- The scalar identification on the source of open exchange.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def sourceRes [Finite B] [Finite C] (a : B →+* C)
    {U X' X : Scheme.{u}} (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] :
    res a U ⋙ (moduleJ B j ⋙ modulePullback B g) ≅
      (moduleJ C j ⋙ modulePullback C g) ⋙ res a X' :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (openRes a j) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (pullRes a g) ≪≫
    (Functor.associator _ _ _).symm

/-- The scalar identification on the target of open exchange.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def targetRes [Finite B] [Finite C] (a : B →+* C)
    {U' U X' : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X') [IsOpenImmersion j'] :
    res a U ⋙ (modulePullback B gU ⋙ moduleJ B j') ≅
      (modulePullback C gU ⋙ moduleJ C j') ⋙ res a X' :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (pullRes a gU) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (openRes a j') ≪≫
    (Functor.associator _ _ _).symm

/-- Scalar restriction on unbounded complexes, with all terms and differentials retained.
Source: blueprint finite exchange paragraph
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev resC (a : B →+* C) (X : Scheme.{u}) :
    CochainComplex (Modules C X) ℤ ⥤ CochainComplex (Modules B X) ℤ :=
  (res a X).mapHomologicalComplex (.up ℤ)

/-- The complex-level exchange, from the recorded sheaf exchange term by term.
Source: Stacks Tag 09AE (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def betaC (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) :
    (moduleJ A j ⋙ modulePullback A g).mapHomologicalComplex (.up ℤ) ≅
      (modulePullback A gU ⋙ moduleJ A j').mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (beta A gU j' j g h hsq) (.up ℤ)

/-- The source identification on complexes.
Source: blueprint finite exchange paragraph
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def sourceResC [Finite B] [Finite C] (a : B →+* C)
    {U X' X : Scheme.{u}} (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] :
    (res a U ⋙ (moduleJ B j ⋙ modulePullback B g)).mapHomologicalComplex (.up ℤ) ≅
      ((moduleJ C j ⋙ modulePullback C g) ⋙ res a X').mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (sourceRes a j g) (.up ℤ)

/-- The target identification on complexes.
Source: blueprint finite exchange paragraph
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def targetResC [Finite B] [Finite C] (a : B →+* C)
    {U' U X' : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X') [IsOpenImmersion j'] :
    (res a U ⋙ (modulePullback B gU ⋙ moduleJ B j')).mapHomologicalComplex (.up ℤ) ≅
      ((modulePullback C gU ⋙ moduleJ C j') ⋙ res a X').mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (targetRes a gU j') (.up ℤ)

/-- Scalar restriction preserves the inverse-image/direct-image unit and counit.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: direct image comparison is the identity on sections. The pullback comparison
was defined as its mate using the normalized module adjunctions. The mate unit and
counit equations give the two equalities; all constructions are applied degreewise. -/
theorem pull_unit_counit [Finite B] [Finite C] (a : B →+* C)
    {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (∀ F : Modules C X,
      (res a X).map ((Scheme.proEtaleRingModuleAdjunction f
          (coefficients C X) (coefficients C Y) (constantRingIso C f)).unit.app F) ≫
          (pushRes a f).hom.app ((modulePullback C f).obj F) =
        (Scheme.proEtaleRingModuleAdjunction f
          (coefficients B X) (coefficients B Y) (constantRingIso B f)).unit.app
            ((res a X).obj F) ≫
          (moduleDirectImage B f).map ((pullRes a f).hom.app F)) ∧
    (∀ N : Modules C Y,
      (pullRes a f).hom.app ((moduleDirectImage C f).obj N) ≫
          (res a Y).map ((Scheme.proEtaleRingModuleAdjunction f
            (coefficients C X) (coefficients C Y) (constantRingIso C f)).counit.app N) =
        (modulePullback B f).map ((pushRes a f).hom.app N) ≫
          (Scheme.proEtaleRingModuleAdjunction f
            (coefficients B X) (coefficients B Y) (constantRingIso B f)).counit.app
              ((res a Y).obj N)) := by
  let adjC := Scheme.proEtaleRingModuleAdjunction f
    (coefficients C X) (coefficients C Y) (constantRingIso C f)
  let adjB := Scheme.proEtaleRingModuleAdjunction f
    (coefficients B X) (coefficients B Y) (constantRingIso B f)
  have hm := pullRes_mate a f
  constructor
  · intro F
    have hu := unit_mateEquiv adjC adjB (TwoSquare.mk _ _ _ _ (pullRes a f).hom) F
    change (res a X).map (adjC.unit.app F) ≫
      ((mateEquiv adjC adjB (TwoSquare.mk _ _ _ _ (pullRes a f).hom))).app _ =
        adjB.unit.app _ ≫ (moduleDirectImage B f).map ((pullRes a f).hom.app F) at hu
    rw [hm] at hu
    exact hu
  · intro N
    have hc := mateEquiv_counit adjC adjB
      (TwoSquare.mk _ _ _ _ (pullRes a f).hom) N
    change (modulePullback B f).map
      ((mateEquiv adjC adjB (TwoSquare.mk _ _ _ _ (pullRes a f).hom)).app N) ≫
        adjB.counit.app _ = (pullRes a f).hom.app _ ≫
          (res a Y).map (adjC.counit.app N) at hc
    rw [hm] at hc
    exact hc.symm

/-- Restriction along the identity has its unique identity-on-sections identification.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: identity scalar restriction leaves the action unchanged. Identity section maps
are linear and natural, and their inverses are identical. Sections determine uniqueness. -/
theorem resId_existsUnique (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    ∃! e : res (RingHom.id A) X ≅ 𝟭 (Modules A X),
      ∀ (M : Modules A X) (W : X.ProEtᵒᵖ) (m : M.val.obj W),
        (e.hom.app M).val.app W m = m := by
  have hid : ringCoefficientMap (RingHom.id A) X = 𝟙 _ := by
    change (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (𝟙 _)) = _
    exact (congrArg (fun k ↦ (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map k)
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map_id
        (CommRingCat.of A))).trans
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_id _)
  let e : res (RingHom.id A) X ≅ 𝟭 (Modules A X) :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun W ↦
        ModuleCat.restrictScalarsId'App _
          (congrArg (fun k ↦ (k.hom.app W).hom) hid) (M.val.obj W)) (by
        intro W W' f
        ext m
        rfl))) (by
      intro M N f
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro W
      ext m
      rfl)
  refine ⟨e, fun _ _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  exact he' M W m

/-- The identity-on-sections identification for identity restriction.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def resId (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    res (RingHom.id A) X ≅ 𝟭 (Modules A X) :=
  Classical.choose (resId_existsUnique A X)

/-- Compatible ambient coefficient actions give a unique identity-on-sections comparison.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the equation on ring maps says the two restricted actions agree. Identity on
every section is therefore linear, natural, and its own inverse. Sectionwise faithfulness
makes the resulting natural isomorphism unique. -/
theorem ambientRes_existsUnique (a : B →+* C) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    (rB : R ⟶ ringCoefficients B X) (rC : R ⟶ ringCoefficients C X)
    (hr : rB ≫ ringCoefficientMap a X = rC) :
    ∃! e : res a X ⋙ SheafOfModules.restrictScalars.{u + 1} rB ≅
        SheafOfModules.restrictScalars.{u + 1} rC,
      ∀ (M : Modules C X) (W : X.ProEtᵒᵖ) (m : M.val.obj W),
        (e.hom.app M).val.app W m = m := by
  let e : res a X ⋙ SheafOfModules.restrictScalars.{u + 1} rB ≅
      SheafOfModules.restrictScalars.{u + 1} rC :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun W ↦
        (ModuleCat.restrictScalarsComp'App (rB.hom.app W).hom
          ((ringCoefficientMap a X).hom.app W).hom (rC.hom.app W).hom
          (congrArg (fun k ↦ (k.hom.app W).hom) hr.symm) (M.val.obj W)).symm) (by
        intro W W' f
        ext m
        rfl))) (by
      intro M N f
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro W
      ext m
      rfl)
  refine ⟨e, fun _ _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  exact he' M W m

/-- The fixed comparison for restriction to compatible ambient actions.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def ambientRes (a : B →+* C) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    (rB : R ⟶ ringCoefficients B X) (rC : R ⟶ ringCoefficients C X)
    (hr : rB ≫ ringCoefficientMap a X = rC) :
    res a X ⋙ SheafOfModules.restrictScalars.{u + 1} rB ≅
      SheafOfModules.restrictScalars.{u + 1} rC :=
  Classical.choose (ambientRes_existsUnique a X R rB rC hr)

/-- Constant coefficient maps respect composition.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: this is functoriality of constant-sheaf sheafification on ring maps. -/
theorem coefficientMap_comp {D : Type (u + 1)} [CommRing D]
    (a : B →+* C) (b : C →+* D) (X : Scheme.{u}) :
    ringCoefficientMap a X ≫ ringCoefficientMap b X = ringCoefficientMap (b.comp a) X := by
  change (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map _ ≫
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map _ = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The identity-on-sections comparison between successive and composite restriction.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def resComp {D : Type (u + 1)} [CommRing D] (a : B →+* C) (b : C →+* D)
    (X : Scheme.{u}) : res b X ⋙ res a X ≅ res (b.comp a) X :=
  ambientRes b X (ringCoefficients B X) (ringCoefficientMap a X)
    (ringCoefficientMap (b.comp a) X)
    (coefficientMap_comp a b X)

section

set_option backward.isDefEq.respectTransparency false

private theorem resId_apply (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M : Modules A X) (W : X.ProEtᵒᵖ) (m : M.val.obj W) :
    ((resId A X).hom.app M).val.app W m = m :=
  (Classical.choose_spec (resId_existsUnique A X)).1 M W m

private theorem push_identity (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (f : Y ⟶ X) (N : Modules A Y) :
    (pushRes (RingHom.id A) f).hom.app N ≫
        (moduleDirectImage A f).map ((resId A Y).hom.app N) =
      (resId A X).hom.app ((moduleDirectImage A f).obj N) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  change ((resId A Y).hom.app N).val.app ((Scheme.proEtaleBaseChange f).op.obj W)
    (((pushRes (RingHom.id A) f).hom.app N).val.app W m) = _
  rw [pushRes_apply, resId_apply]
  exact (resId_apply A X ((moduleDirectImage A f).obj N) W m).symm

private theorem left_square_identity
    {D E : Type*} [Category D] [Category E]
    {L : D ⥤ E} {R : E ⥤ D} (adj : L ⊣ R)
    {G : D ⥤ D} {H : E ⥤ E} (eG : G ⟶ 𝟭 D) (eH : H ⟶ 𝟭 E)
    (p : G ⋙ L ⟶ L ⋙ H) (d : R ⋙ G ⟶ H ⋙ R)
    (hu : ∀ M, G.map (adj.unit.app M) ≫ d.app (L.obj M) =
      adj.unit.app (G.obj M) ≫ R.map (p.app M))
    (hd : ∀ N, d.app N ≫ R.map (eH.app N) = eG.app (R.obj N)) (M : D) :
    p.app M ≫ eH.app (L.obj M) = L.map (eG.app M) := by
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, ← hu, Category.assoc, hd]
  exact (eG.naturality (adj.unit.app M)).trans (adj.unit.naturality (eG.app M))

private theorem pull_identity_aux (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y X : Scheme.{u}} (f : Y ⟶ X) (M : Modules A X) :
    (pullRes (RingHom.id A) f).hom.app M ≫
        (resId A Y).hom.app ((modulePullback A f).obj M) =
      (modulePullback A f).map ((resId A X).hom.app M) := by
  exact left_square_identity (Scheme.proEtaleRingModuleAdjunction f
    (coefficients A X) (coefficients A Y) (constantRingIso A f))
    (resId A X).hom (resId A Y).hom (pullRes (RingHom.id A) f).hom
    (pushRes (RingHom.id A) f).hom
    (pull_unit_counit (RingHom.id A) f).1 (push_identity A f) M

/-- The canonical inverse-image and extension scalar identifications preserve identities.
Source: Stacks Tags 03D2 and 03DI
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the identity-on-sections direct-image comparison is the identity after resId.
Uniqueness of the unit-preserving mate gives the pullback equality. Transposing that
equality under the two open adjunctions gives the extension equality. -/
theorem scalar_identity (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ M : Modules A X,
      (pullRes (RingHom.id A) j).hom.app M ≫
          (resId A U).hom.app ((modulePullback A j).obj M) =
        (modulePullback A j).map ((resId A X).hom.app M)) ∧
    (∀ F : Modules A U,
      (openRes (RingHom.id A) j).hom.app F ≫
          (resId A X).hom.app ((moduleJ A j).obj F) =
        (moduleJ A j).map ((resId A U).hom.app F)) := by
  constructor
  · exact pull_identity_aux A j
  · intro F
    apply left_square_identity (moduleJAdj A j)
      (resId A U).hom (resId A X).hom (openRes (RingHom.id A) j).hom
      (pullRes (RingHom.id A) j).inv
    · intro M
      exact unit_mateEquiv_symm (moduleJAdj A j) (moduleJAdj A j)
        (TwoSquare.mk _ _ _ _ (pullRes (RingHom.id A) j).inv) M
    · intro N
      apply (cancel_epi ((pullRes (RingHom.id A) j).hom.app N)).mp
      simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using
        (pull_identity_aux A j N).symm

end

set_option backward.isDefEq.respectTransparency false in
private theorem left_square_composition
    {D₁ D₂ D₃ E₁ E₂ E₃ : Type*}
    [Category D₁] [Category D₂] [Category D₃]
    [Category E₁] [Category E₂] [Category E₃]
    {L₁ : D₁ ⥤ E₁} {R₁ : E₁ ⥤ D₁}
    {L₂ : D₂ ⥤ E₂} {R₂ : E₂ ⥤ D₂}
    {L₃ : D₃ ⥤ E₃} {R₃ : E₃ ⥤ D₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    {G₁ : D₁ ⥤ D₂} {G₂ : D₂ ⥤ D₃} {G₃ : D₁ ⥤ D₃}
    {H₁ : E₁ ⥤ E₂} {H₂ : E₂ ⥤ E₃} {H₃ : E₁ ⥤ E₃}
    (eG : G₁ ⋙ G₂ ≅ G₃) (eH : H₁ ⋙ H₂ ≅ H₃)
    (p₁ : G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) (p₂ : G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂)
    (p₃ : G₃ ⋙ L₃ ⟶ L₁ ⋙ H₃)
    (d₁ : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) (d₂ : R₂ ⋙ G₂ ⟶ H₂ ⋙ R₃)
    (d₃ : R₁ ⋙ G₃ ⟶ H₃ ⋙ R₃)
    (hu₁ : ∀ M, G₁.map (adj₁.unit.app M) ≫ d₁.app (L₁.obj M) =
      adj₂.unit.app (G₁.obj M) ≫ R₂.map (p₁.app M))
    (hu₂ : ∀ M, G₂.map (adj₂.unit.app M) ≫ d₂.app (L₂.obj M) =
      adj₃.unit.app (G₂.obj M) ≫ R₃.map (p₂.app M))
    (hu₃ : ∀ M, G₃.map (adj₁.unit.app M) ≫ d₃.app (L₁.obj M) =
      adj₃.unit.app (G₃.obj M) ≫ R₃.map (p₃.app M))
    (hd : ∀ N, G₂.map (d₁.app N) ≫ d₂.app (H₁.obj N) ≫ R₃.map (eH.hom.app N) =
      eG.hom.app (R₁.obj N) ≫ d₃.app N) (M : D₁) :
    L₃.map (eG.inv.app M) ≫ p₂.app (G₁.obj M) ≫ H₂.map (p₁.app M) ≫
        eH.hom.app (L₁.obj M) = p₃.app M := by
  apply (cancel_epi (L₃.map (eG.hom.app M))).mp
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  apply (adj₃.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj, Category.assoc]
  simp only [← Category.assoc]
  rw [← hu₂ (G₁.obj M)]
  simp only [Category.assoc]
  have hn := NatTrans.naturality_assoc d₂ (p₁.app M)
    (R₃.map (eH.hom.app (L₁.obj M)))
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [← hn]
  simp only [← Category.assoc, ← Functor.map_comp]
  rw [← hu₁ M]
  simp only [Functor.map_comp, Category.assoc]
  rw [hd, ← Category.assoc]
  have he := eG.hom.naturality (adj₁.unit.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at he
  rw [he]
  simp only [Category.assoc]
  rw [hu₃]
  have ha := adj₃.unit.naturality (eG.hom.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at ha
  simpa only [Functor.id_obj, Functor.comp_obj, Category.assoc] using
    congrArg (fun k ↦ k ≫ R₃.map (p₃.app M)) ha

set_option backward.isDefEq.respectTransparency false in
private theorem resComp_apply {D : Type (u + 1)} [CommRing D]
    (a : B →+* C) (b : C →+* D) (X : Scheme.{u})
    (M : Modules D X) (W : X.ProEtᵒᵖ) (m : M.val.obj W) :
    ((resComp a b X).hom.app M).val.app W m = m :=
  (Classical.choose_spec (ambientRes_existsUnique b X (ringCoefficients B X)
    (ringCoefficientMap a X) (ringCoefficientMap (b.comp a) X)
    (coefficientMap_comp a b X))).1 M W m

set_option backward.isDefEq.respectTransparency false in
private theorem push_composition {D : Type (u + 1)} [CommRing D]
    (a : B →+* C) (b : C →+* D) {Y X : Scheme.{u}} (f : Y ⟶ X)
    (N : Modules D Y) :
    (res a X).map ((pushRes b f).hom.app N) ≫
        (pushRes a f).hom.app ((res b Y).obj N) ≫
        (moduleDirectImage B f).map ((resComp a b Y).hom.app N) =
      (resComp a b X).hom.app ((moduleDirectImage D f).obj N) ≫
        (pushRes (b.comp a) f).hom.app N := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  change ((resComp a b Y).hom.app N).val.app
      ((Scheme.proEtaleBaseChange f).op.obj W)
      (((pushRes a f).hom.app ((res b Y).obj N)).val.app W
        (((pushRes b f).hom.app N).val.app W m)) =
    ((pushRes (b.comp a) f).hom.app N).val.app W
      (((resComp a b X).hom.app ((moduleDirectImage D f).obj N)).val.app W m)
  simp only [resComp_apply, pushRes_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem pull_composition_aux {D : Type (u + 1)} [CommRing D]
    [Finite B] [Finite C] [Finite D] (a : B →+* C) (b : C →+* D)
    {Y X : Scheme.{u}} (f : Y ⟶ X) (M : Modules D X) :
    (modulePullback B f).map ((resComp a b X).inv.app M) ≫
        (pullRes a f).hom.app ((res b X).obj M) ≫
        (res a Y).map ((pullRes b f).hom.app M) ≫
        (resComp a b Y).hom.app ((modulePullback D f).obj M) =
      (pullRes (b.comp a) f).hom.app M := by
  exact left_square_composition
    (Scheme.proEtaleRingModuleAdjunction f
      (coefficients D X) (coefficients D Y) (constantRingIso D f))
    (Scheme.proEtaleRingModuleAdjunction f
      (coefficients C X) (coefficients C Y) (constantRingIso C f))
    (Scheme.proEtaleRingModuleAdjunction f
      (coefficients B X) (coefficients B Y) (constantRingIso B f))
    (resComp a b X) (resComp a b Y)
    (pullRes b f).hom (pullRes a f).hom (pullRes (b.comp a) f).hom
    (pushRes b f).hom (pushRes a f).hom (pushRes (b.comp a) f).hom
    (pull_unit_counit b f).1 (pull_unit_counit a f).1
    (pull_unit_counit (b.comp a) f).1 (push_composition a b f) M

/-- Pullback and open-extension identifications compose along arbitrary coefficient maps.
Source: Stacks Tags 03D2 and 03DI
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: all direct-image scalar identifications are identity on sections, so their
composite is the identity for the composite ring map under resComp. Mate pasting gives
the pullback equality; mate pasting once more under the open adjunctions gives the
extension equality. Applying degreewise gives the same identities for chain maps. -/
theorem scalar_composition {D : Type (u + 1)} [CommRing D]
    [Finite B] [Finite C] [Finite D] (a : B →+* C) (b : C →+* D)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ M : Modules D X,
      (modulePullback B j).map ((resComp a b X).inv.app M) ≫
          (pullRes a j).hom.app ((res b X).obj M) ≫
          (res a U).map ((pullRes b j).hom.app M) ≫
          (resComp a b U).hom.app ((modulePullback D j).obj M) =
        (pullRes (b.comp a) j).hom.app M) ∧
    (∀ F : Modules D U,
      (moduleJ B j).map ((resComp a b U).inv.app F) ≫
          (openRes a j).hom.app ((res b U).obj F) ≫
          (res a X).map ((openRes b j).hom.app F) ≫
          (resComp a b X).hom.app ((moduleJ D j).obj F) =
        (openRes (b.comp a) j).hom.app F) := by
  constructor
  · exact pull_composition_aux a b j
  · intro F
    apply left_square_composition (moduleJAdj D j) (moduleJAdj C j) (moduleJAdj B j)
      (resComp a b U) (resComp a b X)
      (openRes b j).hom (openRes a j).hom (openRes (b.comp a) j).hom
      (pullRes b j).inv (pullRes a j).inv (pullRes (b.comp a) j).inv
    · intro M
      exact unit_mateEquiv_symm (moduleJAdj D j) (moduleJAdj C j)
        (TwoSquare.mk _ _ _ _ (pullRes b j).inv) M
    · intro M
      exact unit_mateEquiv_symm (moduleJAdj C j) (moduleJAdj B j)
        (TwoSquare.mk _ _ _ _ (pullRes a j).inv) M
    · intro M
      exact unit_mateEquiv_symm (moduleJAdj D j) (moduleJAdj B j)
        (TwoSquare.mk _ _ _ _ (pullRes (b.comp a) j).inv) M
    · intro N
      apply (cancel_mono ((pullRes (b.comp a) j).hom.app N)).mp
      simp only [Category.assoc, Iso.inv_hom_id_app]
      conv_lhs => rw [← pull_composition_aux a b j N]
      simp only [Functor.comp_obj]
      slice_lhs 3 4 =>
        rw [← Functor.map_comp, Iso.hom_inv_id_app]
        erw [CategoryTheory.Functor.map_id]
      simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
      slice_lhs 1 2 =>
        rw [← Functor.map_comp, Iso.inv_hom_id_app]
        erw [CategoryTheory.Functor.map_id]
      simp only [Category.id_comp, Category.comp_id]

/-- Pullback scalar identifications preserve the identity for arbitrary scheme maps.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the direct-image comparison is identity on every section after the identity
restriction comparison. Uniqueness of its adjunction mate gives this equation. -/
theorem pull_identity (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y X : Scheme.{u}} (f : Y ⟶ X) (M : Modules A X) :
    (pullRes (RingHom.id A) f).hom.app M ≫
        (resId A Y).hom.app ((modulePullback A f).obj M) =
      (modulePullback A f).map ((resId A X).hom.app M) := by
  exact pull_identity_aux A f M

section

attribute [local irreducible] sourceResC targetResC betaC sourceRes targetRes openRes pullRes
  pushRes beta openResMap Scheme.proEtaleRingModulePullback

end

section

attribute [local irreducible] ambientRes sourceResC targetResC betaC sourceRes targetRes openRes
  pullRes Scheme.proEtaleRingModulePullback

end

end AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars
