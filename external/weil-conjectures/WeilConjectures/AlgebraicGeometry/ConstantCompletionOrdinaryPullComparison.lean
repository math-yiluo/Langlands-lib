/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.RingedCoefficientPullbackComparison
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import all WeilConjectures.CategoryTheory.GeometricModuleTransport

/-!
# Constant coefficient completion: OrdinaryPullComparison

The ordinary scalar pullback comparison (`ordinaryPullComparison_existsUnique`).

Part of the split of `Sheaf.Paper.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local irreducible] completed
variable {J A I}
attribute [local irreducible] derivedExtension
attribute [local irreducible] SheafOfModules.monoidalCategory
variable (J A I)
variable {J A I}
attribute [local irreducible] strictLimit
variable (J A I)
attribute [local irreducible] ordinaryUnit
attribute [local irreducible] quotientPresentation
variable {J A I}
variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)
attribute [local semireducible] completed
attribute [local irreducible] completed
variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]
attribute [local irreducible] derivedPull pull change

set_option backward.isDefEq.respectTransparency false

open SheafOfModules.RingedCoefficientProjection
  (imagePair imagePair_fst imagePair_snd addMap smulMap)

private def restrictionUnderlying {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (M : Mod S) :
    (underlying (F.rings.obj R)).obj
        ((F.algebra R).modules.obj ((res a).obj M)) ≅
      (underlying (F.rings.obj R)).obj
        ((res (F.rings.map a)).obj
          ((F.algebra S).modules.obj M)) :=
  (F.algebra R).moduleUnderlying.app
    ((res a).obj M) ≪≫
      ((F.algebra S).moduleUnderlying.app M).symm

private theorem restrictionUnderlying_add {R S : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (M : Mod S) (U : C'ᵒᵖ)
    (x y : ((F.algebra R).modules.obj
      ((res a).obj M)).val.obj U) :
    (restrictionUnderlying F a M).hom.hom.app U (x + y) =
      (show ((F.algebra S).modules.obj M).val.obj U from
        (restrictionUnderlying F a M).hom.hom.app U x) +
      (show ((F.algebra S).modules.obj M).val.obj U from
        (restrictionUnderlying F a M).hom.hom.app U y) := by
  let N := (res a).obj M
  let A := (underlying S).obj M
  let e := (F.algebra R).moduleUnderlying.app N
  let p := imagePair A A U (e.hom.hom.app U x) (e.hom.hom.app U y)
  have hR := (F.algebra R).moduleAdd N (A ⨯ A) prod.fst prod.snd (addMap M)
    (fun _ _ ↦ rfl) U p
  have hS := (F.algebra S).moduleAdd M (A ⨯ A) prod.fst prod.snd (addMap M)
    (fun _ _ ↦ rfl) U p
  have hx : (e.inv).hom.app U ((L.map (prod.fst : A ⨯ A ⟶ A)).hom.app U p) = x := by
    rw [imagePair_fst]
    exact congrArg (fun k ↦ k.hom.app U x) e.hom_inv_id
  have hy : (e.inv).hom.app U ((L.map (prod.snd : A ⨯ A ⟶ A)).hom.app U p) = y := by
    rw [imagePair_snd]
    exact congrArg (fun k ↦ k.hom.app U y) e.hom_inv_id
  dsimp only [id] at hR hS
  change e.inv.hom.app U ((L.map (addMap M)).hom.app U p) =
    (show ((F.algebra R).modules.obj N).val.obj U from
      e.inv.hom.app U ((L.map (prod.fst : A ⨯ A ⟶ A)).hom.app U p)) +
    (show ((F.algebra R).modules.obj N).val.obj U from
      e.inv.hom.app U ((L.map (prod.snd : A ⨯ A ⟶ A)).hom.app U p)) at hR
  have hR' := hR.trans (congrArg₂ (· + ·) hx hy)
  let f : ((F.algebra R).modules.obj N).val.obj U →
      ((F.algebra S).modules.obj M).val.obj U := fun z ↦
    ((F.algebra S).moduleUnderlying.inv.app M).hom.app U (e.hom.hom.app U z)
  have h := congrArg f hR'
  have hc : f (e.inv.hom.app U ((L.map (addMap M)).hom.app U p)) =
      ((F.algebra S).moduleUnderlying.inv.app M).hom.app U
        ((L.map (addMap M)).hom.app U p) :=
    congrArg (fun z ↦ ((F.algebra S).moduleUnderlying.inv.app M).hom.app U z)
      (congrArg (fun k ↦ k.hom.app U ((L.map (addMap M)).hom.app U p)) e.inv_hom_id)
  change ((F.algebra S).moduleUnderlying.inv.app M).hom.app U
      ((L.map (addMap M)).hom.app U p) =
    (show ((F.algebra S).modules.obj M).val.obj U from
      ((F.algebra S).moduleUnderlying.inv.app M).hom.app U
        ((L.map (prod.fst : A ⨯ A ⟶ A)).hom.app U p)) +
    (show ((F.algebra S).modules.obj M).val.obj U from
      ((F.algebra S).moduleUnderlying.inv.app M).hom.app U
        ((L.map (prod.snd : A ⨯ A ⟶ A)).hom.app U p)) at hS
  have hS' := hS.trans (congrArg₂ (· + ·)
    (congrArg (fun z ↦ ((F.algebra S).moduleUnderlying.inv.app M).hom.app U z)
      (imagePair_fst A A U _ _))
    (congrArg (fun z ↦ ((F.algebra S).moduleUnderlying.inv.app M).hom.app U z)
      (imagePair_snd A A U _ _)))
  change f (x + y) = f x + f y
  exact h.symm.trans (hc.trans hS')

private theorem restrictionUnderlying_smul {R S : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (M : Mod S) (U : C'ᵒᵖ)
    (t : (F.rings.obj R).obj.obj U)
    (x : ((F.algebra R).modules.obj
      ((res a).obj M)).val.obj U) :
    (restrictionUnderlying F a M).hom.hom.app U (t • x) =
      t • (show ((res (F.rings.map a)).obj
        ((F.algebra S).modules.obj M)).val.obj U from
          (restrictionUnderlying F a M).hom.hom.app U x) := by
  let N := (res a).obj M
  let A := (underlying S).obj M
  let B := (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R
  let e := (F.algebra R).moduleUnderlying.app N
  let er := (F.algebra R).ringUnderlying
  let p := imagePair B A U (er.inv.hom.app U t) (e.hom.hom.app U x)
  let b : B ⨯ A ⟶ (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj S :=
    prod.fst ≫ (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map a
  have hR := (F.algebra R).moduleSMul N (B ⨯ A) prod.fst prod.snd (smulMap N)
    (fun _ _ ↦ rfl) U p
  have hS := (F.algebra S).moduleSMul M (B ⨯ A) b prod.snd (smulMap N)
    (fun _ _ ↦ rfl) U p
  have ht : er.hom.hom.app U ((L.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p) = t := by
    rw [imagePair_fst]
    exact congrArg (fun k ↦ k.hom.app U t) er.inv_hom_id
  have hx : e.inv.hom.app U ((L.map (prod.snd : B ⨯ A ⟶ A)).hom.app U p) = x := by
    rw [imagePair_snd]
    exact congrArg (fun k ↦ k.hom.app U x) e.hom_inv_id
  dsimp only [id] at hR hS
  change e.inv.hom.app U ((L.map (smulMap N)).hom.app U p) =
    (show (F.rings.obj R).obj.obj U from
      er.hom.hom.app U ((L.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p)) •
      (show ((F.algebra R).modules.obj N).val.obj U from
        e.inv.hom.app U ((L.map (prod.snd : B ⨯ A ⟶ A)).hom.app U p)) at hR
  have hR' := hR.trans (congrArg₂ (· • ·) ht hx)
  change ((F.algebra S).moduleUnderlying.inv.app M).hom.app U
      ((L.map (smulMap N)).hom.app U p) =
    (show (F.rings.obj S).obj.obj U from
      (F.algebra S).ringUnderlying.hom.hom.app U ((L.map b).hom.app U p)) •
      (show ((F.algebra S).modules.obj M).val.obj U from
        ((F.algebra S).moduleUnderlying.inv.app M).hom.app U
          ((L.map (prod.snd : B ⨯ A ⟶ A)).hom.app U p)) at hS
  have hb : ((F.algebra S).ringUnderlying.hom).hom.app U
      ((L.map b).hom.app U p) = (F.rings.map a).hom.app U t := by
    have h := congrArg (fun k ↦ k.hom.app U
      ((L.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p))
      (F.ring_naturality a)
    change ((F.algebra S).ringUnderlying.hom).hom.app U
        ((L.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map a)).hom.app U
          ((L.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p)) =
      (F.rings.map a).hom.app U
        (er.hom.hom.app U ((L.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p)) at h
    rw [ht] at h
    simpa only [b, Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, types_comp_apply] using h
  have hp : (L.map (prod.snd : B ⨯ A ⟶ A)).hom.app U p =
      e.hom.hom.app U x := imagePair_snd B A U _ _
  have hS' := hS.trans (congrArg₂ (· • ·) hb
    (congrArg (fun z ↦ ((F.algebra S).moduleUnderlying.inv.app M).hom.app U z) hp))
  let f : ((F.algebra R).modules.obj N).val.obj U →
      ((F.algebra S).modules.obj M).val.obj U := fun z ↦
    ((F.algebra S).moduleUnderlying.inv.app M).hom.app U (e.hom.hom.app U z)
  have h := congrArg f hR'
  have hc : f (e.inv.hom.app U ((L.map (smulMap N)).hom.app U p)) =
      ((F.algebra S).moduleUnderlying.inv.app M).hom.app U
        ((L.map (smulMap N)).hom.app U p) :=
    congrArg (fun z ↦ ((F.algebra S).moduleUnderlying.inv.app M).hom.app U z)
      (congrArg (fun k ↦ k.hom.app U ((L.map (smulMap N)).hom.app U p)) e.inv_hom_id)
  change f (t • x) = (F.rings.map a).hom.app U t • f x
  exact h.symm.trans (hc.trans hS')

private def restrictionMap {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (M : Mod S) :
    (F.algebra R).modules.obj ((res a).obj M) ⟶
      (res (F.rings.map a)).obj
        ((F.algebra S).modules.obj M) :=
  SheafOfModules.linearLift (restrictionUnderlying F a M).hom
    (restrictionUnderlying_add F a M) (restrictionUnderlying_smul F a M)

private def inverseRestriction {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    res a ⋙ (F.algebra R).modules ⟶ (F.algebra S).modules ⋙ res (F.rings.map a) where
  app := restrictionMap F a
  naturality := by
    intro M N f
    apply (underlying (F.rings.obj R)).map_injective
    change (underlying (F.rings.obj R)).map
        ((F.algebra R).modules.map ((res a).map f)) ≫
          (restrictionUnderlying F a N).hom =
        (restrictionUnderlying F a M).hom ≫
          (underlying (F.rings.obj S)).map ((F.algebra S).modules.map f)
    have hR := (F.algebra R).moduleUnderlying.hom.naturality ((res a).map f)
    have hS := (F.algebra S).moduleUnderlying.inv.naturality f
    dsimp only [Functor.comp_map] at hR hS
    dsimp only [restrictionUnderlying, Iso.trans_hom, Iso.symm_hom]
    erw [← Category.assoc, hR, Category.assoc, hS]
    rfl

attribute [local semireducible] change pull

private def scalarAdj {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S) :
    change c ⊣ res c := SheafOfModules.RingedTensor.tensorAdjunction c

private theorem insertion_eq_unit {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S)
    (M : Mod R) :
    insertion c M = (underlying R).map ((scalarAdj c).unit.app M) := by
  apply (insertion_existsUnique c M).unique
    (insertion_existsUnique c M).exists.choose_spec
  intro U m
  rfl

attribute [local semireducible] completed

omit hL in
private theorem coefficient_square (A : Type u) [CommRing A] (I : Ideal A) :
    constantMap F A ≫ coefficientMap J' A I =
      F.rings.map (coefficientMap J A I) ≫ completedMap F A I := by
  apply limit.hom_ext
  intro n
  change (constantMap F A ≫ coefficientMap J' A I) ≫
      limit.π (finiteSystem J' A I) n = _
  simp only [Category.assoc, coefficientMap, completedMap, limit.lift_π]
  change constantMap F A ≫ quotient J' A I n.unop =
    F.rings.map (coefficientMap J A I) ≫
      (F.rings.map (projection J A I n.unop) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (n.unop + 1)))).hom)
  rw [← Category.assoc, ← F.rings.map_comp]
  have hp : coefficientMap J A I ≫ projection J A I n.unop =
      quotient J A I n.unop := limit.lift_π (quotientCone J A I) (op n.unop)
  rw [hp]
  exact (F.constants.hom.naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n.unop + 1))))).symm

attribute [local irreducible] completed

private def squareRestriction {R S T U : Sheaf J' CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ U) (c : R ⟶ T) (d : T ⟶ U) (h : c ≫ d = a ≫ b) :
    res b ⋙ res a ≅ res d ⋙ res c :=
  resCompIso a b (a ≫ b) rfl ≪≫ (resCompIso c d (a ≫ b) h).symm

private theorem squareRestriction_apply {R S T U : Sheaf J' CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ U) (c : R ⟶ T) (d : T ⟶ U) (h : c ≫ d = a ≫ b)
    (M : Mod U) (W : C'ᵒᵖ) (m : M.val.obj W) :
    ((squareRestriction a b c d h).hom.app M).val.app W m = m := by
  change ((resCompIso c d (a ≫ b) h).inv.app M).val.app W
    (((resCompIso a b (a ≫ b) rfl).hom.app M).val.app W m) = m
  rw [resCompIso_hom_apply, resCompIso_inv_apply]

private def comparisonAdjunct (A : Type u) [CommRing A] (I : Ideal A) :
    res (coefficientMap J A I) ⋙ (F.algebra (constant J A)).modules ⟶
      pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) ⋙ res (constantMap F A) :=
  inverseRestriction F (coefficientMap J A I) ≫
    Functor.whiskerLeft (F.algebra (completed J A I)).modules
      (Functor.whiskerRight (scalarAdj (completedMap F A I)).unit
        (res (F.rings.map (coefficientMap J A I)))) ≫
    Functor.whiskerLeft (pull F (completedMap F A I))
      (squareRestriction (F.rings.map (coefficientMap J A I)) (completedMap F A I)
        (constantMap F A) (coefficientMap J' A I) (coefficient_square F A I)).hom

private def comparison (A : Type u) [CommRing A] (I : Ideal A) :
    res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⟶
      pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) where
  app M := ((scalarAdj (constantMap F A)).homEquiv _ _).symm
    ((comparisonAdjunct F A I).app M)
  naturality := by
    intro M N f
    apply ((scalarAdj (constantMap F A)).homEquiv _ _).injective
    dsimp only [Functor.comp_map, pull]
    rw [(scalarAdj (constantMap F A)).homEquiv_naturality_left,
      (scalarAdj (constantMap F A)).homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact (comparisonAdjunct F A I).naturality f

private theorem comparisonAdjunct_underlying (A : Type u) [CommRing A] (I : Ideal A)
    (M : Mod (completed J A I)) :
    (underlying (F.rings.obj (constant J A))).map ((comparisonAdjunct F A I).app M) =
      (F.algebra (constant J A)).moduleUnderlying.hom.app
        ((res (coefficientMap J A I)).obj M) ≫ pullInsertion F (completedMap F A I) M := by
  ext W x
  dsimp only [comparisonAdjunct, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  change ((squareRestriction (F.rings.map (coefficientMap J A I))
      (completedMap F A I) (constantMap F A) (coefficientMap J' A I)
      (coefficient_square F A I)).hom.app _).val.app W _ = _
  rw [squareRestriction_apply]
  rw [pullInsertion, insertion_eq_unit]
  rfl

omit hL in
private theorem pull_homEquiv {R : Sheaf J CommRingCat.{u}}
    {S : Sheaf J' CommRingCat.{u}} (c : F.rings.obj R ⟶ S)
    (M : Mod R) (N : Mod S) (f : (pull F c).obj M ⟶ N) :
    (F.algebra R).moduleUnderlying.inv.app M ≫
        (underlying (F.rings.obj R)).map ((scalarAdj c).homEquiv _ _ f) =
      pullInsertion F c M ≫ (underlying S).map f := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, pullInsertion, insertion_eq_unit]
  rfl

/-- The unreduced scalar comparison on ordinary modules is fixed by scalar insertion.
This is exactly u^(-1)M → u^(-1)M tensor the completed coefficient ring after inverse image.
Source: Stacks 06YY, 099L (auxiliary; not a blueprint node).
Proof: the finite projections make the coefficient square commute. After identifying
inverse images of constant coefficients, define q by m ↦ 1 tensor m. It is linear over
the constant coefficient sheaf, and natural in M. Pure tensors generate after
sheafification, so the insertion equation determines q uniquely. -/
theorem ordinaryPullComparison_existsUnique (A : Type u) [CommRing A] (I : Ideal A) :
    ∃! q : res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⟶
        pull F (completedMap F A I) ⋙ res (coefficientMap J' A I),
      ∀ M : Mod (completed J A I),
        pullInsertion F (constantMap F A) ((res (coefficientMap J A I)).obj M) ≫
            (underlying (constant J' A)).map (q.app M) =
          pullInsertion F (completedMap F A I) M := by
  have hnorm (M : Mod (completed J A I)) :
      pullInsertion F (constantMap F A) ((res (coefficientMap J A I)).obj M) ≫
          (underlying (constant J' A)).map ((comparison F A I).app M) =
        pullInsertion F (completedMap F A I) M := by
    rw [← pull_homEquiv]
    change (F.algebra (constant J A)).moduleUnderlying.inv.app _ ≫
      (underlying (F.rings.obj (constant J A))).map
        (((scalarAdj (constantMap F A)).homEquiv _ _)
          (((scalarAdj (constantMap F A)).homEquiv _ _).symm
            ((comparisonAdjunct F A I).app M))) = _
    rw [Equiv.apply_symm_apply, comparisonAdjunct_underlying]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  refine ⟨comparison F A I, hnorm, ?_⟩
  intro q hq
  apply NatTrans.ext
  funext M
  apply ((scalarAdj (constantMap F A)).homEquiv _ _).injective
  apply (underlying (F.rings.obj (constant J A))).map_injective
  apply (cancel_epi ((F.algebra (constant J A)).moduleUnderlying.inv.app
    ((res (coefficientMap J A I)).obj M))).mp
  rw [pull_homEquiv, pull_homEquiv]
  exact (hq M).trans (hnorm M).symm

end CategoryTheory.ConstantCompletion
