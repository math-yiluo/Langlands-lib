/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData
import all WeilConjectures.Algebra.Homology.StrictScalarHom.SliceScalarHomChainAdjunction
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-! # Ordinary clopen scalar comparison

Source: Stacks Project, sites-modules.tex, Tags 03EL, 03CY and 03DH.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] ClopenLocalization.modulesAbelian ClopenLocalization.hasDerived
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

open scoped ChangeOfRings
open SheafOfModules.StrictScalarHom
universe a b e f r

section OrdinaryRestriction
variable {C₀ : Type a} [Category.{b} C₀] {D₀ : Type e} [Category.{f} D₀]
  {J₀ : GrothendieckTopology C₀} {K₀ : GrothendieckTopology D₀}
  (F : C₀ ⥤ D₀) [Functor.IsContinuous F J₀ K₀] [F.IsCocontinuous J₀ K₀]
  [J₀.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J₀ AddCommGrpCat.{r}]
  [HasWeakSheafify J₀ AddCommGrpCat.{r}]
  [K₀.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K₀ AddCommGrpCat.{r}]
  [HasWeakSheafify K₀ AddCommGrpCat.{r}]
  [K₀.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R₀ S₀ : Sheaf K₀ CommRingCat.{r}} (φ₀ : R₀ ⟶ S₀)

private theorem pure_hom_ext
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀))
    {H : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)}
    (f g : changeOfRings φ₀ M ⟶ H)
    (h : ∀ U s x, f.val.app U (pure φ₀ M U s x) =
      g.val.app U (pure φ₀ M U s x)) : f = g := by
  apply (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀) (𝟙 _)).homEquiv _ _
    |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact h U 1 x

private theorem pure_map
    {M N : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)}
    (g : M ⟶ N) (U : D₀ᵒᵖ) (s : S₀.obj.obj U) (x : M.val.obj U) :
    (changeOfRingsHom φ₀ M g).val.app U (pure φ₀ M U s x) =
      pure φ₀ N U s (g.val.app U x) := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀) (𝟙 _)).unit.naturality
      ({ app := fun V ↦ (ModuleCat.extendScalars (φ₀.hom.app V).hom).map (g.val.app V)
         naturality := changeOfRingsHom_naturality φ₀ M g } :
        changeOfRingsPresheaf φ₀ M ⟶ changeOfRingsPresheaf φ₀ N)
  exact (congrArg (fun z ↦ z.app U
    (s ⊗ₜ[R₀.obj.obj U, (φ₀.hom.app U).hom] x)) h).symm

private def oldScalarRawIso
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    changeOfRingsPresheaf ((pullRing (J₀ := J₀) F).map φ₀)
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) ≅
      (rawRestriction (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).obj
          (changeOfRingsPresheaf φ₀ M) :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro X Y f
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    exact (changeOfRingsMap_tmul
      ((pullRing (J₀ := J₀) F).map φ₀) _ f 1 x).trans
      (changeOfRingsMap_tmul φ₀ M (F.op.map f) 1 x).symm)

omit [F.IsCocontinuous J₀ K₀] [HasSheafify J₀ AddCommGrpCat.{r}]
  [HasSheafify K₀ AddCommGrpCat.{r}] in
private theorem oldScalarRawIso_pure
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀))
    (X : C₀ᵒᵖ) (s : S₀.obj.obj (F.op.obj X)) (x : M.val.obj (F.op.obj X)) :
    (oldScalarRawIso (J₀ := J₀) F φ₀ M).hom.app X
      (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x) =
      s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x := rfl

attribute [local irreducible] oldScalarRawIso

private def oldScalarBackHom
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    changeOfRings ((pullRing (J₀ := J₀) F).map φ₀)
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) ⟶
      (moduleRestrictionF (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).obj
          (changeOfRings φ₀ M) :=
  let A := (sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀
  let T := PresheafOfModules.sheafification
    (R := restrictedRing (J₀ := J₀) F A) (𝟙 _)
  T.map (oldScalarRawIso (J₀ := J₀) F φ₀ M).hom ≫
    restrictionSheafify (J₀ := J₀) F A (changeOfRingsPresheaf φ₀ M)

omit [F.IsCocontinuous J₀ K₀] [HasSheafify J₀ AddCommGrpCat.{r}]
  [HasSheafify K₀ AddCommGrpCat.{r}] in
private theorem oldScalarBackHom_eq
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    oldScalarBackHom (J₀ := J₀) F φ₀ M =
      (PresheafOfModules.sheafification
        (R := restrictedRing (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)) (𝟙 _)).map
        (oldScalarRawIso (J₀ := J₀) F φ₀ M).hom ≫
        restrictionSheafify (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)
          (changeOfRingsPresheaf φ₀ M) := rfl

attribute [local irreducible] oldScalarBackHom

omit [F.IsCocontinuous J₀ K₀] in
private theorem oldScalarBackHom_pure
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀))
    (X : C₀ᵒᵖ) (s : S₀.obj.obj (F.op.obj X)) (x : M.val.obj (F.op.obj X)) :
    (oldScalarBackHom (J₀ := J₀) F φ₀ M).val.app X
        (pure ((pullRing (J₀ := J₀) F).map φ₀)
          ((moduleRestrictionF (J₀ := J₀) F
            ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) X s x) =
      pure φ₀ M (F.op.obj X) s x := by
  let A := (sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀
  let P := changeOfRingsPresheaf φ₀ M
  let Q := changeOfRingsPresheaf ((pullRing (J₀ := J₀) F).map φ₀)
    ((moduleRestrictionF (J₀ := J₀) F
      ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M)
  let b := PresheafOfModules.sheafificationAdjunction (R := restrictedRing (J₀ := J₀) F A)
    (𝟙 _)
  have hn := b.unit.naturality (oldScalarRawIso (J₀ := J₀) F φ₀ M).hom
  have hu := restrictionSheafify_unit (J₀ := J₀) (K₀ := K₀) F A P
  have hn' := congrArg (fun t ↦ t.app X
    (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x)) hn
  change (toSheafify J₀ ((rawRestriction (J₀ := J₀) F A).obj P).presheaf).app X
      ((oldScalarRawIso (J₀ := J₀) F φ₀ M).hom.app X
        (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x)) = _ at hn'
  rw [oldScalarRawIso_pure] at hn'
  have hu' := congrArg (fun t ↦ t.app X
    (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x)) hu
  have hn'' := congrArg (fun z ↦ (restrictionSheafify (J₀ := J₀) F A P).val.app X z) hn'
  change (oldScalarBackHom (J₀ := J₀) F φ₀ M).val.app X
      (pure _ _ X s x) = _
  rw [oldScalarBackHom_eq]
  change (restrictionSheafify (J₀ := J₀) F A P).val.app X
    (((PresheafOfModules.sheafification (𝟙 _)).map
      (oldScalarRawIso (J₀ := J₀) F φ₀ M).hom).val.app X
      (pure ((pullRing (J₀ := J₀) F).map φ₀) _ X s x)) = _
  exact hn''.symm.trans hu'

omit [F.IsCocontinuous J₀ K₀] in
private theorem oldScalarBackHom_natural
    {M N : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)}
    (g : M ⟶ N) :
    changeOfRingsHom ((pullRing (J₀ := J₀) F).map φ₀) _
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).map g) ≫
        (oldScalarBackHom (J₀ := J₀) F φ₀ N) =
      (oldScalarBackHom (J₀ := J₀) F φ₀ M) ≫
        (moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).map
            (changeOfRingsHom φ₀ M g) := by
  apply pure_hom_ext ((pullRing (J₀ := J₀) F).map φ₀)
    ((moduleRestrictionF (J₀ := J₀) F
      ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M)
  intro X s x
  change (oldScalarBackHom (J₀ := J₀) F φ₀ N).val.app X
      ((changeOfRingsHom ((pullRing (J₀ := J₀) F).map φ₀) _
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).map g)).val.app X
        (pure ((pullRing (J₀ := J₀) F).map φ₀)
          ((moduleRestrictionF (J₀ := J₀) F
            ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) X s x)) =
    (changeOfRingsHom φ₀ M g).val.app (F.op.obj X)
      ((oldScalarBackHom (J₀ := J₀) F φ₀ M).val.app X
        (pure ((pullRing (J₀ := J₀) F).map φ₀)
          ((moduleRestrictionF (J₀ := J₀) F
            ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) X s x))
  rw [pure_map, oldScalarBackHom_pure, oldScalarBackHom_pure, pure_map]
  rfl

omit [HasSheafify J₀ AddCommGrpCat.{r}] [HasSheafify K₀ AddCommGrpCat.{r}] in
private theorem oldScalarBackHom_isIso
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    IsIso (oldScalarBackHom (J₀ := J₀) F φ₀ M) := by
  let := restrictionSheafify_isIso (J₀ := J₀) F
    ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)
      (changeOfRingsPresheaf φ₀ M)
  change IsIso (oldScalarBackHom (J₀ := J₀) F φ₀ M)
  rw [oldScalarBackHom_eq]
  change IsIso
    ((PresheafOfModules.sheafification
      (R := restrictedRing (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)) (𝟙 _)).map
      (oldScalarRawIso (J₀ := J₀) F φ₀ M).hom ≫
      restrictionSheafify (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)
        (changeOfRingsPresheaf φ₀ M))
  infer_instance

private def oldScalarBackIso
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    changeOfRings ((pullRing (J₀ := J₀) F).map φ₀)
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) ≅
      (moduleRestrictionF (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).obj
          (changeOfRings φ₀ M) := by
  letI := oldScalarBackHom_isIso (J₀ := J₀) F φ₀ M
  exact asIso (oldScalarBackHom (J₀ := J₀) F φ₀ M)

private theorem oldScalarBackIso_pure
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀))
    (X : C₀ᵒᵖ) (s : S₀.obj.obj (F.op.obj X)) (x : M.val.obj (F.op.obj X)) :
    (oldScalarBackIso (J₀ := J₀) F φ₀ M).hom.val.app X
        (pure ((pullRing (J₀ := J₀) F).map φ₀)
          ((moduleRestrictionF (J₀ := J₀) F
            ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) X s x) =
      pure φ₀ M (F.op.obj X) s x := by
  exact oldScalarBackHom_pure (J₀ := J₀) F φ₀ M X s x

private theorem oldScalarBackIso_natural
    {M N : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)}
    (g : M ⟶ N) :
    changeOfRingsHom ((pullRing (J₀ := J₀) F).map φ₀) _
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).map g) ≫
        (oldScalarBackIso (J₀ := J₀) F φ₀ N).hom =
      (oldScalarBackIso (J₀ := J₀) F φ₀ M).hom ≫
        (moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).map
            (changeOfRingsHom φ₀ M g) := by
  exact oldScalarBackHom_natural (J₀ := J₀) F φ₀ g

attribute [local irreducible] oldScalarBackIso

end OrdinaryRestriction

attribute [local irreducible] changeOfRings changeOfRingsHom changeOfRingsPresheaf
  SheafOfModules.pushforward PresheafOfModules.pushforward


attribute [local semireducible] SheafOfModules.pushforward PresheafOfModules.pushforward

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
