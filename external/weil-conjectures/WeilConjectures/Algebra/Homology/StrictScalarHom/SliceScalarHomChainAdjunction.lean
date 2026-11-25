/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.StrictScalarHom.StrictScalarHomChain
import all WeilConjectures.Algebra.Homology.StrictScalarHom.StrictScalarHomChain
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Slice-normalized scalar adjunction for product Hom complexes

Source: Stacks Project, sites-modules.tex, Tags 03CZ, 03CY, 03DH and 04IX;
sites-cohomology.tex, Tag 0A8X
(blueprint: lem-sfb-slice-scalar-hom-chain-adjunction).

The interfaces below reuse the existing scalar extension, tensor and actual Hom
product projections. They specify the ordinary slice adjunctions and precisely
the nu/theta portion of the scalar-Hom comparison, without its evaluation square.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.StrictScalarHom

attribute [local irreducible] changeOfRingsOfUniverses changeOfRingsHomOfUniverses
  scalarExtensionSection tensorSection evaluate homMap

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasWeakSheafify J AddCommGrpCat.{max c v u}]

open scoped ChangeOfRings

set_option linter.unusedTactic false
set_option linter.unusedSectionVars false

attribute [local semireducible] changeOfRingsOfUniverses changeOfRingsHomOfUniverses
  scalarExtensionSection evaluate

attribute [local instance] ordinaryExtension_additive
attribute [local irreducible] scalarSheafHomEquiv ordinaryAdjunction

private def extensionIso {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) : ordinaryExtension.{c, v, u} φ ≅ E.functor := by
  let e : ordinaryExtension.{c, v, u} φ ≅ E.functor :=
    NatIso.ofComponents (fun M ↦ eqToIso (E.obj_eq M).symm) (by
      intro M N f
      change changeOfRingsHomOfUniverses φ M f ≫ eqToHom (E.obj_eq N).symm =
        eqToHom (E.obj_eq M).symm ≫ E.functor.map f
      rw [E.map_eq]
      simp)
  exact e

private def normalizedAdjunction {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) : E.functor ⊣ moduleRestriction.{c, v, u} φ :=
  (ordinaryAdjunction.{c, v, u} φ).ofNatIsoLeft (extensionIso E)

attribute [local irreducible] normalizedAdjunction extensionIso

attribute [local irreducible] ordinaryExtension canonicalExtension

universe a b d e r

section RestrictionComparison
variable {C₀ : Type a} [Category.{b} C₀] {D₀ : Type d} [Category.{e} D₀]
  {J₀ : GrothendieckTopology C₀} {K₀ : GrothendieckTopology D₀}
  (F : C₀ ⥤ D₀) [Functor.IsContinuous F J₀ K₀] [F.IsCocontinuous J₀ K₀]
  [J₀.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J₀ AddCommGrpCat.{r}]
  [K₀.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify K₀ AddCommGrpCat.{r}]
  (A : Sheaf K₀ RingCat.{r})

private abbrev restrictedRing := (F.sheafPushforwardContinuous RingCat.{r} J₀ K₀).obj A

private def rawRestriction : PresheafOfModules.{r} A.obj ⥤
    PresheafOfModules.{r} (restrictedRing (J₀ := J₀) F A).obj :=
  PresheafOfModules.pushforward (F := F) (𝟙 _)

private def moduleRestrictionF : SheafOfModules.{r} A ⥤
    SheafOfModules.{r} (restrictedRing (J₀ := J₀) F A) :=
  pushforward (F := F) (𝟙 _)

private def restrictionSheafify (P : PresheafOfModules.{r} A.obj) :
    (PresheafOfModules.sheafification (R := restrictedRing (J₀ := J₀) F A) (𝟙 _)).obj
      ((rawRestriction F A).obj P) ⟶
    (moduleRestrictionF F A).obj
      ((PresheafOfModules.sheafification (R := A) (𝟙 _)).obj P) :=
  ((PresheafOfModules.sheafificationAdjunction
    (R := restrictedRing (J₀ := J₀) F A) (𝟙 _)).homEquiv _ _).symm
      ((rawRestriction F A).map
        ((PresheafOfModules.sheafificationAdjunction (R := A) (𝟙 _)).unit.app P))

omit [F.IsCocontinuous J₀ K₀] in
private theorem restrictionSheafify_unit (P : PresheafOfModules.{r} A.obj) :
    toSheafify J₀ ((rawRestriction F A).obj P).presheaf ≫
      (PresheafOfModules.toPresheaf _).map (restrictionSheafify (J₀ := J₀) F A P).val =
    Functor.whiskerLeft F.op (toSheafify K₀ P.presheaf) := by
  have h := ((PresheafOfModules.sheafificationAdjunction
    (R := restrictedRing (J₀ := J₀) F A) (𝟙 _)).homEquiv
      ((rawRestriction F A).obj P)
      ((moduleRestrictionF F A).obj
        ((PresheafOfModules.sheafification (R := A) (𝟙 _)).obj P))).apply_symm_apply
      ((rawRestriction F A).map
        ((PresheafOfModules.sheafificationAdjunction (R := A) (𝟙 _)).unit.app P))
  exact congrArg ((PresheafOfModules.toPresheaf (restrictedRing (J₀ := J₀) F A).obj).map) h

private theorem restrictionSheafify_isIso (P : PresheafOfModules.{r} A.obj) :
    IsIso (restrictionSheafify (J₀ := J₀) F A P) := by
  let η := toSheafify J₀ ((rawRestriction (J₀ := J₀) F A).obj P).presheaf
  let t := (PresheafOfModules.toPresheaf (restrictedRing (J₀ := J₀) F A).obj).map
    (restrictionSheafify (J₀ := J₀) F A P).val
  have hi : Presheaf.IsLocallyInjective J₀
      (Functor.whiskerLeft F.op (toSheafify K₀ P.presheaf)) :=
    Presheaf.isLocallyInjective_whisker J₀ K₀ F _
  have hs : Presheaf.IsLocallySurjective J₀
      (Functor.whiskerLeft F.op (toSheafify K₀ P.presheaf)) :=
    Presheaf.isLocallySurjective_whisker J₀ K₀ F _
  have hi' : Presheaf.IsLocallyInjective J₀ t := by
    rw [← Presheaf.comp_isLocallyInjective_iff J₀ η t]
    change Presheaf.IsLocallyInjective J₀
      (toSheafify J₀ ((rawRestriction (J₀ := J₀) F A).obj P).presheaf ≫
        (PresheafOfModules.toPresheaf _).map
          (restrictionSheafify (J₀ := J₀) F A P).val)
    rw [restrictionSheafify_unit (J₀ := J₀) F A P]
    exact hi
  have hs' : Presheaf.IsLocallySurjective J₀ t := by
    rw [← Presheaf.comp_isLocallySurjective_iff J₀ η t]
    change Presheaf.IsLocallySurjective J₀
      (toSheafify J₀ ((rawRestriction (J₀ := J₀) F A).obj P).presheaf ≫
        (PresheafOfModules.toPresheaf _).map
          (restrictionSheafify (J₀ := J₀) F A P).val)
    rw [restrictionSheafify_unit (J₀ := J₀) F A P]
    exact hs
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (restrictedRing (J₀ := J₀) F A))]
  exact (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hi', hs'⟩

attribute [local irreducible] restrictionSheafify

variable [K₀.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R₀ S₀ : Sheaf K₀ CommRingCat.{r}} (φ₀ : R₀ ⟶ S₀)

private abbrev pullRing := F.sheafPushforwardContinuous CommRingCat.{r} J₀ K₀

private def scalarRawIso
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    changeOfRingsPresheafOfUniverses ((pullRing (J₀ := J₀) F).map φ₀)
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) ≅
      (rawRestriction (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).obj
          (changeOfRingsPresheafOfUniverses φ₀ M) :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro X Y f
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    exact (changeOfRingsMap_tmulOfUniverses
      ((pullRing (J₀ := J₀) F).map φ₀) _ f 1 x).trans
      (changeOfRingsMap_tmulOfUniverses φ₀ M (F.op.map f) 1 x).symm)

private theorem scalarRawIso_pure
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀))
    (X : C₀ᵒᵖ) (s : S₀.obj.obj (F.op.obj X)) (x : M.val.obj (F.op.obj X)) :
    (scalarRawIso (J₀ := J₀) F φ₀ M).hom.app X
      (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x) =
      s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x := rfl

attribute [local irreducible] scalarRawIso

private def scalarBackHom
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    changeOfRingsOfUniverses ((pullRing (J₀ := J₀) F).map φ₀)
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) ⟶
      (moduleRestrictionF (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).obj
          (changeOfRingsOfUniverses φ₀ M) :=
  let A := (sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀
  let T := PresheafOfModules.sheafification
    (R := restrictedRing (J₀ := J₀) F A) (𝟙 _)
  T.map (scalarRawIso (J₀ := J₀) F φ₀ M).hom ≫
    restrictionSheafify (J₀ := J₀) F A (changeOfRingsPresheafOfUniverses φ₀ M)

private theorem scalarBackHom_eq
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    scalarBackHom (J₀ := J₀) F φ₀ M =
      (PresheafOfModules.sheafification
        (R := restrictedRing (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)) (𝟙 _)).map
        (scalarRawIso (J₀ := J₀) F φ₀ M).hom ≫
        restrictionSheafify (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)
          (changeOfRingsPresheafOfUniverses φ₀ M) := rfl

attribute [local irreducible] scalarBackHom

private theorem scalarBackHom_pure
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀))
    (X : C₀ᵒᵖ) (s : S₀.obj.obj (F.op.obj X)) (x : M.val.obj (F.op.obj X)) :
    (scalarBackHom (J₀ := J₀) F φ₀ M).val.app X
        (scalarExtensionSection ((pullRing (J₀ := J₀) F).map φ₀)
          ((moduleRestrictionF (J₀ := J₀) F
            ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) X s x) =
      scalarExtensionSection φ₀ M (F.op.obj X) s x := by
  let A := (sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀
  let P := changeOfRingsPresheafOfUniverses φ₀ M
  let Q := changeOfRingsPresheafOfUniverses ((pullRing (J₀ := J₀) F).map φ₀)
    ((moduleRestrictionF (J₀ := J₀) F
      ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M)
  let b := PresheafOfModules.sheafificationAdjunction (R := restrictedRing (J₀ := J₀) F A)
    (𝟙 _)
  have hn := b.unit.naturality (scalarRawIso (J₀ := J₀) F φ₀ M).hom
  have hu := restrictionSheafify_unit (J₀ := J₀) (K₀ := K₀) F A P
  have hn' := congrArg (fun t ↦ t.app X
    (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x)) hn
  change (toSheafify J₀ ((rawRestriction (J₀ := J₀) F A).obj P).presheaf).app X
      ((scalarRawIso (J₀ := J₀) F φ₀ M).hom.app X
        (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x)) = _ at hn'
  rw [scalarRawIso_pure] at hn'
  have hu' := congrArg (fun t ↦ t.app X
    (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x)) hu
  have hn'' := congrArg (fun z ↦ (restrictionSheafify (J₀ := J₀) F A P).val.app X z) hn'
  change (scalarBackHom (J₀ := J₀) F φ₀ M).val.app X
      (scalarExtensionSection _ _ X s x) = _
  rw [scalarBackHom_eq]
  change (restrictionSheafify (J₀ := J₀) F A P).val.app X
    (((PresheafOfModules.sheafification (𝟙 _)).map (scalarRawIso (J₀ := J₀) F φ₀ M).hom).val.app X
      (scalarExtensionSection ((pullRing (J₀ := J₀) F).map φ₀) _ X s x)) = _
  exact hn''.symm.trans hu'

private theorem scalarBackHom_natural
    {M N : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)}
    (g : M ⟶ N) :
    changeOfRingsHomOfUniverses ((pullRing (J₀ := J₀) F).map φ₀) _
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).map g) ≫
        (scalarBackHom (J₀ := J₀) F φ₀ N) =
      (scalarBackHom (J₀ := J₀) F φ₀ M) ≫
        (moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).map
            (changeOfRingsHomOfUniverses φ₀ M g) := by
  apply scalarExtension_hom_ext
  intro X s x
  change (scalarBackHom (J₀ := J₀) F φ₀ N).val.app X
      ((changeOfRingsHomOfUniverses _ _ _).val.app X
        (scalarExtensionSection _ _ X s x)) =
    (changeOfRingsHomOfUniverses φ₀ M g).val.app (F.op.obj X)
      ((scalarBackHom (J₀ := J₀) F φ₀ M).val.app X (scalarExtensionSection _ _ X s x))
  rw [scalarExtension_map_tmul, scalarBackHom_pure, scalarBackHom_pure,
    scalarExtension_map_tmul]
  rfl

private theorem scalarBackHom_isIso
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    IsIso (scalarBackHom (J₀ := J₀) F φ₀ M) := by
  let := restrictionSheafify_isIso (J₀ := J₀) F
    ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)
      (changeOfRingsPresheafOfUniverses φ₀ M)
  change IsIso (scalarBackHom (J₀ := J₀) F φ₀ M)
  rw [scalarBackHom_eq]
  change IsIso
    ((PresheafOfModules.sheafification
      (R := restrictedRing (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)) (𝟙 _)).map
      (scalarRawIso (J₀ := J₀) F φ₀ M).hom ≫
      restrictionSheafify (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)
        (changeOfRingsPresheafOfUniverses φ₀ M))
  infer_instance

private def scalarBackIso
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    changeOfRingsOfUniverses ((pullRing (J₀ := J₀) F).map φ₀)
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) ≅
      (moduleRestrictionF (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).obj
          (changeOfRingsOfUniverses φ₀ M) := by
  letI := scalarBackHom_isIso (J₀ := J₀) F φ₀ M
  exact asIso (scalarBackHom (J₀ := J₀) F φ₀ M)

private theorem scalarBackIso_natural
    {M N : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)}
    (g : M ⟶ N) :
    changeOfRingsHomOfUniverses ((pullRing (J₀ := J₀) F).map φ₀) _
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).map g) ≫
        (scalarBackIso (J₀ := J₀) F φ₀ N).hom =
      (scalarBackIso (J₀ := J₀) F φ₀ M).hom ≫
        (moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).map
            (changeOfRingsHomOfUniverses φ₀ M g) := by
  exact scalarBackHom_natural (J₀ := J₀) F φ₀ g

attribute [local irreducible] scalarBackIso

private def scalarExtensionF {D₁ : Type*} [Category D₁] {K₁ : GrothendieckTopology D₁}
    [K₁.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K₁.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify K₁ AddCommGrpCat.{r}]
    {R₁ S₁ : Sheaf K₁ CommRingCat.{r}} (ψ : R₁ ⟶ S₁) :
    SheafOfModules.{r} ((sheafCompose K₁ (forget₂ CommRingCat RingCat)).obj R₁) ⥤
      SheafOfModules.{r} ((sheafCompose K₁ (forget₂ CommRingCat RingCat)).obj S₁) where
  obj M := changeOfRingsOfUniverses ψ M
  map f := changeOfRingsHomOfUniverses ψ _ f
  map_id M := scalarExtension_map_id ψ M
  map_comp f g := scalarExtension_map_comp ψ f g

private def scalarRestrictionIso :
    moduleRestrictionF (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀) ⋙
      scalarExtensionF ((pullRing (J₀ := J₀) F).map φ₀) ≅
    scalarExtensionF φ₀ ⋙ moduleRestrictionF (J₀ := J₀) F
      ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀) :=
  NatIso.ofComponents (fun M ↦ scalarBackIso (J₀ := J₀) F φ₀ M)
    (fun g ↦ scalarBackIso_natural (J₀ := J₀) F φ₀ g)

end RestrictionComparison

variable [∀ W : C, (J.over W).HasSheafCompose
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
  [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [∀ W : C, HasWeakSheafify (J.over W) AddCommGrpCat.{max c v u}]

attribute [local semireducible] ordinaryExtension canonicalExtension

end SheafOfModules.StrictScalarHom
