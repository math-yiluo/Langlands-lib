/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteGlobalPresentationInternalHomColimit
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Internal Hom from a locally finitely presented module on a site

Source: Stacks Project, Modules on Sites, Tag 0GMZ, restriction and the local reduction
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u + 1})
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

private theorem over_preserves_colimits (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{u + 1}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (I : Type (u + 1)) [SmallCategory I] :
    PreservesColimitsOfShape I (overFunctor.{u + 1} R U) := by
  have : PreservesColimitsOfShape I (toSheaf.{u + 1} R) :=
    ((moduleSheaves_colimits_forgetful R).2.2.2.2.2 I).2.1
  have : PreservesColimitsOfShape I
      ((Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{u + 1} (J.over U) J) :=
    ((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (J.over U) J).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape I
      (overFunctor.{u + 1} R U ⋙ toSheaf.{u + 1} (R.over U)) :=
    inferInstanceAs (PreservesColimitsOfShape I
      (toSheaf.{u + 1} R ⋙
        (Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{u + 1} (J.over U) J))
  have : PreservesColimitsOfShape I (toSheaf.{u + 1} (R.over U)) :=
    ((moduleSheaves_colimits_forgetful (R.over U)).2.2.2.2.2 I).2.1
  have : ReflectsColimitsOfShape I (toSheaf.{u + 1} (R.over U)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (toSheaf.{u + 1} (R.over U))

set_option backward.isDefEq.respectTransparency false in
omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private theorem isIso_of_over_cover {κ : Type*} (X : κ → C) (hX : J.CoversTop X)
    {M N : SheafOfModules.{u + 1} R} (f : M ⟶ N)
    (hf : ∀ i, IsIso (f.over (X i))) : IsIso f := by
  let g := (toSheaf R).map f
  have hinj (i : κ) (W : C) (a : W ⟶ X i) : Function.Injective (f.val.app (op W)) := by
    have : IsIso (f.over (X i)) := hf i
    exact (ConcreteCategory.isIso_iff_bijective
      ((evaluation (R.over (X i)) (op (Over.mk a))).map (f.over (X i)))).mp
        inferInstance |>.1
  have hsurj (i : κ) (W : C) (a : W ⟶ X i) : Function.Surjective (f.val.app (op W)) := by
    have : IsIso (f.over (X i)) := hf i
    exact (ConcreteCategory.isIso_iff_bijective
      ((evaluation (R.over (X i)) (op (Over.mk a))).map (f.over (X i)))).mp
        inferInstance |>.2
  have : Presheaf.IsLocallyInjective J g.hom := ⟨fun {W} s t h ↦ by
    apply J.superset_covering _ (hX W.unop)
    rintro Z a ⟨i, ⟨b⟩⟩
    apply hinj i Z b
    change f.val.app (op Z) (M.val.map a.op s) =
      f.val.app (op Z) (M.val.map a.op t)
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
    exact congrArg (N.val.map a.op) h⟩
  have : Presheaf.IsLocallySurjective J g.hom := ⟨fun {W} s ↦ by
    apply J.superset_covering _ (hX W)
    rintro Z a ⟨i, ⟨b⟩⟩
    exact hsurj i Z b (N.val.map a.op s)⟩
  have : IsIso g := (Sheaf.isLocallyBijective_iff_isIso g).mp ⟨inferInstance, inferInstance⟩
  exact isIso_of_reflects_iso f (toSheaf R)

section CommRing
variable (A : Sheaf J CommRingCat.{u + 1})
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]

set_option hygiene false in
local notation "𝓐" => (sheafCompose J (forget₂ CommRingCat RingCat.{u + 1})).obj A

private noncomputable def over_val_iso (M : SheafOfModules.{u + 1} 𝓐) (U : C) :
    (M.over U).val ≅ (PresheafOfModules.restrictOver A.obj U).obj M.val :=
  PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by intro W W' f; rfl)

private noncomputable def over_hom_iso (M N : SheafOfModules.{u + 1} 𝓐) (U : C) :
    (homObj M N).over U ≅ homObj (R := A.over U) (M.over U) (N.over U) :=
  (fullyFaithfulForget _).preimageIso <|
    over_val_iso A (homObj M N) U ≪≫
    PresheafOfModules.restrictOverHomObjIso (R := A.obj) M.val N.val U ≪≫
    ((PresheafOfModules.homFunctor ((Over.forget U).op ⋙ A.obj)).mapIso
      (over_val_iso A M U).op).app _ ≪≫
    ((PresheafOfModules.homFunctor ((Over.forget U).op ⋙ A.obj)).obj
      (op (M.over U).val)).mapIso (over_val_iso A N U).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def over_hom_functor_iso (M : SheafOfModules.{u + 1} 𝓐) (U : C) :
    (homFunctor A).obj (op M) ⋙ overFunctor 𝓐 U ≅
      overFunctor 𝓐 U ⋙ (homFunctor (A.over U)).obj (op (M.over U)) :=
  NatIso.ofComponents
    (F := (homFunctor A).obj (op M) ⋙ overFunctor 𝓐 U)
    (G := overFunctor 𝓐 U ⋙ (homFunctor (A.over U)).obj (op (M.over U)))
    (fun N ↦ over_hom_iso A M N U) (by
    intro N N' f
    apply hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    rfl)

private theorem hom_preserves_colimit_of_cover
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u + 1}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {κ : Type*} (X : κ → C) (hX : J.CoversTop X)
    (P : SheafOfModules.{u + 1} 𝓐)
    (I : Type (u + 1)) [SmallCategory I]
    (N : I ⥤ SheafOfModules.{u + 1} 𝓐)
    (h : ∀ i, PreservesColimit (N ⋙ overFunctor 𝓐 (X i))
      ((homFunctor (A.over (X i))).obj (op (P.over (X i))))) :
    PreservesColimit N ((homFunctor A).obj (op P)) := by
  let H := (homFunctor A).obj (op P)
  have hi : IsIso (colimit.post N H) := by
    apply isIso_of_over_cover 𝓐 X hX
    intro i
    let U := overFunctor 𝓐 (X i)
    have : PreservesColimitsOfShape I U := over_preserves_colimits 𝓐 (X i) I
    have : PreservesColimit (N ⋙ U)
        ((homFunctor (A.over (X i))).obj (op (P.over (X i)))) := h i
    have : PreservesColimit N
        (U ⋙ (homFunctor (A.over (X i))).obj (op (P.over (X i)))) := inferInstance
    have : PreservesColimit N (H ⋙ U) :=
      preservesColimit_of_natIso N (over_hom_functor_iso A P (X i)).symm
    have : IsIso (colimit.post (N ⋙ H) U ≫ U.map (colimit.post N H)) := by
      rw [colimit.post_post]
      infer_instance
    exact IsIso.of_isIso_comp_left (colimit.post (N ⋙ H) U) _
  exact preservesColimit_of_isIso_post H N

end CommRing

/-- Internal Hom from a locally finitely presented sheaf preserves filtered colimits.

Source: Stacks Project, Modules on Sites, Tag 0GMZ, first paragraph of the proof.
(auxiliary; not a blueprint node)

Proof: Choose the covering family and finite presentations supplied by finite
presentation. Slice restriction preserves colimits, and its comparison with internal
Hom is natural in the target, via the equivalence between iterated slice categories.
On each member of the family the assertion is the finite global presentation case.
The colimit comparison is therefore an isomorphism on every member of the family.
These restrictions jointly detect isomorphisms: any section of the target lifts on
the covering sieve of objects mapping into the family, and equal images in the
source agree there. Thus the underlying sheaf map is locally bijective and is an
isomorphism. The module forgetful functor reflects this isomorphism.
-/
theorem internalHom_preserves_filteredColimit_of_isFinitePresentation
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u + 1}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [∀ U W, HasSheafify ((J.over U).over W) AddCommGrpCat.{u + 1}]
    [∀ U W, ((J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [∀ U, (J.over U).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    (A : Sheaf J CommRingCat.{u + 1})
    (P : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u + 1})).obj A))
    [P.IsFinitePresentation]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (N : I ⥤ SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u + 1})).obj A)) :
    PreservesColimit N ((homFunctor A).obj (op P)) := by
  obtain ⟨q, hq⟩ := IsFinitePresentation.exists_quasicoherentData P
  have : q.IsFinitePresentation := hq
  apply hom_preserves_colimit_of_cover A q.X q.coversTop P I N
  intro i
  exact internalHom_preserves_filteredColimit_of_finitePresentation
    (A.over (q.X i)) (P.over (q.X i)) (q.presentation i) I
      (N ⋙ overFunctor
        ((sheafCompose J (forget₂ CommRingCat RingCat.{u + 1})).obj A) (q.X i))

end SheafOfModules
