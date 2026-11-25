/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Signed.SignedLinePullbackNormalization
public import WeilConjectures.Algebra.Homology.Finite.FiniteFreeDualPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import WeilConjectures.Algebra.Homology.RingedSitePullback.PullbackLocalizationOfUniverses
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Existence of normalized signed line pullbacks

Source: Stacks Project, Modules on Sites, Tags 03EL, 0GMX and 04J0.
(blueprint: lem-pur-normalized-signed-line-pullback-exists)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

set_option allowUnsafeReducibility true in
attribute [local reducible] siteSheafTensorRight siteTensorRight
  SheafOfModules.forget siteSheafTensorSecondMap
  SheafOfModules.overFunctor PresheafOfModules.restrictOver
  Functor.sheafPushforwardContinuous Over.forget
  sheafCompose SheafOfModules.unit
  PresheafOfModules.unit SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

attribute [local irreducible] pullback pullbackPushforwardAdjunction
  Functor.leftAdjoint Functor.rightAdjoint

@[irreducible] private noncomputable def tensorIso
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify H AddCommGrpCat.{w}]
    {A : Sheaf H CommRingCat.{w}}
    {M M' N N' : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A)}
    (f : M ≅ M') (g : N ≅ N') :
    (siteSheafTensorRight N).obj M ≅ (siteSheafTensorRight N').obj M' := by
  let raw : siteTensorPresheaf M.val N.val ≅ siteTensorPresheaf M'.val N'.val :=
    { hom := siteTensorHom f.hom.val N.val ≫ siteTensorSecondMap M'.val g.hom.val
      inv := siteTensorHom f.inv.val N'.val ≫ siteTensorSecondMap M.val g.inv.val
      hom_inv_id := by
        ext X : 1
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro x y
        change f.inv.val.app X (f.hom.val.app X x) ⊗ₜ[A.obj.obj X]
          g.inv.val.app X (g.hom.val.app X y) = x ⊗ₜ[A.obj.obj X] y
        have hf := congrArg (fun t ↦ t.val.app X x) f.hom_inv_id
        have hg := congrArg (fun t ↦ t.val.app X y) g.hom_inv_id
        exact congrArg₂ (fun a b ↦ a ⊗ₜ[A.obj.obj X] b) hf hg
      inv_hom_id := by
        ext X : 1
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro x y
        change f.hom.val.app X (f.inv.val.app X x) ⊗ₜ[A.obj.obj X]
          g.hom.val.app X (g.inv.val.app X y) = x ⊗ₜ[A.obj.obj X] y
        have hf := congrArg (fun t ↦ t.val.app X x) f.inv_hom_id
        have hg := congrArg (fun t ↦ t.val.app X y) g.inv_hom_id
        exact congrArg₂ (fun a b ↦ a ⊗ₜ[A.obj.obj X] b) hf hg }
  exact (PresheafOfModules.sheafification (𝟙 _)).mapIso raw

private theorem tensorIso_hom
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify H AddCommGrpCat.{w}]
    {A : Sheaf H CommRingCat.{w}}
    {M M' N N' : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A)}
    (f : M ≅ M') (g : N ≅ N') :
    (tensorIso f g).hom =
      (siteSheafTensorRight N).map f.hom ≫ siteSheafTensorSecondMap M' g.hom := by
  unfold tensorIso
  exact (PresheafOfModules.sheafification (𝟙 _)).map_comp _ _

@[irreducible] private noncomputable def tensorMapBoth
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify H AddCommGrpCat.{w}]
    {A : Sheaf H CommRingCat.{w}}
    {M M' N N' : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (siteSheafTensorRight N).obj M ⟶ (siteSheafTensorRight N').obj M' :=
  (siteSheafTensorRight N).map f ≫ siteSheafTensorSecondMap M' g

private theorem tensorMaps_isIso
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify H AddCommGrpCat.{w}]
    {A : Sheaf H CommRingCat.{w}}
    {M M' N N' : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A)}
    (f : M ⟶ M') (g : N ⟶ N') [IsIso f] [IsIso g] :
    IsIso (tensorMapBoth f g) := by
  unfold tensorMapBoth
  change IsIso ((siteSheafTensorRight N).map (asIso f).hom ≫
    siteSheafTensorSecondMap M' (asIso g).hom)
  rw [← tensorIso_hom]
  infer_instance

private theorem tensorMapBoth_pure
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify H AddCommGrpCat.{w}]
    {A : Sheaf H CommRingCat.{w}}
    {M M' N N' : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A)}
    (f : M ⟶ M') (g : N ⟶ N') (X : Eᵒᵖ)
    (x : M.val.obj X) (y : N.val.obj X) :
    (tensorMapBoth f g).val.app X (siteSheafTensorTmul M N X x y) =
      siteSheafTensorTmul M' N' X (f.val.app X x) (g.val.app X y) := by
  unfold tensorMapBoth
  change (siteSheafTensorSecondMap M' g).val.app X
    (((siteSheafTensorRight N).map f).val.app X _) = _
  rw [scalarTensor_first_tmul, scalarTensor_second_tmul]

private theorem tensorIso_pure
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify H AddCommGrpCat.{w}]
    {A : Sheaf H CommRingCat.{w}}
    {M M' N N' : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A)}
    (f : M ≅ M') (g : N ≅ N') (X : Eᵒᵖ)
    (x : M.val.obj X) (y : N.val.obj X) :
    (tensorIso f g).hom.val.app X (siteSheafTensorTmul M N X x y) =
      siteSheafTensorTmul M' N' X (f.hom.val.app X x) (g.hom.val.app X y) := by
  rw [tensorIso_hom]
  change (siteSheafTensorSecondMap M' g.hom).val.app X
    (((siteSheafTensorRight N).map f.hom).val.app X _) = _
  rw [scalarTensor_first_tmul, scalarTensor_second_tmul]

@[irreducible] private noncomputable def overTensorIso
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify H AddCommGrpCat.{max u v w}]
    (A : Sheaf H CommRingCat.{max u v w}) (V : E)
    [(H.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify (H.over V) AddCommGrpCat.{max u v w}]
    (M N : SheafOfModules.{max u v w} ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A)) :
    ((siteSheafTensorRight N).obj M).over V ≅
      (siteSheafTensorRight (A := A.over V) (N.over V)).obj (M.over V) :=
  (exists_localizedSiteTensorRestriction.{u, v, max u v w, max u v w}
    H A V).choose M N

private theorem overTensorIso_pure
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify H AddCommGrpCat.{max u v w}]
    (A : Sheaf H CommRingCat.{max u v w}) (V : E)
    [(H.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify (H.over V) AddCommGrpCat.{max u v w}]
    (M N : SheafOfModules.{max u v w} ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A))
    (T : Over V) (x : M.val.obj (op T.left)) (y : N.val.obj (op T.left)) :
    (overTensorIso A V M N).hom.val.app (op T)
      (siteSheafTensorTmul M N (op T.left) x y) =
      siteSheafTensorTmul (A := A.over V) (M.over V) (N.over V) (op T) x y := by
  unfold overTensorIso
  exact (exists_localizedSiteTensorRestriction.{u, v, max u v w, max u v w}
    H A V).choose_spec.2 M N T x y

private theorem overTensorIso_inv_pure
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify H AddCommGrpCat.{max u v w}]
    (A : Sheaf H CommRingCat.{max u v w}) (V : E)
    [(H.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify (H.over V) AddCommGrpCat.{max u v w}]
    (M N : SheafOfModules.{max u v w} ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A))
    (T : Over V) (x : M.val.obj (op T.left)) (y : N.val.obj (op T.left)) :
    (overTensorIso A V M N).inv.val.app (op T)
      (siteSheafTensorTmul (A := A.over V) (M.over V) (N.over V) (op T) x y) =
      siteSheafTensorTmul M N (op T.left) x y := by
  rw [← overTensorIso_pure A V M N T x y]
  exact congrArg (fun f ↦ f.val.app (op T)
    (siteSheafTensorTmul M N (op T.left) x y)) (overTensorIso A V M N).hom_inv_id

@[irreducible] private noncomputable def dualIso
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
    {A : Sheaf H CommRingCat.{max u v w}}
    {M N : SheafOfModules.{max u v w}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A)} (e : M ≅ N) :
    homObj M (unit _) ≅ homObj N (unit _) :=
  ((homFunctor A).mapIso e.symm.op).app (unit _)

private theorem dualIso_hom
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
    {A : Sheaf H CommRingCat.{max u v w}}
    {M N : SheafOfModules.{max u v w}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A)} (e : M ≅ N) :
    (dualIso e).hom = homObjMap e.inv (𝟙 _) := by
  unfold dualIso
  rfl

@[irreducible] private noncomputable def powerOverIso
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify H AddCommGrpCat.{max u v w}]
    (A : Sheaf H CommRingCat.{max u v w}) (V : E)
    [(H.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify (H.over V) AddCommGrpCat.{max u v w}]
    (M : SheafOfModules.{max u v w} ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A))
    (e : M.over V ≅ unit (((sheafCompose H (forget₂ CommRingCat RingCat)).obj A).over V)) :
    ∀ n : ℕ, (scalarTensorPower A M n).over V ≅
      unit (((sheafCompose H (forget₂ CommRingCat RingCat)).obj A).over V)
  := fun n ↦ Nat.rec (motive := fun n ↦
      (scalarTensorPower A M n).over V ≅
        unit (((sheafCompose H (forget₂ CommRingCat RingCat)).obj A).over V))
    (Iso.refl _) (fun n ih ↦ match n with
      | 0 => e
      | n + 1 => overTensorIso A V (scalarTensorPower A M (n + 1)) M ≪≫
          tensorIso ih e ≪≫ scalarTensorRightUnitor (A.over V) (unit _)) n

section GenericTensorPullback

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}]

section TensorPullback

variable {R : Sheaf J CommRingCat.{w}}
  {S : Sheaf K CommRingCat.{w}}
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  [hAdjTensor : (pushforward.{w} a).IsRightAdjoint]

@[irreducible] private noncomputable def tensorPullbackRaw
    (M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    siteTensorPresheaf M.val N.val ⟶
      ((pushforward a).obj ((siteSheafTensorRight ((pullback a).obj N)).obj
        ((pullback a).obj M))).val where
  app X := by
    let η := (pullbackPushforwardAdjunction a).unit
    let T := (siteSheafTensorRight ((pullback a).obj N)).obj ((pullback a).obj M)
    refine ModuleCat.ofHom (Y := ((pushforward a).obj T).val.obj X)
      (TensorProduct.lift (LinearMap.mk₂ (R.obj.obj X)
      (fun (x : M.val.obj X) (y : N.val.obj X) ↦
        siteSheafTensorTmul ((pullback a).obj M) ((pullback a).obj N)
        (U.op.obj X) ((η.app M).val.app X x) ((η.app N).val.app X y))
      ?_ ?_ ?_ ?_))
    · intro x y z
      simp only [map_add, scalarTensorTmul_add_first]
    · intro r x y
      have h := ((η.app M).val.app X).hom.map_smul r x
      change (η.app M).val.app X (r • x) =
        (show S.obj.obj (U.op.obj X) from a.hom.app X r) •
          (show ((pullback a).obj M).val.obj (U.op.obj X) from
          (η.app M).val.app X x) at h
      rw [h, scalarTensorTmul_smul_first]
      rfl
    · intro x y z
      simp only [map_add, siteSheafTensorTmul, TensorProduct.tmul_add]
    · intro r x y
      have h := ((η.app N).val.app X).hom.map_smul r y
      change (η.app N).val.app X (r • y) =
        (show S.obj.obj (U.op.obj X) from a.hom.app X r) •
          (show ((pullback a).obj N).val.obj (U.op.obj X) from
          (η.app N).val.app X y) at h
      rw [h, scalarTensorTmul_smul_second]
      rfl
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change siteSheafTensorTmul ((pullback a).obj M) ((pullback a).obj N) (U.op.obj Y)
        (((pullbackPushforwardAdjunction a).unit.app M).val.app Y (M.val.map f x))
        (((pullbackPushforwardAdjunction a).unit.app N).val.app Y (N.val.map f y)) =
      ((siteSheafTensorRight ((pullback a).obj N)).obj ((pullback a).obj M)).val.map
        (U.op.map f) (siteSheafTensorTmul _ _ (U.op.obj X)
          (((pullbackPushforwardAdjunction a).unit.app M).val.app X x)
          (((pullbackPushforwardAdjunction a).unit.app N).val.app X y))
    rw [scalarTensorTmul_naturality]
    congr 1
    · exact PresheafOfModules.naturality_apply
        ((pullbackPushforwardAdjunction a).unit.app M).val f x
    · exact PresheafOfModules.naturality_apply
        ((pullbackPushforwardAdjunction a).unit.app N).val f y

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
private theorem tensorPullbackRaw_pure
    (M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (X : Cᵒᵖ) (x : M.val.obj X) (y : N.val.obj X) :
    (tensorPullbackRaw a M N).app X (x ⊗ₜ[R.obj.obj X] y) =
      siteSheafTensorTmul ((pullback a).obj M) ((pullback a).obj N) (U.op.obj X)
        (((pullbackPushforwardAdjunction a).unit.app M).val.app X x)
        (((pullbackPushforwardAdjunction a).unit.app N).val.app X y) := by
  unfold tensorPullbackRaw
  rfl

@[irreducible] private noncomputable def tensorPullback
    (M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (pullback a).obj ((siteSheafTensorRight N).obj M) ⟶
      (siteSheafTensorRight ((pullback a).obj N)).obj ((pullback a).obj M) :=
  ((pullbackPushforwardAdjunction a).homEquiv
      ((siteSheafTensorRight N).obj M)
      ((siteSheafTensorRight ((pullback a).obj N)).obj ((pullback a).obj M))).symm
    ((PresheafOfModules.sheafificationHomEquiv
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (R₀ := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj) (𝟙 _)
      (P := siteTensorPresheaf M.val N.val)
      (F := (pushforward a).obj ((siteSheafTensorRight ((pullback a).obj N)).obj
        ((pullback a).obj M)))).symm (tensorPullbackRaw a M N))

private theorem tensorPullback_pure
    (M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : C) (x : M.val.obj (op V)) (y : N.val.obj (op V)) :
    (tensorPullback a M N).val.app (op (U.obj V))
      (((pullbackPushforwardAdjunction a).unit.app
        ((siteSheafTensorRight N).obj M)).val.app (op V)
          (siteSheafTensorTmul M N (op V) x y)) =
      siteSheafTensorTmul ((pullback a).obj M) ((pullback a).obj N) (op (U.obj V))
        (((pullbackPushforwardAdjunction a).unit.app M).val.app (op V) x)
        (((pullbackPushforwardAdjunction a).unit.app N).val.app (op V) y) := by
  let t := (PresheafOfModules.sheafificationHomEquiv
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (R₀ := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj) (𝟙 _)
      (P := siteTensorPresheaf M.val N.val)
    (F := (pushforward a).obj ((siteSheafTensorRight ((pullback a).obj N)).obj
      ((pullback a).obj M)))).symm (tensorPullbackRaw a M N)
  have h : (pullbackPushforwardAdjunction a).homEquiv
      ((siteSheafTensorRight N).obj M)
      ((siteSheafTensorRight ((pullback a).obj N)).obj ((pullback a).obj M))
      (tensorPullback a M N) = t := by
    unfold tensorPullback
    exact ((pullbackPushforwardAdjunction a).homEquiv
      ((siteSheafTensorRight N).obj M)
      ((siteSheafTensorRight ((pullback a).obj N)).obj ((pullback a).obj M))).apply_symm_apply t
  rw [Adjunction.homEquiv_unit] at h
  have hs := congrArg (fun f ↦
    PresheafOfModules.sheafificationHomEquiv
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (R₀ := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj) (𝟙 _)
      (P := siteTensorPresheaf M.val N.val)
      (F := (pushforward a).obj ((siteSheafTensorRight ((pullback a).obj N)).obj
        ((pullback a).obj M))) f) h
  dsimp only [t] at hs
  erw [Equiv.apply_symm_apply] at hs
  exact (congrArg (fun f ↦ f.app (op V) (x ⊗ₜ[R.obj.obj (op V)] y)) hs).trans
    (tensorPullbackRaw_pure a M N (op V) x y)

set_option allowUnsafeReducibility true in
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
  siteSheafTensorRight siteSheafTensorTmul siteSheafTensorSecondMap

omit [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}] in
private theorem pullback_tensor_ext
    (M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {H : SheafOfModules.{w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)}
    (f g : (pullback a).obj ((siteSheafTensorRight N).obj M) ⟶ H)
    (h : ∀ (V : C) (x : M.val.obj (op V)) (y : N.val.obj (op V)),
      f.val.app (op (U.obj V))
        (((pullbackPushforwardAdjunction a).unit.app
          ((siteSheafTensorRight N).obj M)).val.app (op V)
            (siteSheafTensorTmul M N (op V) x y)) =
      g.val.app (op (U.obj V))
        (((pullbackPushforwardAdjunction a).unit.app
          ((siteSheafTensorRight N).obj M)).val.app (op V)
            (siteSheafTensorTmul M N (op V) x y))) : f = g := by
  apply ((pullbackPushforwardAdjunction a).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply scalarTensor_hom_ext M N
  intro V x y
  exact h V.unop x y

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}] in
private theorem pullback_unit_pure (V : C) (r : R.obj.obj (op V)) :
    (pullbackObjUnitToUnit a).val.app (op (U.obj V))
      (((pullbackPushforwardAdjunction a).unit.app (unit _)).val.app (op V) r) =
      a.hom.app (op V) r := by
  have h := pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit a
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun f ↦ f.val.app (op V) r) h

private theorem tensorPullback_naturality
    {M M' N N' : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ≅ M') (g : N ≅ N') :
    (pullback a).map (tensorIso f g).hom ≫ tensorPullback a M' N' =
      tensorPullback a M N ≫ (tensorIso ((pullback a).mapIso f)
        ((pullback a).mapIso g)).hom := by
  apply pullback_tensor_ext a M N
  intro V x y
  have hn := (pullbackPushforwardAdjunction a).unit.naturality (tensorIso f g).hom
  have he := congrArg (fun t ↦ t.val.app (op V) (siteSheafTensorTmul M N (op V) x y)) hn
  change (((pullbackPushforwardAdjunction a).unit.app _).val.app (op V)
      ((tensorIso f g).hom.val.app (op V) (siteSheafTensorTmul M N (op V) x y))) =
    ((pullback a).map (tensorIso f g).hom).val.app (op (U.obj V))
      (((pullbackPushforwardAdjunction a).unit.app _).val.app (op V)
        (siteSheafTensorTmul M N (op V) x y)) at he
  change (tensorPullback a M' N').val.app (op (U.obj V)) _ = _
  erw [← he]
  rw [tensorIso_pure, tensorPullback_pure]
  change _ = (tensorIso _ _).hom.val.app (op (U.obj V))
    ((tensorPullback a M N).val.app (op (U.obj V)) _)
  rw [tensorPullback_pure, tensorIso_pure]
  congr 1
  · exact congrArg (fun t ↦ t.val.app (op V) x)
      ((pullbackPushforwardAdjunction a).unit.naturality f.hom)
  · exact congrArg (fun t ↦ t.val.app (op V) y)
      ((pullbackPushforwardAdjunction a).unit.naturality g.hom)

private theorem tensorPullback_unit_isIso
    [HasFiniteLimits C] [PreservesFiniteLimits U]
    (M : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    IsIso (tensorPullback a M (unit _)) := by
  let e := tensorIso (Iso.refl ((pullback a).obj M)) (asIso (pullbackObjUnitToUnit a))
  have h : tensorPullback a M (unit _) ≫ e.hom ≫
      (scalarTensorRightUnitor S ((pullback a).obj M)).hom =
      (pullback a).map (scalarTensorRightUnitor R M).hom := by
    apply pullback_tensor_ext a M (unit _)
    intro V x r
    change (scalarTensorRightUnitor S ((pullback a).obj M)).hom.val.app _
      (e.hom.val.app _ ((tensorPullback a M (unit _)).val.app _ _)) = _
    rw [tensorPullback_pure]
    dsimp only [e]
    rw [tensorIso_pure]
    simp only [asIso_hom, Iso.refl_hom, id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply]
    rw [pullback_unit_pure]
    rw [scalarTensorRightUnitor_tmul]
    have hn := congrArg (fun t ↦ t.val.app (op V)
      (siteSheafTensorTmul M (unit _) (op V) x r))
      ((pullbackPushforwardAdjunction a).unit.naturality (scalarTensorRightUnitor R M).hom)
    change (((pullbackPushforwardAdjunction a).unit.app M).val.app (op V)
      ((scalarTensorRightUnitor R M).hom.val.app (op V)
        (siteSheafTensorTmul M (unit _) (op V) x r))) =
      ((pullback a).map (scalarTensorRightUnitor R M).hom).val.app (op (U.obj V))
        (((pullbackPushforwardAdjunction a).unit.app _).val.app (op V)
          (siteSheafTensorTmul M (unit _) (op V) x r)) at hn
    erw [← hn]
    rw [scalarTensorRightUnitor_tmul]
    exact (((pullbackPushforwardAdjunction a).unit.app M).val.app (op V)).hom.map_smul r x
      |>.symm
  have : IsIso (tensorPullback a M (unit _) ≫ e.hom ≫
      (scalarTensorRightUnitor S ((pullback a).obj M)).hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (e.hom ≫
    (scalarTensorRightUnitor S ((pullback a).obj M)).hom)

private theorem tensorPullback_trivial_isIso
    [HasFiniteLimits C] [PreservesFiniteLimits U]
    (M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (e : N ≅ unit _) : IsIso (tensorPullback a M N) := by
  have := tensorPullback_unit_isIso a M
  have h := tensorPullback_naturality a (Iso.refl M) e
  have : IsIso (tensorPullback a M N ≫
      (tensorIso ((pullback a).mapIso (Iso.refl M)) ((pullback a).mapIso e)).hom) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right (tensorPullback a M N)
    (tensorIso ((pullback a).mapIso (Iso.refl M)) ((pullback a).mapIso e)).hom

end TensorPullback
end GenericTensorPullback

set_option allowUnsafeReducibility true in
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
  siteSheafTensorRight siteSheafTensorTmul siteSheafTensorSecondMap

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]

section TensorPullback

variable {R : Sheaf J CommRingCat.{max u v w}}
  {S : Sheaf K CommRingCat.{max u v w}}
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  [(pushforward.{max u v w} a).IsRightAdjoint]

set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] RingedSitePullback.localComparison
set_option allowUnsafeReducibility true in
attribute [local semireducible] sheafCompose siteTensorRight SheafOfModules.forget
  SheafOfModules.unit PresheafOfModules.unit Functor.sheafPushforwardContinuous
  Over.forget SheafOfModules.overFunctor
  PresheafOfModules.restrictOver SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

private theorem tensorPullback_local
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (V : C)
    [(Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))]
    [hSliceAdj : (pushforward.{max u v w} (RingedSitePullback.locMap.{u, v, w}
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S) a V)).IsRightAdjoint]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify (J.over V) AddCommGrpCat.{max u v w}]
    [(K.over (U.obj V)).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify (K.over (U.obj V)) AddCommGrpCat.{max u v w}]
    (M N : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (pullback (RingedSitePullback.locMap.{u, v, w}
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S) a V)).map
      (overTensorIso R V M N).inv ≫
      RingedSitePullback.localComparison.{u, v, w} a V ((siteSheafTensorRight N).obj M) ≫
      (tensorPullback a M N).over (U.obj V) ≫
      (overTensorIso S (U.obj V) ((pullback a).obj M) ((pullback a).obj N)).hom =
    tensorPullback.{max u v, v, max u v w}
        (C := Over V) (D := Over (U.obj V))
        (J := J.over V) (K := K.over (U.obj V)) (U := Over.post U)
        (hAdjTensor := hSliceAdj) (R := R.over V) (S := S.over (U.obj V))
        (RingedSitePullback.locMap.{u, v, w}
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S) a V)
        (M.over V) (N.over V) ≫
      tensorMapBoth (A := S.over (U.obj V))
        (RingedSitePullback.localComparison.{u, v, w} a V M)
        (RingedSitePullback.localComparison.{u, v, w} a V N) := by
  let b := RingedSitePullback.locMap.{u, v, w} a V
  apply pullback_tensor_ext.{max u v, v, max u v w}
    (C := Over V) (D := Over (U.obj V))
    (J := J.over V) (K := K.over (U.obj V)) (U := Over.post U)
    (hAdjTensor := hSliceAdj) (R := R.over V)
    (S := S.over (U.obj V)) b (M.over V) (N.over V)
  intro T x y
  have hn := (pullbackPushforwardAdjunction b).unit.naturality (overTensorIso R V M N).inv
  have he := congrArg (fun f ↦ f.val.app (op T)
    (siteSheafTensorTmul (A := R.over V) (M.over V) (N.over V) (op T) x y)) hn
  change (((pullbackPushforwardAdjunction b).unit.app _).val.app (op T)
      ((overTensorIso R V M N).inv.val.app (op T)
        (siteSheafTensorTmul (A := R.over V) (M.over V) (N.over V) (op T) x y))) =
    ((pullback b).map (overTensorIso R V M N).inv).val.app
      (op ((Over.post U).obj T))
      (((pullbackPushforwardAdjunction b).unit.app _).val.app (op T)
        (siteSheafTensorTmul (A := R.over V) (M.over V) (N.over V) (op T) x y)) at he
  let q := (overTensorIso S (U.obj V) ((pullback a).obj M) ((pullback a).obj N)).hom
  let t := tensorPullback a M N
  let c := RingedSitePullback.localComparison.{u, v, w} a V
    ((siteSheafTensorRight N).obj M)
  let tx := siteSheafTensorTmul M N (op T.left) x y
  have h1 := congrArg (fun z ↦ q.val.app (op ((Over.post U).obj T))
    (t.val.app (op (U.obj T.left)) (c.val.app (op ((Over.post U).obj T)) z))) he.symm
  have h2 := congrArg (fun z ↦ q.val.app (op ((Over.post U).obj T))
    (t.val.app (op (U.obj T.left)) (c.val.app (op ((Over.post U).obj T))
      (((pullbackPushforwardAdjunction b).unit.app
        (((siteSheafTensorRight N).obj M).over V)).val.app (op T) z))))
    (overTensorIso_inv_pure R V M N T x y)
  have h3 := congrArg (fun z ↦ q.val.app (op ((Over.post U).obj T))
    (t.val.app (op (U.obj T.left)) z))
    (RingedSitePullback.localComparison_unit_apply.{u, v, w} a V
      ((siteSheafTensorRight N).obj M) T tx)
  have h4 := congrArg (fun z ↦ q.val.app (op ((Over.post U).obj T)) z)
    (tensorPullback_pure a M N T.left x y)
  have h5 := overTensorIso_pure S (U.obj V) ((pullback a).obj M)
    ((pullback a).obj N) ((Over.post U).obj T)
    (((pullbackPushforwardAdjunction a).unit.app M).val.app (op T.left) x)
    (((pullbackPushforwardAdjunction a).unit.app N).val.app (op T.left) y)
  have hl := h1.trans (h2.trans (h3.trans (h4.trans h5)))
  let cM := RingedSitePullback.localComparison.{u, v, w} a V M
  let cN := RingedSitePullback.localComparison.{u, v, w} a V N
  have r1 := congrArg (fun z ↦ (tensorMapBoth (A := S.over (U.obj V)) cM cN).val.app
    (op ((Over.post U).obj T)) z)
    (tensorPullback_pure.{max u v, v, max u v w}
      (C := Over V) (D := Over (U.obj V))
      (J := J.over V) (K := K.over (U.obj V)) (U := Over.post U)
      (hAdjTensor := hSliceAdj) (R := R.over V) (S := S.over (U.obj V))
      b (M.over V) (N.over V) T x y)
  have r2 := tensorMapBoth_pure (A := S.over (U.obj V)) cM cN
    (op ((Over.post U).obj T))
    (((pullbackPushforwardAdjunction b).unit.app (M.over V)).val.app (op T) x)
    (((pullbackPushforwardAdjunction b).unit.app (N.over V)).val.app (op T) y)
  have r3 := congrArg₂ (fun xx yy ↦ siteSheafTensorTmul (A := S.over (U.obj V))
    (((pullback a).obj M).over (U.obj V)) (((pullback a).obj N).over (U.obj V))
      (op ((Over.post U).obj T)) xx yy)
    (RingedSitePullback.localComparison_unit_apply.{u, v, w} a V M T x)
    (RingedSitePullback.localComparison_unit_apply.{u, v, w} a V N T y)
  exact hl.trans (r1.trans (r2.trans r3)).symm

private theorem tensorPullback_line_isIso
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (hcover : CoverPreserving J K U)
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (M N : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hN : ∃ (I : Type u) (V : I → C), J.CoversTop V ∧
      ∀ i : I, Nonempty (N.over (V i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (V i)))) :
    IsIso (tensorPullback a M N) := by
  classical
  obtain ⟨I, V, hV, e⟩ := hN
  let (V : C) : HasSheafify (J.over V) AddCommGrpCat.{max u v w} :=
    (coefficientSheafification.{max u v, v, max u v w} (J.over V)).1
  let (W : D) : HasSheafify (K.over W) AddCommGrpCat.{max u v w} :=
    (coefficientSheafification.{max u v, v, max u v w} (K.over W)).1
  let (W : D) : (K.over W).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    (coefficientSheafification.{max u v, v, max u v w} (K.over W)).2
  have hcov : K.CoversTop (fun i ↦ U.obj (V i)) := by
    apply (K.coversTop_iff_of_isTerminal (U.obj (⊤_ C))
      ((terminalIsTerminal (C := C)).isTerminalObj U (⊤_ C))
      (fun i ↦ U.obj (V i))).2
    apply K.superset_covering _ (hcover.cover_preserve (hV (⊤_ C)))
    exact Sieve.functorPushforward_ofObjects_le _ _ _
  have hi (i : I) : IsIso ((tensorPullback a M N).over (U.obj (V i))) := by
    let X := V i
    let : (Over.post (X := X) U).IsContinuous (J.over X) (K.over (U.obj X)) :=
      RingedSitePullback.local_continuous hcover X
    let b := RingedSitePullback.locMap.{u, v, w} a X
    have : (pushforward.{max u v w} b).IsRightAdjoint :=
      module_pushforward_isRightAdjoint_of_universes b
    have := tensorPullback_trivial_isIso.{max u v, v, max u v w}
      (C := Over X) (D := Over (U.obj X))
      (J := J.over X) (K := K.over (U.obj X)) (U := Over.post U)
      (R := R.over X) (S := S.over (U.obj X)) b (M.over X) (N.over X) (e i).some
    have : IsIso (RingedSitePullback.localComparison.{u, v, w} a X
        ((siteSheafTensorRight N).obj M)) :=
      RingedSitePullback.localComparison_isIso.{u, v, w} a X _
    have : IsIso (RingedSitePullback.localComparison.{u, v, w} a X N) :=
      RingedSitePullback.localComparison_isIso.{u, v, w} a X N
    have : IsIso (RingedSitePullback.localComparison.{u, v, w} a X M) :=
      RingedSitePullback.localComparison_isIso.{u, v, w} a X M
    have hmaps := tensorMaps_isIso (A := S.over (U.obj X))
      (RingedSitePullback.localComparison.{u, v, w} a X M)
      (RingedSitePullback.localComparison.{u, v, w} a X N)
    have he := tensorPullback_local a X M N
    have : IsIso ((pullback b).map (overTensorIso R X M N).inv ≫
        RingedSitePullback.localComparison.{u, v, w} a X ((siteSheafTensorRight N).obj M) ≫
        (tensorPullback a M N).over (U.obj X) ≫
        (overTensorIso S (U.obj X) ((pullback a).obj M) ((pullback a).obj N)).hom) := by
      rw [he]
      infer_instance
    have : IsIso (RingedSitePullback.localComparison.{u, v, w} a X
        ((siteSheafTensorRight N).obj M) ≫ (tensorPullback a M N).over (U.obj X) ≫
        (overTensorIso S (U.obj X) ((pullback a).obj M) ((pullback a).obj N)).hom) :=
      IsIso.of_isIso_comp_left ((pullback b).map (overTensorIso R X M N).inv) _
    have : IsIso ((tensorPullback a M N).over (U.obj X) ≫
        (overTensorIso S (U.obj X) ((pullback a).obj M) ((pullback a).obj N)).hom) :=
      IsIso.of_isIso_comp_left
        (RingedSitePullback.localComparison.{u, v, w} a X ((siteSheafTensorRight N).obj M)) _
    exact IsIso.of_isIso_comp_right ((tensorPullback a M N).over (U.obj X))
      (overTensorIso S (U.obj X) ((pullback a).obj M) ((pullback a).obj N)).hom
  have : IsIso ((toSheaf _).map (tensorPullback a M N)) := by
    apply Sheaf.isIso_of_coversTop hcov
    intro i
    have := hi i
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    intro T
    exact Functor.map_isIso (forget₂ _ AddCommGrpCat)
      ((evaluation _ T).map ((tensorPullback a M N).over (U.obj (V i))))
  exact isIso_of_reflects_iso (tensorPullback a M N) (toSheaf _)

end TensorPullback

/-- Normalized pullback comparisons for the signed powers of one line.
Source: Stacks Project, Modules on Sites, Tags 03EL, 0GMX, 0FNY and 04J0;
steps 1, 3 and 4 of the signed-line pullback argument.
(blueprint: lem-pur-normalized-signed-line-pullback-exists)

Proof: In degree zero use the coefficient-unit comparison, and in degree one use p.
For n at least one, apply the tensor pullback comparison to the nth power tensor L,
then tensor the preceding comparison with p. The unit and pure-tensor formulas give
exactly the positive recursion. Restricting to a trivializing cover of L shows that
all its positive tensor powers are locally free of rank one. For a negative degree,
apply finite_free_dual_pullback to the corresponding positive power, and compose its
evaluation comparison with precomposition by the inverse positive comparison. Both
factors are invertible. Evaluating against the positive comparison cancels its inverse
and gives the coefficient image of the original evaluation, after every restriction.
Thus the four normalization clauses hold. No scalar square is involved in this result. -/
theorem exists_signedLinePullbackNormalized
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (hcover : CoverPreserving J K U)
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    {R : Sheaf J CommRingCat.{max u v w}} {R' : Sheaf K CommRingCat.{max u v w}}
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (L' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (hL : ∃ (I : Type u) (V : I → C), J.CoversTop V ∧
      ∀ i : I, Nonempty (L.over (V i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (V i))))
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ≅ L') :
    ∃ P : ∀ m : ℤ, (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj
        (signedLinePower.{u, v, w} L m) ≅ signedLinePower.{u, v, w} L' m,
      SignedLinePullbackNormalized a L L' p P := by
  classical
  let := module_pushforward_isRightAdjoint_of_universes a
  let (V : C) : HasSheafify (J.over V) AddCommGrpCat.{max u v w} :=
    (coefficientSheafification.{max u v, v, max u v w} (J.over V)).1
  have ht (M : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
      IsIso (tensorPullback a M L) := tensorPullback_line_isIso a hcover M L hL
  let pos : ∀ n : ℕ,
      (pullback a).obj (scalarTensorPower R L (n + 1)) ≅
        scalarTensorPower R' L' (n + 1) := fun n ↦
    Nat.rec (motive := fun n ↦
      (pullback a).obj (scalarTensorPower R L (n + 1)) ≅
        scalarTensorPower R' L' (n + 1)) p
      (fun n e ↦ by
        have := ht (scalarTensorPower R L (n + 1))
        exact asIso (tensorPullback a (scalarTensorPower R L (n + 1)) L) ≪≫
          tensorIso e p) n
  obtain ⟨hAdj, δ, ⟨hδ, _hnat, hiso⟩, _hunique⟩ := finite_free_dual_pullback a hcover
  have hδiso (n : ℕ) : IsIso (δ (scalarTensorPower R L (n + 1))) := by
    apply hiso
    obtain ⟨I, V, hV, e⟩ := hL
    refine ⟨ULift.{max u v w} I, fun i ↦ V i.down, fun _ ↦ 1, ?_, ?_⟩
    · rw [Sieve.ofArrows_eq_ofObjects terminalIsTerminal]
      apply J.superset_covering _ (hV (⊤_ C))
      rintro T f ⟨i, ⟨g⟩⟩
      exact ⟨ULift.up i, ⟨g⟩⟩
    · intro i
      exact ⟨powerOverIso R (V i.down) L (e i.down).some (n + 1) ≪≫
        (freeUniqueIso (ULift.{max u v w} (Fin 1))).symm⟩
  let neg (n : ℕ) : (pullback a).obj (homObj (scalarTensorPower R L (n + 1)) (unit _)) ≅
      homObj (scalarTensorPower R' L' (n + 1)) (unit _) := by
    have := hδiso n
    exact asIso (δ (scalarTensorPower R L (n + 1))) ≪≫ dualIso (pos n)
  let P : ∀ m : ℤ, (pullback a).obj (signedLinePower.{u, v, w} L m) ≅
      signedLinePower.{u, v, w} L' m
    | .ofNat 0 => asIso (pullbackObjUnitToUnit a)
    | .ofNat (n + 1) => pos n
    | .negSucc n => neg n
  refine ⟨P, ?_, rfl, ?_, ?_⟩
  · intro V r
    exact pullback_unit_pure a V r
  · intro n V x y
    change (tensorIso (pos n) p).hom.val.app (op (U.obj V))
      ((tensorPullback a (scalarTensorPower R L (n + 1)) L).val.app (op (U.obj V)) _) = _
    dsimp only [ringedSitePullbackSection]
    erw [tensorPullback_pure]
    rw [tensorIso_pure]
    change _ = siteSheafTensorTmul _ _ _
      ((pos n).hom.val.app _ _) _
    rfl
  · intro n V φ x
    dsimp only [P, neg, Iso.trans_hom, asIso_hom]
    rw [dualIso_hom]
    change ((δ (scalarTensorPower R L (n + 1))).val.app (op (U.obj V))
      (ringedSitePullbackSection a _ _ V φ)).app (op (Over.mk (𝟙 (U.obj V))))
        ((pos n).inv.val.app (op (U.obj V))
          ((pos n).hom.val.app (op (U.obj V)) (ringedSitePullbackSection a _ _ V x))) = _
    have hi := congrArg (fun f ↦ f.val.app (op (U.obj V))
      (ringedSitePullbackSection a
        (module_pushforward_isRightAdjoint_of_universes a)
          (scalarTensorPower R L (n + 1)) V x)) (pos n).hom_inv_id
    erw [hi]
    exact hδ (scalarTensorPower R L (n + 1)) V φ x

end SheafOfModules
