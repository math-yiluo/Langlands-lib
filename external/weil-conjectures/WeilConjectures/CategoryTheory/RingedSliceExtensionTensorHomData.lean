/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-! The Hom-equivalence data for the ringed-slice tensor projection formula. -/

@[expose] public section

universe uC u v

open CategoryTheory

namespace SheafOfModules

noncomputable def ringedSliceTensorLeft
    {C : Type uC} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}] :
    (SheafOfModules.{max u v} (((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U) ×
      SheafOfModules.{max u v} ((sheafCompose J
        (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ⥤
      SheafOfModules.{max u v} ((sheafCompose J
        (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) :=
  letI := siteTensor_identity_locallyInjective
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)
  letI := siteTensor_identity_locallySurjective
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)
  ((forget.{max u v} (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
    R).over U)).prod
      (overFunctor.{max u v} ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u
        v})).obj R) U ⋙ forget.{max u v}
        (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U)) ⋙
    MonoidalCategory.tensor
      (C := PresheafOfModules.{max u v} ((R.over U).obj ⋙
        forget₂ CommRingCat.{max u v} RingCat.{max u v})) ⋙
    PresheafOfModules.sheafification.{max u v} (J := J.over U)
      (R := ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U) (𝟙
        _) ⋙
    extensionByZeroPresheaf.{max u v} ((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U ⋙
    PresheafOfModules.sheafification.{max u v} (𝟙 ((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).obj))

noncomputable def ringedSliceTensorRight
    {C : Type uC} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}] :
    (SheafOfModules.{max u v} (((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U) ×
      SheafOfModules.{max u v} ((sheafCompose J
        (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ⥤
      SheafOfModules.{max u v} ((sheafCompose J
        (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) :=
  letI := siteTensor_identity_locallyInjective
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)
  letI := siteTensor_identity_locallySurjective
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)
  (((extensionByZeroPresheaf.{max u v} ((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U ⋙
        PresheafOfModules.sheafification.{max u v} (𝟙 ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).obj) ⋙
        forget.{max u v} ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
          R)).prod
      (forget.{max u v} ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
        R))) ⋙
    MonoidalCategory.tensor
      (C := PresheafOfModules.{max u v} (R.obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u v})) ⋙
    PresheafOfModules.sheafification.{max u v} (𝟙 ((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).obj))

namespace RingedSliceTensor

section HomData

universe vD vE vB vK uD uE uB uK
variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {B : Type uB} [Category.{vB} B] {K : Type uK} [Category.{vK} K]

-- Compose Hom equivalences without unfolding their constructions in the naturality proofs.
private structure HomData (A : D ⥤ B) (T : E ⥤ B) (A' : D ⥤ K) (T' : E ⥤ K) where
  equiv : ∀ X H, ((A).obj X ⟶ T.obj H) ≃ (A'.obj X ⟶ T'.obj H)
  post : ∀ X H H' (f : (A).obj X ⟶ T.obj H) (h : H ⟶ H'),
    equiv X H' (f ≫ T.map h) = equiv X H f ≫ T'.map h
  pre : ∀ X X' H (g : X ⟶ X') (f : (A).obj X' ⟶ T.obj H),
    equiv X H (A.map g ≫ f) = A'.map g ≫ equiv X' H f

@[irreducible] private noncomputable def HomData.trans
    {V : Type*} [Category* V] {A : D ⥤ B} {T : E ⥤ B}
    {A' : D ⥤ K} {T' : E ⥤ K} {A'' : D ⥤ V} {T'' : E ⥤ V}
    (a : HomData A T A' T') (b : HomData A' T' A'' T'') : HomData A T A'' T'' where
  equiv X H := (a.equiv X H).trans (b.equiv X H)
  post X H H' f h := by
    change b.equiv _ _ (a.equiv _ _ _) = _
    rw [a.post, b.post]
    rfl
  pre X X' H g f := by
    change b.equiv _ _ (a.equiv _ _ _) = _
    rw [a.pre, b.pre]
    rfl

@[irreducible] private noncomputable def HomData.symm
    {A : D ⥤ B} {T : E ⥤ B} {A' : D ⥤ K} {T' : E ⥤ K}
    (a : HomData A T A' T') : HomData A' T' A T where
  equiv X H := (a.equiv X H).symm
  post X H H' f h := by
    apply (a.equiv X H').injective
    rw [a.post, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  pre X X' H g f := by
    apply (a.equiv X H).injective
    rw [a.pre, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[irreducible] private noncomputable def HomData.adj (L : B ⥤ K) (Q : K ⥤ B) (adj : L ⊣ Q)
    (A : D ⥤ B) (T : E ⥤ K) : HomData (A ⋙ L) T A (T ⋙ Q) where
  equiv X H := adj.homEquiv ((A).obj X) (T.obj H)
  post _ _ _ f h := adj.homEquiv_naturality_right f (T.map h)
  pre _ _ _ g f := adj.homEquiv_naturality_left (A.map g) f

@[irreducible] private noncomputable def HomData.iso {A A' : D ⥤ B} (a : A ≅ A') (T : E ⥤ B) :
    HomData A T A' T where
  equiv X H := (a.app X).homCongr (Iso.refl _)
  post X H H' f h := by simp [Iso.homCongr, Category.assoc]
  pre X X' H g f := by
    change a.inv.app X ≫ (A.map g ≫ f) ≫ 𝟙 _ =
      A'.map g ≫ a.inv.app X' ≫ f ≫ 𝟙 _
    simp only [Category.comp_id]
    exact a.inv.naturality_assoc g f |>.symm

end HomData

section
variable {R : Type (max u v)} [CommRing R] {ι : Type v} [DecidableEq ι]
  {M : ι → Type (max u v)} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  {N P : Type (max u v)} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
-- Keep the direct-sum/tensor construction behind its generator formula.
@[irreducible] private noncomputable def sumTensorLift
    (a : ∀ i, TensorProduct R (M i) N →ₗ[R] P) :
    TensorProduct R (DirectSum ι M) N →ₗ[R] P :=
  TensorProduct.lift (DirectSum.toModule R ι (N →ₗ[R] P)
    (fun i ↦ TensorProduct.curry (a i)))
private theorem sumTensorLift_of (a : ∀ i, TensorProduct R (M i) N →ₗ[R] P)
    (i : ι) (x : M i) (y : N) :
    sumTensorLift.{u, v} a (DirectSum.of M i x ⊗ₜ[R] y) = a i (x ⊗ₜ[R] y) := by
  unfold sumTensorLift
  simp only [TensorProduct.lift.tmul]
  erw [DirectSum.toModule_lof]
  rfl
end

-- The explicit adjunction from LocalizedModuleAdjunctionExact, with independent
-- object and coefficient universes. No exactness or precoverage hypotheses are needed.
open Classical in
private theorem extensionRestrict_of
    {C : Type uC} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (F : SheafOfModules.{max u v} (R.over U)) {V W : Cᵒᵖ} (a : V ⟶ W)
    (φ : V.unop ⟶ U) (ψ : W.unop ⟶ U) (h : a.unop ≫ φ = ψ)
    (x : F.val.obj (Opposite.op (Over.mk φ))) :
    extensionByZeroPresheafRestrictAdd R U F a
        (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x) =
      DirectSum.of (fun χ : W.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk χ))) ψ
        (F.val.map (Opposite.op (Over.homMk a.unop h : Over.mk ψ ⟶ Over.mk φ)) x) := by
  subst ψ
  change (DirectSum.toAddMonoid _)
    (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
private noncomputable def extensionPresheafToHom
    {C : Type uC} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (F : SheafOfModules.{max u v} (R.over U)) (G : SheafOfModules.{max u v} R)
    (a : extensionByZeroPresheafObj R U F ⟶ G.val) :
    F ⟶ (overFunctor.{max u v} R U).obj G where
  val.app X := ModuleCat.ofHom
    ((a.app (Opposite.op X.unop.left)).hom.comp
      (DirectSum.lof (R.obj.obj (Opposite.op X.unop.left)) (X.unop.left ⟶ U)
        (fun φ ↦ F.val.obj (Opposite.op (Over.mk φ))) X.unop.hom))
  val.naturality {X Y} f := by
    ext x
    have h := PresheafOfModules.naturality_apply a
      ((Over.forget U).op.map f)
      (DirectSum.of _ X.unop.hom x)
    change a.app (Opposite.op Y.unop.left)
        (extensionByZeroPresheafRestrictAdd R U F ((Over.forget U).op.map f)
          (DirectSum.of _ X.unop.hom x)) = _ at h
    have hr := extensionRestrict_of.{uC, u, v} R U F ((Over.forget U).op.map f)
      X.unop.hom Y.unop.hom (Over.w f.unop) x
    erw [hr] at h
    have hf : (Over.homMk f.unop.left (Over.w f.unop) : Y.unop ⟶ X.unop) =
        f.unop := by ext; rfl
    erw [hf] at h
    change a.app (Opposite.op Y.unop.left)
        (DirectSum.of (fun φ : Y.unop.left ⟶ U ↦
          F.val.obj (Opposite.op (Over.mk φ))) Y.unop.hom (F.val.map f x)) =
      G.val.map ((Over.forget U).op.map f)
        (a.app (Opposite.op X.unop.left)
          (DirectSum.of (fun φ : X.unop.left ⟶ U ↦
            F.val.obj (Opposite.op (Over.mk φ))) X.unop.hom x))
    exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
private noncomputable def extensionHomToPresheaf
    {C : Type uC} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (F : SheafOfModules.{max u v} (R.over U)) (G : SheafOfModules.{max u v} R)
    (a : F ⟶ (overFunctor.{max u v} R U).obj G) :
    extensionByZeroPresheafObj R U F ⟶ G.val where
  app V := ModuleCat.ofHom (DirectSum.toModule _ _ _
    (fun φ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk φ))).hom))
  naturality {V W} f := by
    ext x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of φ x =>
      change (DirectSum.toModule (R.obj.obj W) _ (G.val.obj W)
        (fun ψ : W.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom))
        (extensionByZeroPresheafRestrictAdd R U F f
          (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x)) =
          G.val.map f ((DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
            (fun ψ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom))
            (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x))
      erw [extensionRestrict_of.{uC, u, v} R U F f φ (f.unop ≫ φ) rfl]
      erw [DirectSum.toModule_lof, DirectSum.toModule_lof]
      exact PresheafOfModules.naturality_apply a.val
        (Opposite.op (Over.homMk f.unop : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ)) x
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option backward.isDefEq.respectTransparency false in
open Classical in
private noncomputable def extensionPresheafHomEquiv
    {C : Type uC} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (F : SheafOfModules.{max u v} (R.over U)) (G : SheafOfModules.{max u v} R) :
    (extensionByZeroPresheafObj R U F ⟶ G.val) ≃
      (F ⟶ (overFunctor.{max u v} R U).obj G) where
  toFun := extensionPresheafToHom.{uC, u, v} R U F G
  invFun := extensionHomToPresheaf.{uC, u, v} R U F G
  left_inv a := by
    ext V x
    change (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
      (fun φ : V.unop ⟶ U ↦ (a.app V).hom.comp
        (DirectSum.lof (R.obj.obj V) _ _ φ))) x = (a.app V) x
    exact (DirectSum.toModule.unique _ (a.app V).hom x).symm
  right_inv a := by
    ext X x
    change (DirectSum.toModule (R.obj.obj (Opposite.op X.unop.left)) _
      (G.val.obj (Opposite.op X.unop.left))
      (fun φ : X.unop.left ⟶ U ↦ (a.val.app (Opposite.op (Over.mk φ))).hom))
        (DirectSum.lof _ _ _ X.unop.hom x) = (a.val.app X) x
    erw [DirectSum.toModule_lof]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem extensionPresheafHomEquiv_naturality_right
    {C : Type uC} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (F : SheafOfModules.{max u v} (R.over U)) (G H : SheafOfModules.{max u v} R)
    (a : extensionByZeroPresheafObj R U F ⟶ G.val) (b : G ⟶ H) :
    extensionPresheafHomEquiv.{uC, u, v} R U F H (a ≫ b.val) =
      extensionPresheafHomEquiv.{uC, u, v} R U F G a ≫ (overFunctor.{max u v} R U).map b := by
  ext X x
  rfl

set_option backward.isDefEq.respectTransparency false in
open Classical in
private theorem extensionPresheafHomEquiv_naturality_left
    {C : Type uC} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (F H : SheafOfModules.{max u v} (R.over U)) (G : SheafOfModules.{max u v} R)
    (a : H ⟶ F) (b : extensionByZeroPresheafObj R U F ⟶ G.val) :
    extensionPresheafHomEquiv.{uC, u, v} R U H G ((extensionByZeroPresheaf.{max u v} R U).map a ≫
      b) =
      a ≫ extensionPresheafHomEquiv.{uC, u, v} R U F G b := by
  ext X x
  change b.app (Opposite.op X.unop.left)
    ((DirectSum.lmap (R := R.obj.obj (Opposite.op X.unop.left))
      (fun ψ ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom))
        (DirectSum.of _ X.unop.hom x)) =
      b.app (Opposite.op X.unop.left)
        (DirectSum.of _ X.unop.hom ((a.val.app X) x))
  erw [DirectSum.lmap_of]
  rfl

@[irreducible] private noncomputable def extensionHomData
    {C : Type uC} [Category.{v} C] {J : GrothendieckTopology C}
    {D : Type*} [Category* D]
    (R : Sheaf J RingCat.{max u v}) (U : C) (F : D ⥤ SheafOfModules.{max u v} (R.over U)) :
    HomData (F ⋙ extensionByZeroPresheaf.{max u v} R U) (forget.{max u v} R) F (overFunctor.{max u
      v} R U) where
  equiv X H := extensionPresheafHomEquiv.{uC, u, v} R U (F.obj X) H
  post X H H' f h := extensionPresheafHomEquiv_naturality_right.{uC, u, v} R U (F.obj X) H H' f h
  pre X Y H f a := extensionPresheafHomEquiv_naturality_left.{uC, u, v} R U (F.obj Y) (F.obj X) H
    (F.map f) a

section RawTensor

open Opposite MonoidalCategory

variable {C : Type uC} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  (R : Sheaf J CommRingCat.{max u v}) (U : C)

set_option backward.isDefEq.respectTransparency false

set_option hygiene false in
local notation "A" => (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R

private abbrev rawRestrict
    (M : PresheafOfModules.{max u v} (R.obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u v})) :
    PresheafOfModules.{max u v} ((R.over U).obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u v})
      :=
  (PresheafOfModules.pushforward₀OfCommRingCat (Over.forget U) R.obj).obj M

variable (F : SheafOfModules.{max u v} ((A).over U)) (G H : SheafOfModules.{max u v} A)

open Classical in
@[irreducible] private noncomputable def rawFromSlice
    (a : (PresheafOfModules.Monoidal.tensorObj (R := (R.over U).obj)
      F.val (rawRestrict.{uC, u, v} R U G.val)) ⟶ (rawRestrict.{uC, u, v} R U H.val)) :
    (PresheafOfModules.Monoidal.tensorObj (R := R.obj)
      ((extensionByZeroPresheaf.{max u v} A U).obj F) G.val) ⟶ H.val where
  app V := by
    change ModuleCat.of (R.obj.obj V)
      (TensorProduct (R.obj.obj V) (extensionByZeroPresheafSection A U F V)
        (G.val.obj V)) ⟶ H.val.obj V
    exact ModuleCat.ofHom (sumTensorLift.{u, v} (R := R.obj.obj V)
      (fun φ ↦ by exact (a.app (op (Over.mk φ))).hom))
  naturality {V W} i := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext' (R := R.obj.obj V)
    intro x y
    induction x using DirectSum.induction_on with
    | zero => simp [LinearMap.map_zero]
    | of φ x =>
      change sumTensorLift.{u, v} (R := R.obj.obj W)
        (N := G.val.obj W) (P := H.val.obj W)
        (fun ψ ↦ by exact (a.app (op (Over.mk ψ))).hom)
          (extensionByZeroPresheafRestrictAdd A U F i (DirectSum.of _ φ x) ⊗ₜ[R.obj.obj W]
            (show G.val.obj W from G.val.map i y)) =
            H.val.map i (sumTensorLift.{u, v} (R := R.obj.obj V)
              (fun ψ ↦ by exact (a.app (op (Over.mk ψ))).hom)
                (DirectSum.of (fun ψ ↦ F.val.obj (op (Over.mk ψ))) φ x ⊗ₜ[R.obj.obj V] y))
      erw [extensionRestrict_of.{uC, u, v} A U F i φ (i.unop ≫ φ) rfl]
      erw [sumTensorLift_of.{u, v}, sumTensorLift_of.{u, v}]
      exact PresheafOfModules.naturality_apply a
        (op (Over.homMk i.unop : Over.mk (i.unop ≫ φ) ⟶ Over.mk φ))
          (x ⊗ₜ[R.obj.obj V] y)
    | add x z hx hz =>
      simpa only [map_add, TensorProduct.add_tmul] using congrArg₂ (· + ·) hx hz

open Classical in
private theorem rawFromSlice_of
    (a : (PresheafOfModules.Monoidal.tensorObj (R := (R.over U).obj)
      F.val (rawRestrict.{uC, u, v} R U G.val)) ⟶ (rawRestrict.{uC, u, v} R U H.val))
    (V : Cᵒᵖ) (φ : V.unop ⟶ U) (x : F.val.obj (op (Over.mk φ)))
    (y : G.val.obj V) :
    (rawFromSlice.{uC, u, v} R U F G H a).app V
        (DirectSum.of (fun ψ ↦ F.val.obj (op (Over.mk ψ))) φ x ⊗ₜ[R.obj.obj V] y) =
      a.app (op (Over.mk φ)) (x ⊗ₜ[R.obj.obj V] y) := by
  unfold rawFromSlice
  change sumTensorLift.{u, v} (R := R.obj.obj V)
    (M := fun ψ : V.unop ⟶ U ↦ F.val.obj (op (Over.mk ψ)))
    (N := G.val.obj V) (P := H.val.obj V)
    (fun ψ ↦ by exact (a.app (op (Over.mk ψ))).hom) _ = _
  exact sumTensorLift_of.{u, v} (R := R.obj.obj V)
    (M := fun ψ : V.unop ⟶ U ↦ F.val.obj (op (Over.mk ψ)))
    (N := G.val.obj V) (P := H.val.obj V) _ φ x y

open Classical in
private noncomputable def rawToSlice
    (b : (PresheafOfModules.Monoidal.tensorObj (R := R.obj)
      ((extensionByZeroPresheaf.{max u v} A U).obj F) G.val) ⟶ H.val) :
    (PresheafOfModules.Monoidal.tensorObj (R := (R.over U).obj)
      F.val (rawRestrict.{uC, u, v} R U G.val)) ⟶ (rawRestrict.{uC, u, v} R U H.val) where
  app X := ModuleCat.ofHom ((b.app (op X.unop.left)).hom.comp
    (TensorProduct.map
      (DirectSum.lof (R.obj.obj (op X.unop.left)) (X.unop.left ⟶ U)
        (fun φ ↦ F.val.obj (op (Over.mk φ))) X.unop.hom) LinearMap.id))
  naturality {X Y} i := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext' (R := R.obj.obj (op X.unop.left))
    intro x y
    have h := PresheafOfModules.naturality_apply b ((Over.forget U).op.map i)
      (DirectSum.of _ X.unop.hom x ⊗ₜ[R.obj.obj (op X.unop.left)] y)
    change b.app (op Y.unop.left)
        (extensionByZeroPresheafRestrictAdd A U F ((Over.forget U).op.map i)
          (DirectSum.of _ X.unop.hom x) ⊗ₜ[R.obj.obj (op Y.unop.left)]
            G.val.map ((Over.forget U).op.map i) y) = _ at h
    erw [extensionRestrict_of.{uC, u, v} A U F ((Over.forget U).op.map i)
      X.unop.hom Y.unop.hom (Over.w i.unop) x] at h
    have hi : (Over.homMk i.unop.left (Over.w i.unop) : Y.unop ⟶ X.unop) =
        i.unop := by ext; rfl
    erw [hi] at h
    exact h

private noncomputable def rawTensorHomEquiv :
    ((PresheafOfModules.Monoidal.tensorObj (R := (R.over U).obj)
      F.val (rawRestrict.{uC, u, v} R U G.val)) ⟶ (rawRestrict.{uC, u, v} R U H.val)) ≃
      ((PresheafOfModules.Monoidal.tensorObj (R := R.obj)
      ((extensionByZeroPresheaf.{max u v} A U).obj F) G.val) ⟶ H.val) where
  toFun := rawFromSlice.{uC, u, v} R U F G H
  invFun := rawToSlice.{uC, u, v} R U F G H
  left_inv a := by
    classical
    ext X : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext' (R := R.obj.obj (op X.unop.left))
    intro x y
    exact rawFromSlice_of.{uC, u, v} R U F G H a (op X.unop.left) X.unop.hom x y
  right_inv b := by
    classical
    ext V : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext' (R := R.obj.obj V)
    intro x y
    induction x using DirectSum.induction_on with
    | zero => simp
    | of φ x =>
      erw [rawFromSlice_of.{uC, u, v} R U F G H]
      rfl
    | add x z hx hz =>
      simpa only [map_add, TensorProduct.add_tmul] using congrArg₂ (· + ·) hx hz

private noncomputable def rawSliceTensor :
    (SheafOfModules.{max u v} ((A).over U) × SheafOfModules.{max u v} A) ⥤
      PresheafOfModules.{max u v} ((R.over U).obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u
        v}) :=
  (forget.{max u v} ((A).over U)).prod
      (forget.{max u v} A ⋙ PresheafOfModules.pushforward₀OfCommRingCat (Over.forget U) R.obj) ⋙
    MonoidalCategory.tensor
      (C := PresheafOfModules.{max u v} ((R.over U).obj ⋙ forget₂ CommRingCat.{max u v}
        RingCat.{max u v}))

private noncomputable def rawBaseTensor :
    (SheafOfModules.{max u v} ((A).over U) × SheafOfModules.{max u v} A) ⥤
      PresheafOfModules.{max u v} (R.obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u v}) :=
  (extensionByZeroPresheaf.{max u v} A U).prod (forget.{max u v} A) ⋙
    MonoidalCategory.tensor
      (C := PresheafOfModules.{max u v} (R.obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u v}))

@[irreducible] private noncomputable def rawHomData :
    HomData (rawSliceTensor.{uC, u, v} R U) (overFunctor.{max u v} A U ⋙ forget.{max u v} ((A).over
      U))
      (rawBaseTensor.{uC, u, v} R U) (forget.{max u v} A) where
  equiv X H := rawTensorHomEquiv.{uC, u, v} R U X.1 X.2 H
  post X H H' a h := by
    classical
    apply (rawTensorHomEquiv.{uC, u, v} R U X.1 X.2 H').symm.injective
    change (rawTensorHomEquiv.{uC, u, v} R U X.1 X.2 H').symm
      ((rawTensorHomEquiv.{uC, u, v} R U X.1 X.2 H') _) = _
    rw [Equiv.symm_apply_apply]
    ext V : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext' (R := R.obj.obj (op V.unop.left))
    intro x y
    change (h.val.app (op V.unop.left)) (a.app V (x ⊗ₜ[R.obj.obj (op V.unop.left)] y)) =
      (h.val.app (op V.unop.left))
        ((rawFromSlice.{uC, u, v} R U X.1 X.2 H a).app (op V.unop.left)
          (DirectSum.of _ V.unop.hom x ⊗ₜ[R.obj.obj (op V.unop.left)] y))
    erw [rawFromSlice_of.{uC, u, v} R U X.1 X.2 H]
    rfl
  pre X Y H f a := by
    classical
    apply (rawTensorHomEquiv.{uC, u, v} R U X.1 X.2 H).symm.injective
    change (rawTensorHomEquiv.{uC, u, v} R U X.1 X.2 H).symm
      ((rawTensorHomEquiv.{uC, u, v} R U X.1 X.2 H) _) = _
    rw [Equiv.symm_apply_apply]
    ext V : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext' (R := R.obj.obj (op V.unop.left))
    intro x y
    change a.app V
      ((f.1.val.app V) x ⊗ₜ[R.obj.obj (op V.unop.left)]
        (f.2.val.app (op V.unop.left)) y) =
      (rawFromSlice.{uC, u, v} R U Y.1 Y.2 H a).app (op V.unop.left)
        ((DirectSum.lmap (R := R.obj.obj (op V.unop.left))
          (fun ψ ↦ (f.1.val.app (op (Over.mk ψ))).hom))
          (DirectSum.of _ V.unop.hom x) ⊗ₜ[R.obj.obj (op V.unop.left)]
            (f.2.val.app (op V.unop.left)) y)
    erw [DirectSum.lmap_of, rawFromSlice_of.{uC, u, v} R U Y.1 Y.2 H]
    rfl

private noncomputable def publicSliceTensor :
    (SheafOfModules.{max u v} ((A).over U) × SheafOfModules.{max u v} A) ⥤
      PresheafOfModules.{max u v} ((R.over U).obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u
        v}) :=
  (forget.{max u v} ((A).over U)).prod (overFunctor.{max u v} A U ⋙ forget.{max u v} ((A).over U)) ⋙
    MonoidalCategory.tensor
      (C := PresheafOfModules.{max u v} ((R.over U).obj ⋙ forget₂ CommRingCat.{max u v}
        RingCat.{max u v}))

private noncomputable def rawSliceTensorIso : publicSliceTensor.{uC, u, v} R U ≅
  rawSliceTensor.{uC, u, v} R U :=
  NatIso.ofComponents (fun X ↦ PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by
    intro V W i
    apply ModuleCat.hom_ext
    apply TensorProduct.ext' (R := (R.over U).obj.obj V)
    intro x y
    rfl)) (by
      intro X Y f
      ext V : 1
      apply ModuleCat.hom_ext
      apply TensorProduct.ext' (R := (R.over U).obj.obj V)
      intro x y
      rfl)

end RawTensor

section SheafifyTensor

open Opposite MonoidalCategory

variable {C : Type uC} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v}) (U : C)

set_option backward.isDefEq.respectTransparency false

set_option hygiene false in
local notation "A" => (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R

variable [Presheaf.IsLocallyInjective J (𝟙 (A).obj)]
  [Presheaf.IsLocallySurjective J (𝟙 (A).obj)]

private noncomputable def siteTensorIso
    (P N : PresheafOfModules.{max u v} (R.obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u v})) :
    siteTensorPresheaf P N ≅ P ⊗ N :=
  PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by
    intro V W i
    apply ModuleCat.hom_ext
    apply TensorProduct.ext' (R := R.obj.obj V)
    intro x y
    rfl)

@[irreducible] private noncomputable def tensorUnitMap
    (P : PresheafOfModules.{max u v} (R.obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u v})) :
    P ⟶ ((PresheafOfModules.sheafification.{max u v} (R := A) (𝟙 _)).obj P).val :=
  PresheafOfModules.toSheafify (R := A) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf)

private theorem tensorUnitMap_naturality
    {P Q : PresheafOfModules.{max u v} (R.obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u v})}
      (f : P ⟶ Q) :
    f ≫ tensorUnitMap.{uC, u, v} R Q = tensorUnitMap.{uC, u, v} R P ≫
      ((PresheafOfModules.sheafification.{max u v} (R := A) (𝟙 _)).map f).val := by
  unfold tensorUnitMap
  exact (PresheafOfModules.sheafificationAdjunction.{max u v} (R := A) (𝟙 _)).unit.naturality f

private theorem tensorUnitMap_isIso
    (P N : PresheafOfModules.{max u v} (R.obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u v})) :
    IsIso ((PresheafOfModules.sheafification.{max u v} (R := A) (𝟙 _)).map
      (tensorUnitMap.{uC, u, v} R P ▷ N)) := by
  have : PresheafOfModules.IsLocallyInjective J (tensorUnitMap.{uC, u, v} R P) := by
    unfold tensorUnitMap
    infer_instance
  have : PresheafOfModules.IsLocallySurjective J (tensorUnitMap.{uC, u, v} R P) := by
    unfold tensorUnitMap
    infer_instance
  have ht : IsIso ((PresheafOfModules.sheafification.{max u v} (R := A) (𝟙 _)).map
      (siteTensorHom (tensorUnitMap.{uC, u, v} R P) N)) :=
    PresheafOfModules.sheafification_tensorHom_isIso (J := J)
    (f := tensorUnitMap.{uC, u, v} R P) (N := N) (A).property
  have heq : tensorUnitMap.{uC, u, v} R P ▷ N =
      (siteTensorIso.{uC, u, v} R P N).inv ≫ siteTensorHom (tensorUnitMap.{uC, u, v} R P) N ≫
        (siteTensorIso.{uC, u, v} R _ N).hom := by
    ext V : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext' (R := R.obj.obj V)
    intro x y
    rfl
  rw [heq, Functor.map_comp, Functor.map_comp]
  infer_instance

private noncomputable def rawSheafTensor :
    (SheafOfModules.{max u v} ((A).over U) × SheafOfModules.{max u v} A) ⥤
      PresheafOfModules.{max u v} (R.obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u v}) :=
  (extensionByZeroPresheaf.{max u v} A U ⋙ PresheafOfModules.sheafification.{max u v} (R := A) (𝟙
    (A).obj) ⋙
    forget.{max u v} A).prod (forget.{max u v} A) ⋙ MonoidalCategory.tensor
      (C := PresheafOfModules.{max u v} (R.obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u v}))

private noncomputable def rawSheafTensorMap : rawBaseTensor.{uC, u, v} R U ⟶ rawSheafTensor.{uC, u,
  v} R U where
  app X := tensorUnitMap.{uC, u, v} R ((extensionByZeroPresheaf.{max u v} A U).obj X.1) ▷ X.2.val
  naturality {X Y} f := by
    change (_ ⊗ₘ _) ≫ (_ ▷ _) = (_ ▷ _) ≫ (_ ⊗ₘ _)
    rw [tensorHom_comp_whiskerRight, whiskerRight_comp_tensorHom]
    congr 1
    exact tensorUnitMap_naturality.{uC, u, v} R ((extensionByZeroPresheaf.{max u v} A U).map f.1)

@[irreducible] private noncomputable def sheafTensorIso :
    rawBaseTensor.{uC, u, v} R U ⋙ PresheafOfModules.sheafification.{max u v} (R := A) (𝟙 (A).obj) ≅
      rawSheafTensor.{uC, u, v} R U ⋙ PresheafOfModules.sheafification.{max u v} (R := A) (𝟙
        (A).obj) := by
  let t := Functor.whiskerRight (rawSheafTensorMap.{uC, u, v} R U)
    (PresheafOfModules.sheafification.{max u v} (R := A) (𝟙 (A).obj))
  have : ∀ X, IsIso (t.app X) := fun X ↦ tensorUnitMap_isIso.{uC, u, v} R _ _
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

end SheafifyTensor

end RingedSliceTensor

/--
The Hom-equivalence family underlying the ringed-slice projection formula.

Source: Stacks Project, Modules on Sites, Tag 0E8I, lemma-j-shriek-and-tensor.
(auxiliary; not a blueprint node)

Proof: Construct the extension adjunction by evaluating a map out of the direct sum
on each summand; its inverse sums the components of a map to the restricted sheaf.
Compose this with module sheafification. For slice modules F and base modules G,H,
a map from the sectionwise tensor F tensor G|U to H|U extends bilinearly on each
direct-sum summand to a map from the extension presheaf of F tensor G to H.
Conversely, evaluate such a map on a summand injection tensored with the identity.
The direct-sum and tensor generator formulas prove the inverse laws and naturality
in all three modules. These constructions work with an independent object universe.
Finally the sheafification unit of the extension presheaf is locally bijective.
Tensor descent makes its tensor with G an isomorphism after sheafification.
Compose the extension adjunction, slice sheafification adjunction, direct-sum tensor
Hom equivalence, inverse base sheafification adjunction, and this last isomorphism.
Each factor commutes with precomposition in the parameter pair and postcomposition
in the test module, so their composite has both displayed naturality laws.
-/
theorem ringedSlice_extension_tensor_hom_data
    {C : Type uC} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}] :
    let S := SheafOfModules.{max u v} ((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)
    let T := SheafOfModules.{max u v} (((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U)
    ∃ e : ∀ X : T × S, ∀ H : S,
      (((ringedSliceTensorLeft.{uC, u, v} J R U).obj X ⟶ H) ≃
        ((ringedSliceTensorRight.{uC, u, v} J R U).obj X ⟶ H)),
      (∀ (X : T × S) (H K : S)
          (φ : (ringedSliceTensorLeft.{uC, u, v} J R U).obj X ⟶ H) (h : H ⟶ K),
        e X K (φ ≫ h) = e X H φ ≫ h) ∧
      (∀ (X Y : T × S) (H : S) (f : X ⟶ Y)
          (φ : (ringedSliceTensorLeft.{uC, u, v} J R U).obj Y ⟶ H),
        e X H ((ringedSliceTensorLeft.{uC, u, v} J R U).map f ≫ φ) =
          (ringedSliceTensorRight.{uC, u, v} J R U).map f ≫ e Y H φ) := by
  let A := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
  have : Presheaf.IsLocallyInjective J (𝟙 A.obj) :=
    siteTensor_identity_locallyInjective A
  have : Presheaf.IsLocallySurjective J (𝟙 A.obj) :=
    siteTensor_identity_locallySurjective A
  have : Presheaf.IsLocallyInjective (J.over U) (𝟙 (A.over U).obj) :=
    siteTensor_identity_locallyInjective (A.over U)
  have : Presheaf.IsLocallySurjective (J.over U) (𝟙 (A.over U).obj) :=
    siteTensor_identity_locallySurjective (A.over U)
  let S := SheafOfModules.{max u v} A
  let Q := overFunctor.{max u v} A U
  let a := PresheafOfModules.sheafification.{max u v} (J := J) (R := A) (𝟙 A.obj)
  let b := PresheafOfModules.sheafification.{max u v} (J := J.over U) (R := A.over U) (𝟙 _)
  let adj : a ⊣ forget.{max u v} A :=
    PresheafOfModules.sheafificationAdjunction.{max u v} (J := J) (R := A) (𝟙 A.obj)
  let adjU : b ⊣ forget.{max u v} (A.over U) :=
    PresheafOfModules.sheafificationAdjunction.{max u v} (J := J.over U) (R := A.over U) (𝟙 _)
  let TL := RingedSliceTensor.publicSliceTensor.{uC, u, v} R U ⋙ b ⋙ extensionByZeroPresheaf.{max u
    v} A U ⋙ a
  let TR := RingedSliceTensor.rawSheafTensor.{uC, u, v} R U ⋙ a
  have hL : ringedSliceTensorLeft.{uC, u, v} J R U = TL := by rfl
  have hR : ringedSliceTensorRight.{uC, u, v} J R U = TR := by rfl
  rw [hL, hR]
  let e₀ : RingedSliceTensor.HomData TL (𝟭 S)
      (RingedSliceTensor.publicSliceTensor.{uC, u, v} R U ⋙ b ⋙ extensionByZeroPresheaf.{max u v} A
        U) (forget.{max u v} A) :=
    RingedSliceTensor.HomData.adj a (forget.{max u v} A) adj
      (RingedSliceTensor.publicSliceTensor.{uC, u, v} R U ⋙ b ⋙ extensionByZeroPresheaf.{max u v} A
        U) (𝟭 S)
  let e₁ : RingedSliceTensor.HomData
      (RingedSliceTensor.publicSliceTensor.{uC, u, v} R U ⋙ b ⋙ extensionByZeroPresheaf.{max u v} A
        U) (forget.{max u v} A)
      (RingedSliceTensor.publicSliceTensor.{uC, u, v} R U ⋙ b) Q :=
    RingedSliceTensor.extensionHomData A U (RingedSliceTensor.publicSliceTensor.{uC, u, v} R U ⋙ b)
  let e₂ : RingedSliceTensor.HomData (RingedSliceTensor.publicSliceTensor.{uC, u, v} R U ⋙ b) Q
      (RingedSliceTensor.publicSliceTensor.{uC, u, v} R U) (Q ⋙ forget.{max u v} (A.over U)) :=
    RingedSliceTensor.HomData.adj b (forget.{max u v} (A.over U)) adjU
      (RingedSliceTensor.publicSliceTensor.{uC, u, v} R U) Q
  let e₃ := (RingedSliceTensor.HomData.iso (RingedSliceTensor.rawSliceTensorIso.{uC, u, v} R U)
    (Q ⋙ forget.{max u v} (A.over U))).trans (RingedSliceTensor.rawHomData R U)
  let e₄ : RingedSliceTensor.HomData (RingedSliceTensor.rawBaseTensor.{uC, u, v} R U) (forget.{max
    u v} A)
      (RingedSliceTensor.rawBaseTensor.{uC, u, v} R U ⋙ a) (𝟭 S) :=
    (RingedSliceTensor.HomData.adj a (forget.{max u v} A) adj
      (RingedSliceTensor.rawBaseTensor.{uC, u, v} R U) (𝟭 S)).symm
  let e₅ : RingedSliceTensor.HomData (RingedSliceTensor.rawBaseTensor.{uC, u, v} R U ⋙ a) (𝟭 S)
      TR (𝟭 S) :=
    RingedSliceTensor.HomData.iso (RingedSliceTensor.sheafTensorIso.{uC, u, v} R U) (𝟭 S)
  let e := ((((e₀.trans e₁).trans e₂).trans e₃).trans e₄).trans e₅
  exact ⟨e.equiv, e.post, e.pre⟩

end SheafOfModules
