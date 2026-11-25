/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms

/-! # Ordinary derived semilinear sections

Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, Lemma 4.10 and Proposition
  4.17;
Stacks Project, Tags 0941, 079P, 06YS, 06YY, 07A4, 07A6 and 08J7--08JB
(auxiliary; not a blueprint node).

The categories below are module sheaves on the actual vertical sequence site and their
ordinary unbounded derived categories. All comparisons have specified sources, targets
and equations; there are no free proposition-valued parameters.

## Main definitions and statements

- `Systems`, `DS`: strict semilinear systems and their ordinary derived category.
- `Data`, `Geometry`, `OpenSystems`: the coefficient, geometric and localized calculus.
- `TensorComparisonModel`, `InverseTensorPure`: representative and pure-tensor normalization.
- `semilinearDerivedSections`: existence of the complete ordinary-derived calculus.
- `evaluation_mate`: compatibility of specified adjunction transposes with evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r c₂ v₂ k

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

@[irreducible] private def restrictionSheafificationMap
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) :
    (PresheafOfModules.sheafification.{r} (R := S) (𝟙 _)).obj
      ((PresheafOfModules.pushforward φ.hom).obj P) ⟶
        (SheafOfModules.pushforward.{r} φ).obj
          ((PresheafOfModules.sheafification.{r} (R := R) (𝟙 _)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv.{r} (𝟙 _)).symm
    ((PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction.{r} (R := R) (𝟙 _)).unit.app P))

private theorem restrictionSheafificationMap_unit
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) :
    toSheafify K (F.op ⋙ P.presheaf) ≫
        (PresheafOfModules.toPresheaf.{r} _).map (restrictionSheafificationMap φ P).val =
      Functor.whiskerLeft F.op (toSheafify L P.presheaf) := by
  have h := (PresheafOfModules.sheafificationHomEquiv.{r} (R := S) (𝟙 _)
    (P := (PresheafOfModules.pushforward φ.hom).obj P)
    (F := (SheafOfModules.pushforward.{r} φ).obj
      ((PresheafOfModules.sheafification.{r} (R := R) (𝟙 _)).obj P))).apply_symm_apply
    ((PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction.{r} (R := R) (𝟙 _)).unit.app P))
  unfold restrictionSheafificationMap
  exact congrArg ((PresheafOfModules.toPresheaf.{r} S.obj).map) h

private theorem restrictionSheafificationMap_unit_apply
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) (U : Dᵒᵖ)
    (z : ((PresheafOfModules.pushforward φ.hom).obj P).obj U) :
    (restrictionSheafificationMap φ P).val.app U
      (((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.app
        ((PresheafOfModules.pushforward φ.hom).obj P)).app U z) =
      ((PresheafOfModules.sheafificationAdjunction.{r} (R := R) (𝟙 _)).unit.app P).app
        (F.op.obj U) z := by
  exact congrArg (fun k ↦ k.app U z) (restrictionSheafificationMap_unit φ P)

private theorem pushforward_four_comp_apply
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    {A B C : SheafOfModules.{r} S} {P Q : SheafOfModules.{r} R}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ (SheafOfModules.pushforward φ).obj P)
    (d : P ⟶ Q) (U : Dᵒᵖ) (z : A.val.obj U) :
    (a ≫ b ≫ c ≫ (SheafOfModules.pushforward φ).map d).val.app U z =
      d.val.app (F.op.obj U) (c.val.app U (b.val.app U (a.val.app U z))) := rfl

private theorem sheaf_iso_inv_hom_apply
    {D : Type c} [Category.{v} D] {K : GrothendieckTopology D}
    {S : Sheaf K RingCat.{r}} {M N : SheafOfModules.{r} S}
    (T : M ≅ N) (U : Dᵒᵖ) (z : N.val.obj U) :
    T.hom.val.app U (T.inv.val.app U z) = z := by
  exact congrArg (fun k ↦ k.val.app U z) T.inv_hom_id

private theorem sheafification_unit_naturality_apply
    {D : Type c} [Category.{v} D] {K : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (S : Sheaf K RingCat.{r}) {P Q : PresheafOfModules.{r} S.obj} (f : P ⟶ Q)
    (U : Dᵒᵖ) (z : P.obj U) :
    ((PresheafOfModules.sheafification.{r} (R := S) (𝟙 _)).map f).val.app U
      (((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.app P).app
        U z) =
      ((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.app Q).app
        U (f.app U z) := by
  exact congrArg (fun k ↦ k.app U z)
    ((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.naturality f).symm

private theorem tensorComparison_unit_apply
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) (Q : PresheafOfModules.{r} S.obj)
    (t : Q ⟶ (PresheafOfModules.pushforward φ.hom).obj P)
    {A : SheafOfModules.{r} S} {B : SheafOfModules.{r} R}
    (T : A ≅ (PresheafOfModules.sheafification.{r} (R := S) (𝟙 _)).obj Q)
    (V : B ≅ (PresheafOfModules.sheafification.{r} (R := R) (𝟙 _)).obj P)
    (U : Dᵒᵖ) (z : Q.obj U) :
    (T.hom ≫ (PresheafOfModules.sheafification.{r} (R := S) (𝟙 _)).map t ≫
        restrictionSheafificationMap φ P ≫ (SheafOfModules.pushforward φ).map V.inv).val.app U
      (T.inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.app Q).app
          U z)) =
      V.inv.val.app (F.op.obj U)
        (((PresheafOfModules.sheafificationAdjunction.{r} (R := R) (𝟙 _)).unit.app P).app
          (F.op.obj U) (t.app U z)) := by
  rw [pushforward_four_comp_apply, sheaf_iso_inv_hom_apply,
    sheafification_unit_naturality_apply, restrictionSheafificationMap_unit_apply]

private theorem restrictionSheafificationMap_isIso
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L] [F.IsCocontinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) :
    IsIso (restrictionSheafificationMap φ P) := by
  let a := toSheafify K (F.op ⋙ P.presheaf)
  let b := (PresheafOfModules.toPresheaf.{r} _).map (restrictionSheafificationMap φ P).val
  have hi : Presheaf.IsLocallyInjective K
      (Functor.whiskerLeft F.op (toSheafify L P.presheaf)) :=
    Presheaf.isLocallyInjective_whisker K L F _
  have hs : Presheaf.IsLocallySurjective K
      (Functor.whiskerLeft F.op (toSheafify L P.presheaf)) :=
    Presheaf.isLocallySurjective_whisker K L F _
  have hi' : Presheaf.IsLocallyInjective K b := by
    rw [← Presheaf.comp_isLocallyInjective_iff K a b]
    rw [restrictionSheafificationMap_unit]
    exact hi
  have hs' : Presheaf.IsLocallySurjective K b := by
    rw [← Presheaf.comp_isLocallySurjective_iff K a b]
    rw [restrictionSheafificationMap_unit]
    exact hs
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{r} S)]
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · exact (Sheaf.isLocallyInjective_sheafToPresheaf_map_iff _).mp hi'
  · exact (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).mp hs'

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [ambientSmall : EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

private theorem tensorSection_hom_ext
    (R : Sheaf J CommRingCat.{max c v r})
    (M N P : Mod.{c, v, max c v r} J R)
    {f g : ordinaryTensor.{c, v, r} J R M N ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (tensorSection.{c, v, r} J R M N U x y) =
        g.val.app U (tensorSection.{c, v, r} J R M N U x y)) : f = g := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v r}
    (R := ring.{c, v, max c v r} J R) (𝟙 _)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r} M N).inv).mp
  apply (adj.homEquiv _ P).injective
  apply PresheafOfModules.hom_ext
  intro U
  ext z
  change f.val.app U ((SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r}
      M N).inv.val.app U ((adj.unit.app _).app U z)) =
    g.val.app U ((SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r}
      M N).inv.val.app U ((adj.unit.app _).app U z))
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact h U x y
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem restrictScalars_mu_bijective (R S : Type r) [CommRing R] [CommRing S]
    (e : R ≃+* S) (M N : ModuleCat.{r} S) :
    Function.Bijective (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N) := by
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm
  let em : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
      ((ModuleCat.restrictScalars e.toRingHom).obj M) M :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        change (e.toRingHom r) • x = (e.toRingHom r) • x
        rfl }
  let en : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
      ((ModuleCat.restrictScalars e.toRingHom).obj N) N :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        change (e.toRingHom r) • x = (e.toRingHom r) • x
        rfl }
  have hh : (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N :
      _ → _) = TensorProduct.congr em en := by
    funext z
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact ModuleCat.restrictScalars_μ_tmul e.toRingHom M N x y
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hh]
  exact (TensorProduct.congr em en).bijective

private theorem restrictScalars_mu_isIso (R S : Type r) [CommRing R] [CommRing S]
    (f : R →+* S) (M N : ModuleCat.{r} S)
    (hf : Function.Bijective f) :
    IsIso (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars f) M N) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact restrictScalars_mu_bijective R S (RingEquiv.ofBijective f hf) M N

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
@[irreducible] private def restrictionTensorPresheafIso
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {F : D ⥤ E} {R : Eᵒᵖ ⥤ CommRingCat.{r}} {S : Dᵒᵖ ⥤ CommRingCat.{r}}
    (φ : S ⋙ forget₂ CommRingCat RingCat ⟶ (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)
    (hφ : ∀ U, IsIso (φ.app U))
    (M N : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat)) :
    let G := PresheafOfModules.pushforward (F := F)
      (R := R ⋙ forget₂ CommRingCat RingCat)
      (S := S ⋙ forget₂ CommRingCat RingCat) φ
    PresheafOfModules.Monoidal.tensorObj (R := S) (G.obj M) (G.obj N) ≅
      G.obj (PresheafOfModules.Monoidal.tensorObj (R := R) M N) := by
  let G := PresheafOfModules.pushforward (F := F)
    (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat) φ
  letI : G.LaxMonoidal := PresheafOfModules.pushforwardLaxMonoidal φ
  let f := Functor.LaxMonoidal.μ G M N
  have h (U : Dᵒᵖ) : IsIso (f.app U) := by
    dsimp only [f, G]
    erw [PresheafOfModules.pushforward_μ_app φ M N U]
    apply restrictScalars_mu_isIso
    have := hφ U
    exact ConcreteCategory.bijective_of_isIso (φ.app U)
  exact PresheafOfModules.isoMk (fun U ↦ @asIso _ _ _ _ (f.app U) (h U))
    (fun {_ _} i ↦ f.naturality i)

private theorem restrictionTensorPresheafIso_pure
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {F : D ⥤ E} {R : Eᵒᵖ ⥤ CommRingCat.{r}} {S : Dᵒᵖ ⥤ CommRingCat.{r}}
    (φ : S ⋙ forget₂ CommRingCat RingCat ⟶ (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)
    (hφ : ∀ U, IsIso (φ.app U))
    (M N : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat))
    (U : Dᵒᵖ) (x : M.obj (F.op.obj U)) (y : N.obj (F.op.obj U)) :
    (restrictionTensorPresheafIso φ hφ M N).hom.app U (x ⊗ₜ[S.obj U] y) =
      x ⊗ₜ[R.obj (F.op.obj U)] y := by
  unfold restrictionTensorPresheafIso
  exact PresheafOfModules.pushforward_μ_app_tmul φ M N U x y

attribute [local irreducible] systemRing ringPresheaf rings
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
@[irreducible] private def evaluationTensorPresheafIso (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) :
    PresheafOfModules.Monoidal.tensorObj (R := (B n).obj)
      ((evaluation.{c, v, max c v r} J B τ n).obj M).val
      ((evaluation.{c, v, max c v r} J B τ n).obj N).val ≅
      (PresheafOfModules.pushforward
        (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom).obj
          (PresheafOfModules.Monoidal.tensorObj
            (R := (systemRing.{c, v, max c v r} J B τ).obj) M.val N.val) := by
  dsimp only [evaluation, SheafOfModules.pushforward]
  exact restrictionTensorPresheafIso
    (F := Prod.sectR n C) (R := (systemRing.{c, v, max c v r} J B τ).obj)
    (S := (B n).obj) (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom
    (fun U ↦ by
      let φ := eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm
      have : IsIso φ.hom := inferInstance
      exact NatIso.isIso_app_of_isIso φ.hom U) M.val N.val

private theorem evaluationTensorPresheafIso_pure (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))) :
    (evaluationTensorPresheafIso.{c, v, r} J B τ n M N).hom.app U
      (x ⊗ₜ[(B n).obj.obj U] y) =
      x ⊗ₜ[(systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, U.unop))] y := by
  unfold evaluationTensorPresheafIso
  exact restrictionTensorPresheafIso_pure
    (F := Prod.sectR n C) (R := (systemRing.{c, v, max c v r} J B τ).obj)
    (S := (B n).obj) _ _ M.val N.val U x y

@[irreducible] private def evaluationTensorComparison (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) :
    ordinaryTensor.{c, v, r} J (B n) ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) ⟶
      (evaluation.{c, v, max c v r} J B τ n).obj
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N) := by
  let R := systemRing.{c, v, max c v r} J B τ
  let φ := eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm
  let P := PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val
  letI := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} (B n)
  letI := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  exact (SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r}
      ((evaluation.{c, v, max c v r} J B τ n).obj M)
      ((evaluation.{c, v, max c v r} J B τ n).obj N)).hom ≫
    (PresheafOfModules.sheafification.{max c v r} (R := ring.{c, v, max c v r} J (B n))
      (𝟙 _)).map (evaluationTensorPresheafIso.{c, v, r} J B τ n M N).hom ≫
    restrictionSheafificationMap.{c, v, max c v r, c, v} φ P ≫
    (evaluation.{c, v, max c v r} J B τ n).map
      (SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r} M N).inv

private theorem evaluationTensorComparison_isIso (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) :
    IsIso (evaluationTensorComparison.{c, v, r} J B τ n M N) := by
  let R := systemRing.{c, v, max c v r} J B τ
  let φ := eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm
  let P := PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val
  have : (Prod.sectR n C).IsCocontinuous J (coefficientSequenceTopology J) :=
    ⟨fun hS ↦ hS⟩
  have := restrictionSheafificationMap_isIso.{c, v, max c v r, c, v} φ P
  unfold evaluationTensorComparison
  infer_instance

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem evaluationTensorComparison_pure (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))) :
    (evaluationTensorComparison.{c, v, r} J B τ n M N).val.app U
      (tensorSection.{c, v, r} J (B n)
        ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) U x y) =
      tensorSection.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ) M N (op (n, U.unop)) x y  := by
  let R := systemRing.{c, v, max c v r} J B τ
  let φ := eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm
  let P := PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val
  let Q := PresheafOfModules.Monoidal.tensorObj (R := (B n).obj)
    ((evaluation.{c, v, max c v r} J B τ n).obj M).val
    ((evaluation.{c, v, max c v r} J B τ n).obj N).val
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} (B n)
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  let T := SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r}
    ((evaluation.{c, v, max c v r} J B τ n).obj M)
    ((evaluation.{c, v, max c v r} J B τ n).obj N)
  let V := SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r} M N
  unfold evaluationTensorComparison
  exact (tensorComparison_unit_apply φ P Q
    (evaluationTensorPresheafIso.{c, v, r} J B τ n M N).hom T V U
    (x ⊗ₜ[(B n).obj.obj U] y)).trans
      (congrArg (fun z ↦ V.inv.val.app (op (n, U.unop))
        (((PresheafOfModules.sheafificationAdjunction.{max c v r}
          (R := ring.{c, v, max c v r} (coefficientSequenceTopology J) R)
          (𝟙 _)).unit.app P).app (op (n, U.unop)) z))
        (evaluationTensorPresheafIso_pure.{c, v, r} J B τ n M N U x y))

@[irreducible] private def evaluationTensorIso (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) :
    (evaluation.{c, v, max c v r} J B τ n).obj
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N) ≅
      ordinaryTensor.{c, v, r} J (B n)
        ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) :=
  (@asIso _ _ _ _ (evaluationTensorComparison.{c, v, r} J B τ n M N)
    (evaluationTensorComparison_isIso.{c, v, r} J B τ n M N)).symm

private theorem evaluationTensorIso_fac (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) :
    evaluationTensorComparison.{c, v, r} J B τ n M N ≫
        (evaluationTensorIso.{c, v, r} J B τ n M N).hom = 𝟙 _ := by
  have := evaluationTensorComparison_isIso.{c, v, r} J B τ n M N
  unfold evaluationTensorIso
  exact IsIso.hom_inv_id _

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Ordinary evaluation preserves tensor by the identity on local pure tensors.
Source: Zheng 4.1; Stacks 03EK (auxiliary; not a blueprint node).
Proof: restriction to a vertical slice commutes with sectionwise tensor and
sheafification. Map each pure tensor to the identical tensor in that slice.
The sheafification universal property gives a natural isomorphism. Local pure
tensors generate, so the displayed section formula determines it uniquely. -/
theorem ordinaryEvaluationTensor_existsUnique (n : ℕ) :
    ∃! δ : ∀ M N : Systems.{c, v, max c v r} J B τ,
      (evaluation.{c, v, max c v r} J B τ n).obj
          (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r}
            J B τ) M N) ≅
        ordinaryTensor.{c, v, r} J (B n) ((evaluation.{c, v, max c v r} J B τ n).obj M)
          ((evaluation.{c, v, max c v r} J B τ n).obj N),
      ∀ (M N : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
        (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop)))
        (x' : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U)
        (y' : ((evaluation.{c, v, max c v r} J B τ n).obj N).val.obj U)
        (z : ((evaluation.{c, v, max c v r} J B τ n).obj
          (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r}
            J B τ) M N)).val.obj U),
        HEq x x' → HEq y y' →
        HEq z (tensorSection.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v
          r} J B τ)
          M N (op (n, U.unop)) x y) →
        (δ M N).hom.val.app U z =
          tensorSection.{c, v, r} J (B n) ((evaluation.{c, v, max c v r} J B τ n).obj M)
            ((evaluation.{c, v, max c v r} J B τ n).obj N) U x' y' := by
  have hc (M N : Systems.{c, v, max c v r} J B τ) :=
    evaluationTensorComparison_isIso.{c, v, r} J B τ n M N
  let δ (M N : Systems.{c, v, max c v r} J B τ) :
      (evaluation.{c, v, max c v r} J B τ n).obj
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N) ≅
      ordinaryTensor.{c, v, r} J (B n)
        ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) :=
    evaluationTensorIso.{c, v, r} J B τ n M N
  refine ⟨δ, ?_, ?_⟩
  · intro M N U x y x' y' z hx hy hz
    have := hc M N
    have hx' : x = x' := eq_of_heq hx
    have hy' : y = y' := eq_of_heq hy
    have hz' := eq_of_heq hz
    subst x'
    subst y'
    subst z
    have h := evaluationTensorComparison_pure.{c, v, r} J B τ n M N U x y
    have hi := congrArg (fun z ↦ (δ M N).hom.val.app U z) h
    have hh := congrArg (fun k ↦ k.val.app U
      (tensorSection.{c, v, r} J (B n)
        ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) U x y))
      (evaluationTensorIso_fac.{c, v, r} J B τ n M N)
    exact hi.symm.trans hh
  · intro γ hγ
    funext M N
    have := hc M N
    apply Iso.ext
    apply (cancel_epi (evaluationTensorComparison.{c, v, r} J B τ n M N)).mp
    apply tensorSection_hom_ext.{c, v, r} J (B n)
      ((evaluation.{c, v, max c v r} J B τ n).obj M)
      ((evaluation.{c, v, max c v r} J B τ n).obj N)
    intro U x y
    change (γ M N).hom.val.app U
      ((evaluationTensorComparison.{c, v, r} J B τ n M N).val.app U
        (tensorSection.{c, v, r} J (B n)
          ((evaluation.{c, v, max c v r} J B τ n).obj M)
          ((evaluation.{c, v, max c v r} J B τ n).obj N) U x y)) = _
    rw [evaluationTensorComparison_pure.{c, v, r} J B τ n M N U x y]
    have h := hγ M N U x y x y _ (HEq.refl _) (HEq.refl _) (HEq.refl _)
    have hh := congrArg (fun k ↦ k.val.app U
      (tensorSection.{c, v, r} J (B n)
        ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) U x y))
      (evaluationTensorIso_fac.{c, v, r} J B τ n M N)
    exact h.trans hh.symm

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The uniquely section-normalized ordinary tensor evaluation.
Source: Zheng 4.1; Stacks 03EK (auxiliary; not a blueprint node). -/
def ordinaryEvaluationTensor (n : ℕ) :=
  (ordinaryEvaluationTensor_existsUnique.{c, v, r} J B τ n).exists.choose

-- The structure records this unique comparison; it does not compute its chosen witness.
attribute [local irreducible] ordinaryEvaluationTensor

set_option genInjectivity false in
set_option genSizeOf false in
set_option genSizeOfSpec false in
/-- The full ordinary-derived system calculus over one fixed ring tower.
Every proposition field is a specific mathematical assertion about the displayed
categories, functors, maps or adjunctions; none is an unconstrained Prop parameter.
Source: Zheng 4.1 and 4.10; Stacks 06YY, 07A4, 08J7--08JB
(auxiliary; not a blueprint node). -/
structure Data where
  /-- Grothendieck abelianness of the actual category of module systems. -/
  grothendieck : IsGrothendieckAbelian.{max c v r} (Systems.{c, v, max c v r} J B τ)
  /-- Exactness is componentwise, in the actual abelian category. -/
  componentwise : ∀ s : ShortComplex (Systems.{c, v, max c v r} J B τ),
    s.Exact ↔ ∀ n : ℕ, (s.map (evaluation.{c, v, max c v r} J B τ n)).Exact
  /-- Exactness of the derived evaluation functors. -/
  evaluation_triangulated : ∀ n : ℕ,
    ∃ (_ : (e.{c, v, max c v r} J B τ n).CommShift ℤ), (e.{c, v, max c v r} J B τ n).IsTriangulated
  /-- The evaluations jointly detect isomorphisms, without detecting equality of maps. -/
  detects : ∀ {M N : DS.{c, v, max c v r} J B τ} (f : M ⟶ N),
    (∀ n : ℕ, IsIso ((e.{c, v, max c v r} J B τ n).map f)) → IsIso f
  /-- Actual derived scalar extension for every composite coefficient homomorphism. -/
  scalar : ∀ {m n : ℕ} (h : n ≤ m),
    ScalarData.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)
  /-- Tensor reassociation for iterated coefficient extension. -/
  scalarComposition : ∀ {l m n : ℕ} (h : n ≤ m) (k : m ≤ l),
    (scalar k).T ⋙ (scalar h).T ≅ (scalar (h.trans k)).T
  /-- Reassociation is the left-adjoint comparison of actual scalar restrictions. -/
  scalarComposition_transpose : ∀ {l m n : ℕ} (h : n ≤ m) (k : m ≤ l)
    (P : D.{c, v, max c v r} J (B l)) (Q : D.{c, v, max c v r} J (B n))
    (f : (scalar (h.trans k)).T.obj P ⟶ Q),
    ((scalar k).adjunction.homEquiv _ _)
      (((scalar h).adjunction.homEquiv _ _)
        ((scalarComposition h k).hom.app P ≫ f)) =
      ((scalar (h.trans k)).adjunction.homEquiv _ _) f ≫
        (restrictionComposition.{c, v, max c v r} J B τ h k).inv.app Q
  /-- The actual reduction maps satisfy the tensor-associator cocycle. -/
  reduction_cocycle : ∀ {l m n : ℕ} (h : n ≤ m) (k : m ≤ l)
    (M : DS.{c, v, max c v r} J B τ),
    (scalar h).T.map (reduction.{c, v, max c v r} J B τ k (scalar k) M) ≫
        reduction.{c, v, max c v r} J B τ h (scalar h) M =
      (scalarComposition h k).hom.app ((e.{c, v, max c v r} J B τ l).obj M) ≫
        reduction.{c, v, max c v r} J B τ (h.trans k) (scalar (h.trans k)) M
  /-- System tensor is covariant in both variables and closed against the recorded Hom. -/
  closed : Closed.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ)
  /-- Its actual K-flat total-complex model. -/
  tensorModels : Models.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ) closed
  /-- The same closed structure at each actual coefficient level. -/
  levelClosed : ∀ n : ℕ, Closed.{c, v, r} J (B n)
  /-- The levelwise total tensor models. -/
  levelTensorModels : ∀ n : ℕ, Models.{c, v, r} J (B n) (levelClosed n)
  /-- The natural tensor evaluation isomorphism. -/
  tensorEvaluation : ∀ n : ℕ,
    closed.tensor ⋙ e.{c, v, max c v r} J B τ n ≅
      ((e.{c, v, max c v r} J B τ n).prod (e.{c, v, max c v r} J B τ n)) ⋙ (levelClosed n).tensor
  /-- The evaluation comparison is the localized tensor comparison model, with
  its ordinary map fixed by the sectionwise pure-tensor comparison below. -/
  tensorEvaluationModel : ∀ n : ℕ,
    TensorComparisonModel.{c, v, r}
      (coefficientSequenceTopology J) J
      (systemRing.{c, v, max c v r} J B τ) (B n)
      (evaluation.{c, v, max c v r} J B τ n)
      closed (levelClosed n) tensorModels (levelTensorModels n)
      (tensorEvaluation n)
  /-- The ordinary component of the evaluation model is exactly the
  identity-on-sections comparison, so it cannot be sign-twisted. -/
  tensorEvaluationModel_ordinary : ∀ (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ),
    (tensorEvaluationModel n).ordinary M N =
      ordinaryEvaluationTensor.{c, v, r} J B τ n M N
  /-- Tensor commutes with the actual derived coefficient extension. -/
  scalarTensor : ∀ {m n : ℕ} (h : n ≤ m),
    (levelClosed m).tensor ⋙ (scalar h).T ≅
      ((scalar h).T.prod (scalar h).T) ⋙ (levelClosed n).tensor
  /-- Scalar/tensor comparison on K-flat representatives.  Its counit square
  uses the actual derived change-of-rings model, and its ordinary comparison is
  fixed on pure tensors. -/
  scalarTensorModel : ∀ {m n : ℕ} (h : n ≤ m),
    ScalarTensorComparisonModel.{c, v, r} J (B m) (B n)
      (coefficientMap.{c, v, max c v r} J B τ h) (scalar h)
      (levelClosed m) (levelClosed n)
      (levelTensorModels m) (levelTensorModels n) (scalarTensor h)
  /-- The cartesian-input internal-Hom comparison, natural in the second input. -/
  homEvaluation : ∀ (M : DS.{c, v, max c v r} J B τ)
    (_hM : Normalized.{c, v, max c v r} J B τ scalar M) (n : ℕ),
    Prod.sectR (op M) (DS.{c, v, max c v r} J B τ) ⋙
      internalHom.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) ⋙
        e.{c, v, max c v r} J B τ n ≅
      e.{c, v, max c v r} J B τ n ⋙
        Prod.sectR (op ((e.{c, v, max c v r} J B τ n).obj M)) (D.{c, v, max c v r} J (B n)) ⋙
          internalHom.{c, v, r} J (B n)
  /-- The comparison carries the actual system evaluation to the level evaluation. -/
  homEvaluation_evaluation : ∀ (M N : DS.{c, v, max c v r} J B τ)
    (hM : Normalized.{c, v, max c v r} J B τ scalar M) (n : ℕ),
    (levelClosed n).tensor.map
        (Prod.mkHom ((homEvaluation M hM n).hom.app N)
          (𝟙 ((e.{c, v, max c v r} J B τ n).obj M))) ≫
        (levelClosed n).evaluation ((e.{c, v, max c v r} J B τ n).obj M)
          ((e.{c, v, max c v r} J B τ n).obj N) =
      (tensorEvaluation n).inv.app
        ((internalHom.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ)).obj (op M, N), M) ≫
        (e.{c, v, max c v r} J B τ n).map (closed.evaluation M N)

namespace Data

variable (A : Data.{c, v, r} J B τ)

end Data

/-- The actual underlying sheaf of sets of a module sheaf.
Source: Stacks 03D1 (auxiliary; not a blueprint node). -/
abbrev underlying (R : Sheaf J CommRingCat.{max c v r}) :=
  SheafOfModules.toSheaf (ring.{c, v, max c v r} J R) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max c v r})

/-- Pure-tensor normalization of the inverse-image tensor comparison, tested
on all generalized sections. It fixes the ordinary comparison before deriving.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def InverseTensorPure {C' : Type c} [Category.{v} C']
    [EssentiallySmall.{max c v r} C'] (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf J' CommRingCat.{max c v r})
    (I : SheafOfModules.AlgebraicInverseImage uInv R S)
    (μ : ∀ M N : Mod.{c, v, max c v r} J R,
      I.modules.obj (ordinaryTensor.{c, v, r} J R M N) ≅
        ordinaryTensor.{c, v, r} J' S (I.modules.obj M) (I.modules.obj N)) : Prop :=
  ∀ (M N : Mod.{c, v, max c v r} J R) (Z : Sheaf J (Type (max c v r)))
    (x : Z ⟶ (underlying.{c, v, r} J R).obj M) (y : Z ⟶ (underlying.{c, v, r} J R).obj N)
    (z : Z ⟶ (underlying.{c, v, r} J R).obj (ordinaryTensor.{c, v, r} J R M N)),
    (∀ (U : Cᵒᵖ) (a : Z.obj.obj U),
      z.hom.app U a = tensorSection.{c, v, r} J R M N U (x.hom.app U a) (y.hom.app U a)) →
    ∀ (V : C'ᵒᵖ) (a : (uInv.obj Z).obj.obj V),
      ((μ M N).hom.val.app V)
        (((I.moduleUnderlying.inv.app (ordinaryTensor.{c, v, r} J R M N)).hom.app V)
          ((uInv.map z).hom.app V a)) =
        tensorSection.{c, v, r} J' S (I.modules.obj M) (I.modules.obj N) V
          (((I.moduleUnderlying.inv.app M).hom.app V) ((uInv.map x).hom.app V a))
          (((I.moduleUnderlying.inv.app N).hom.app V) ((uInv.map y).hom.app V a))

section ScalarSystems

variable (F : ℕ → Sheaf J CommRingCat.{max c v r})
  (σ : ∀ n : ℕ, F (n + 1) ⟶ F n) (α : ∀ n : ℕ, B n ⟶ F n)
  (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n)

/-- Derived extension for a compatible coefficient-system morphism.
Its level comparison is fixed by transposition against the identity-on-sections
restriction comparison, so it describes the canonical extension and its maps.
Source: Stacks 06YY, 07A6 (auxiliary; not a blueprint node). -/
structure ScalarSystems where
  /-- The actual ringed-system derived change of rings. -/
  scalar : ScalarData.{c, v, max c v r}
    (systemMap.{c, v, max c v r} J B τ F σ α hα)
  /-- The actual derived change of rings at each coefficient level. -/
  levels : ∀ n : ℕ, ScalarData.{c, v, max c v r} (α n)
  /-- Extension evaluates to tensor with F_n over B_n. -/
  evaluation : ∀ n : ℕ,
    scalar.T ⋙ e.{c, v, max c v r} J F σ n ≅
      e.{c, v, max c v r} J B τ n ⋙ (levels n).T
  /-- The comparison is precisely the adjunction transpose of restriction evaluation. -/
  transpose_evaluation : ∀ (n : ℕ) (M : DS.{c, v, max c v r} J B τ)
    (N : DS.{c, v, max c v r} J F σ) (f : scalar.T.obj M ⟶ N),
    (e.{c, v, max c v r} J B τ n).map ((scalar.adjunction.homEquiv _ _) f) ≫
        (restrictionEvaluation.{c, v, max c v r} J B τ F σ α hα n).hom.app N =
      ((levels n).adjunction.homEquiv _ _)
        ((evaluation n).inv.app M ≫ (e.{c, v, max c v r} J F σ n).map f)

end ScalarSystems

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local semireducible] systemRing ringPresheaf rings

section OpenLocalization

variable (U : C)

end OpenLocalization

end WeilConjectures.SemilinearSections
