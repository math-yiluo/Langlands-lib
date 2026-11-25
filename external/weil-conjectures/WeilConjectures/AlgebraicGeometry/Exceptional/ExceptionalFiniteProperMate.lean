/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageBoundedBelow
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # The finite proper direct-image mate in the strict coefficient presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleLevelDerived exceptionalProLevelDerived

section OrdinaryRealization
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]

private def finiteConstantModule (J : GrothendieckTopology C) (A : CommRingCat.{u + 1}) :
    SheafOfModules.{u + 1} ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf J CommRingCat.{u + 1}).obj A)) ⥤
        Sheaf J (ModuleCat.{u + 1} A) where
  obj N :=
    let P : PresheafOfModules.{u + 1}
        ((Functor.const Cᵒᵖ).obj (RingCat.of A)) :=
      (PresheafOfModules.restrictScalars
        (Functor.whiskerRight (toSheafify J
          ((Functor.const Cᵒᵖ).obj A))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))).obj N.val
    { obj :=
        { obj := fun U ↦ P.obj U
          map := fun h ↦ P.map h
          map_id := fun _ ↦ by ext x; simp; rfl
          map_comp := fun _ _ ↦ by ext x; simp; rfl }
      property := by
        apply Presheaf.isSheaf_of_isSheaf_comp J _
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
        exact N.isSheaf }
  map h := ObjectProperty.homMk
    { app := fun U ↦ (ModuleCat.restrictScalars
        (((toSheafify J
          ((Functor.const Cᵒᵖ).obj A)).app U).hom)).map (h.val.app U)
      naturality := fun {_ _} g ↦ by
        ext x
        exact PresheafOfModules.naturality_apply h.val g x }
  map_id _ := by ext U x; rfl
  map_comp _ _ := by ext U x; rfl

private theorem constantSection_apply
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type (u + 1))] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1})]
    (A : Type (u + 1)) [CommRing A] (a : A) (U : Cᵒᵖ)
    (z : ((constantSheaf J (Type (u + 1))).obj PUnit).obj.obj U) :
    ((((sheafificationAdjunction J (Type (u + 1))).homEquiv _
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj
        ((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of A)))).symm
      ((Functor.const Cᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{u + 2}) ↦ a)) ≫
        Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
          (CategoryTheory.forget CommRingCat.{u + 1}))).hom.app U z) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a := by
  let T := (Functor.const Cᵒᵖ).obj (PUnit.{u + 2} : Type (u + 1))
  have hT : Presheaf.IsSheaf J T := Sheaf.tensorUnit_isSheaf J
  have : IsIso (toSheafify J T) := isIso_toSheafify J hT
  obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((toSheafify J T).app U)).surjective z
  have h := ((sheafificationAdjunction J (Type (u + 1))).homEquiv _
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj
        ((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of A)))).apply_symm_apply
    ((Functor.const Cᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{u + 2}) ↦ a)) ≫
      Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
        (CategoryTheory.forget CommRingCat.{u + 1}))
  exact congrArg (fun f ↦ f.app U t) h

private def finiteRestrictionCancel {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}}
    (α : R ⟶ S) (β : S ⟶ R) (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars.{u + 1} β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{u + 1} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private theorem finiteRestrictionEquivalence {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}} (e : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} e.hom).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars e.hom)
    (SheafOfModules.restrictScalars e.inv)
    (finiteRestrictionCancel e.inv e.hom e.inv_hom_id).symm
    (finiteRestrictionCancel e.hom e.inv e.hom_inv_id)).isEquivalence_functor

private theorem constantRingScalar
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasWeakSheafify J RingCat.{u + 1}] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    (A : Type (u + 1)) [CommRing A] (U : Cᵒᵖ) (a : A) :
    (((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
      (CommRingCat.of A)).hom.app U)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a := by
  have h := sheafComposeIso_hom_fac J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  change ((sheafifyComposeIso J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U)
      (((presheafToSheaf J RingCat.{u + 1}).map
        ((Functor.compConstIso Cᵒᵖ
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
            (CommRingCat.of A))).hom.app U
              ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a)) = _
  have hi : ((Functor.compConstIso Cᵒᵖ
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
        (CommRingCat.of A)) = 𝟙 _ := rfl
  rw [hi, CategoryTheory.Functor.map_id]
  exact congrArg (fun f ↦ f.app U a) h

private instance finiteForgetRing (J : GrothendieckTopology C) :
    J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  have : EssentiallySmall.{u + 1} C := essentiallySmallSelf.{0} _
  constructor
  intro P Q f hf
  change J.W (Functor.whiskerRight f (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  have hi : Presheaf.IsLocallyInjective J f := hf.isLocallyInjective
  have hs : Presheaf.IsLocallySurjective J f := hf.isLocallySurjective
  apply (J.W_iff_isLocallyBijective _).mpr
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J f x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem J f x⟩

private instance finiteConstantEquivalence (J : GrothendieckTopology C)
    (B : CommRingCat.{u + 1}) : (finiteConstantModule J B).IsEquivalence := by
  let F := SheafOfModules.restrictScalars
    ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app B).inv ⋙
      constantRingModuleRestriction J B
  have h₁ : (SheafOfModules.restrictScalars
      ((constantCommuteCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app B).inv).IsEquivalence :=
    finiteRestrictionEquivalence
      ((constantCommuteCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app B).symm
  obtain ⟨e, he, _, _, _⟩ := (constant_ring_module_sheaves J B).1
  have h₂ : (constantRingModuleRestriction J B).IsEquivalence := by
    rw [← he]
    exact e.isEquivalence_functor
  have hF : F.IsEquivalence := Functor.isEquivalence_trans _ _
  let δ : finiteConstantModule J B ⟶ F := {
    app := fun M ↦ { hom := {
      app := fun U ↦ ModuleCat.ofHom
        (X := ((finiteConstantModule J B).obj M).obj.obj U)
        (Y := (F.obj M).obj.obj U) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro b x
          change (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U b •
              (show M.val.obj U from x) =
            (((constantCommuteCompose J
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app B).hom.app U)
                ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app U b) •
                  (show M.val.obj U from x)
          rw [constantRingScalar] }
      naturality := by intros; ext; rfl } }
    naturality := by intros; ext; rfl }
  have hδ (M) : IsIso (δ.app M) := by
    have hpoint (U) : IsIso ((δ.app M).hom.app U) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact Function.bijective_id
    have : IsIso ((sheafToPresheaf J _).map (δ.app M)) :=
      NatIso.isIso_of_isIso_app (δ.app M).hom
    exact isIso_of_reflects_iso (δ.app M) (sheafToPresheaf J _)
  have : IsIso δ := NatIso.isIso_of_isIso_app δ
  exact Functor.isEquivalence_of_iso (asIso δ).symm

private instance finiteConstantAdditive (J : GrothendieckTopology C)
    (B : CommRingCat.{u + 1}) : (finiteConstantModule J B).Additive where
  map_add := by intros; ext; rfl

variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (p : C ⥤ D) [Functor.IsContinuous p J K]
  (O : Type (u + 1)) [CommRing O] (ell : O)
  (A : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell _ _
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous p (Type (u + 1)) J K))

-- Check the transported addition and scalar actions on generalized sections.
private theorem finiteConstantRight (n : ℕ) :
    ∃ e : A.right n ⋙ finiteConstantModule J
        (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))) ≅
      finiteConstantModule K
        (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))) ⋙
          p.sheafPushforwardContinuous
            (ModuleCat.{u + 1} (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))) J K,
      ∀ M U (x : ((A.right n).obj M).val.obj U),
        (e.hom.app M).hom.app U x =
          ((A.rightUnderlying n).hom.app M).hom.app U x := by
  let L := Functor.sheafPullbackConstruction.sheafPullback p (Type (u + 1)) J K
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous p (Type (u + 1)) J K
  let Q := coefficientUnderlying (J := J)
    O ell n
  let V := coefficientUnderlying (J := K)
    O ell n
  let I := A.lift n
  let R := A.right n
  let β := A.rightUnderlying n
  have hβ (M) : β.hom.app M = adj.homEquiv _ _
      (I.moduleUnderlying.inv.app (R.obj M) ≫
        V.map ((A.levelAdj n).counit.app M)) := by
    have hc : (A.levelAdj n).homEquiv (R.obj M) M
        ((A.levelAdj n).counit.app M) = 𝟙 _ := by
      rw [← Adjunction.homEquiv_symm_id]
      exact ((A.levelAdj n).homEquiv (R.obj M) M).apply_symm_apply _
    have h := A.levelTranspose n (R.obj M) M
      ((A.levelAdj n).counit.app M)
    change (A.levelAdj n).homEquiv (R.obj M) M
      ((A.levelAdj n).counit.app M) = 𝟙 _ at hc
    change Q.map ((A.levelAdj n).homEquiv (R.obj M) M
      ((A.levelAdj n).counit.app M)) ≫ β.hom.app M = _ at h
    rw [hc, Q.map_id, Category.id_comp] at h
    exact h
  have hunit (M) (T : Sheaf J (Type (u + 1)))
      (a : T ⟶ Q.obj (R.obj M)) (U : Cᵒᵖ) (z : T.obj.obj U) :
      (β.hom.app M).hom.app U (a.hom.app U z) =
      ((A.levelAdj n).counit.app M).val.app (p.op.obj U)
        ((I.moduleUnderlying.inv.app (R.obj M)).hom.app (p.op.obj U)
          ((L.map a).hom.app (p.op.obj U)
            ((adj.unit.app T).hom.app U z))) := by
    rw [hβ, Adjunction.homEquiv_unit]
    have h := congrArg (fun f ↦ f.hom.app U z) (adj.unit.naturality a)
    change (adj.unit.app (Q.obj (R.obj M))).hom.app U (a.hom.app U z) =
      (L.map a).hom.app (p.op.obj U)
        ((adj.unit.app T).hom.app U z) at h
    exact congrArg (fun x ↦
      ((A.levelAdj n).counit.app M).val.app (p.op.obj U)
        ((I.moduleUnderlying.inv.app (R.obj M)).hom.app
          (p.op.obj U) x)) h
  have hadd (M) (U : Cᵒᵖ) (x y : (R.obj M).val.obj U) :
      (β.hom.app M).hom.app U (x + y) =
        (show M.val.obj (p.op.obj U) from
          (β.hom.app M).hom.app U x) +
        (show M.val.obj (p.op.obj U) from
          (β.hom.app M).hom.app U y) := by
    let Tmod := Q.obj (R.obj M)
    let T := (CategoryTheory.MonoidalCategory.tensorObj Tmod Tmod)
    let a : T ⟶ Tmod := CartesianMonoidalCategory.fst Tmod Tmod
    let b : T ⟶ Tmod := CartesianMonoidalCategory.snd Tmod Tmod
    let t : T ⟶ Tmod := ⟨{
      app := fun Y ↦ ↾fun z ↦
        (show (R.obj M).val.obj Y from z.1) +
          (show (R.obj M).val.obj Y from z.2)
      naturality := by
        intro Y Z f
        ext z
        exact ((R.obj M).val.map f).hom.map_add z.1 z.2 |>.symm }⟩
    have h := I.moduleAdd (R.obj M) T a b t (fun _ _ ↦ rfl)
      (p.op.obj U) ((adj.unit.app T).hom.app U (x, y))
    have ha := hunit M T a U (x, y)
    have hb := hunit M T b U (x, y)
    have ht := hunit M T t U (x, y)
    change (β.hom.app M).hom.app U (x + y) = _ at ht
    change (β.hom.app M).hom.app U x = _ at ha
    change (β.hom.app M).hom.app U y = _ at hb
    dsimp only [id] at h
    exact ht.trans ((congrArg
      (fun x ↦ ((A.levelAdj n).counit.app M).val.app (p.op.obj U) x) h).trans
        ((((A.levelAdj n).counit.app M).val.app (p.op.obj U)).hom.map_add _ _ |>.trans
          (congrArg₂ (fun x y : M.val.obj (p.op.obj U) ↦ x + y) ha.symm hb.symm)))
  have hsmul (M) (U : Cᵒᵖ) (q : O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))
      (x : (R.obj M).val.obj U) :
      (β.hom.app M).hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj
          (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))))).app U q • x) =
      (toSheafify (K) ((Functor.const Dᵒᵖ).obj
        (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))))).app
          (p.op.obj U) q •
        (show M.val.obj (p.op.obj U) from
          (β.hom.app M).hom.app U x) := by
    let Tmod := Q.obj (R.obj M)
    let S := (constantSheaf J (Type (u + 1))).obj PUnit
    let T := CategoryTheory.MonoidalCategory.tensorObj S Tmod
    let a : T ⟶ _ := CartesianMonoidalCategory.fst S Tmod ≫
      coefficientConstantSection (J := J)
        O ell n q
    let b : T ⟶ Tmod := CartesianMonoidalCategory.snd S Tmod
    let t : T ⟶ Tmod := ⟨{
      app := fun U₀ ↦ ↾fun z ↦
        (show (coefficientQuotientSheaf (J := J)
          O ell n).obj.obj U₀
            from a.hom.app U₀ z) • (show (R.obj M).val.obj U₀ from z.2)
      naturality := by
        intro U₀ Z f
        ext z
        have hn := congrArg (fun k ↦ k z) (a.hom.naturality f).symm
        change (coefficientQuotientSheaf (J := J)
          O ell n).obj.map f
            (a.hom.app U₀ z) = a.hom.app Z (T.obj.map f z) at hn
        symm
        change (R.obj M).val.map f
          ((show (coefficientQuotientSheaf (J := J)
            O ell n).obj.obj U₀
              from a.hom.app U₀ z) • (show (R.obj M).val.obj U₀ from z.2)) =
          (show (coefficientQuotientSheaf (J := J)
            O ell n).obj.obj Z
              from a.hom.app Z (T.obj.map f z)) •
                (show (R.obj M).val.obj Z from (R.obj M).val.map f z.2)
        rw [(R.obj M).val.map_smul]
        exact congrArg (fun c : (coefficientQuotientSheaf
          (J := J) O ell n).obj.obj Z ↦
            c • (show (R.obj M).val.obj Z from (R.obj M).val.map f z.2)) hn }⟩
    let z : T.obj.obj U :=
      ((toSheafify J ((Functor.const Cᵒᵖ).obj
        (PUnit.{u + 2} : Type (u + 1)))).app U PUnit.unit, x)
    have ha : a.hom.app U z =
        (toSheafify J ((Functor.const Cᵒᵖ).obj
          (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))))).app U q :=
      constantSection_apply J _ q U z.1
    have h := I.moduleSMul (R.obj M) T a b t (fun _ _ ↦ rfl)
      (p.op.obj U) ((adj.unit.app T).hom.app U z)
    have hc : L.map a ≫ I.ringUnderlying.hom =
        L.map (CartesianMonoidalCategory.fst S Tmod) ≫ A.singleton.hom ≫
          coefficientConstantSection (J := K)
            O ell n q := by
      dsimp only [a]
      rw [L.map_comp, Category.assoc, A.constants]
    have hc' := congrArg (fun f ↦ f.hom.app (p.op.obj U)
      ((adj.unit.app T).hom.app U z)) hc
    have ht := hunit M T t U z
    have hb := hunit M T b U z
    change (β.hom.app M).hom.app U
      ((show (coefficientQuotientSheaf (J := J)
        O ell n).obj.obj U from a.hom.app U z) • x) = _ at ht
    change (β.hom.app M).hom.app U x = _ at hb
    dsimp only [id] at h
    have hconst := constantSection_apply K
      (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)) q (p.op.obj U)
      ((A.singleton.hom).hom.app (p.op.obj U)
        ((L.map (CartesianMonoidalCategory.fst S Tmod)).hom.app
          (p.op.obj U) ((adj.unit.app T).hom.app U z)))
    change (I.ringUnderlying.hom).hom.app (p.op.obj U)
      ((L.map a).hom.app (p.op.obj U)
        ((adj.unit.app T).hom.app U z)) = _ at hc'
    have hs := hc'.trans hconst
    have ht' := (congrArg (fun a : (coefficientQuotientSheaf (J := J)
      O ell n).obj.obj U ↦ (β.hom.app M).hom.app U
        (a • x)) ha).symm.trans ht
    exact ht'.trans ((congrArg
      (fun x ↦ ((A.levelAdj n).counit.app M).val.app (p.op.obj U) x) h).trans
        ((((A.levelAdj n).counit.app M).val.app (p.op.obj U)).hom.map_smul _ _ |>.trans
          (congrArg₂ (fun a : (coefficientQuotientSheaf (J := K) O ell n).obj.obj
            (p.op.obj U) ↦ fun x : M.val.obj (p.op.obj U) ↦ a • x) hs hb.symm)))
  let B := CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))
  let F := R ⋙ finiteConstantModule J B
  let G := finiteConstantModule K B ⋙ p.sheafPushforwardContinuous (ModuleCat B) J K
  let γ : F ⟶ G := {
    app := fun M ↦ { hom := {
      app := fun U ↦ ModuleCat.ofHom
        (X := (F.obj M).obj.obj U) (Y := (G.obj M).obj.obj U) {
        toFun := fun x ↦ (β.hom.app M).hom.app U x
        map_add' := fun x y ↦ hadd M U x y
        map_smul' := fun q x ↦ hsmul M U q x }
      naturality := by
        intro U V f
        ext x
        exact congrArg (fun k ↦ k x) ((β.hom.app M).hom.naturality f) } }
    naturality := by
      intro M N f
      ext U x
      exact congrArg (fun k ↦ k.hom.app U x) (β.hom.naturality f) }
  have hγ (M) : IsIso (γ.app M) := by
    have hpoint (U) : IsIso ((γ.app M).hom.app U) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact ConcreteCategory.bijective_of_isIso ((β.hom.app M).hom.app U)
    have : IsIso ((sheafToPresheaf J _).map (γ.app M)) :=
      NatIso.isIso_of_isIso_app (γ.app M).hom
    exact isIso_of_reflects_iso (γ.app M) (sheafToPresheaf J _)
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  exact ⟨asIso γ, fun _ _ _ ↦ rfl⟩

private theorem finiteConstantLeft (n : ℕ) :
    Nonempty ((A.lift n).modules ⋙ finiteConstantModule K
        (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))) ≅
      finiteConstantModule J
        (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))) ⋙
          Functor.sheafPullbackConstruction.sheafPullback p
            (ModuleCat.{u + 1} (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))) J K) := by
  let B := CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))
  have : (finiteConstantModule J B).IsEquivalence := finiteConstantEquivalence J B
  have : (finiteConstantModule K B).IsEquivalence := finiteConstantEquivalence K B
  obtain ⟨β, _⟩ := finiteConstantRight p O ell A n
  let a := A.levelAdj n
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous p (ModuleCat B) J K
  let α := ((mateEquiv a b).symm (.mk _ _ _ _ β.hom))
  have : IsIso α := isIso_inverseMate_of_equivalences a b β
  exact ⟨(asIso α).symm⟩

end OrdinaryRealization

private theorem finiteLocalizedSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : C ⥤ D) (a : A ⥤ C) (b : B ⥤ D)
    [F.Additive] [G.Additive] [a.Additive] [b.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits a] [PreservesFiniteColimits a]
    [PreservesFiniteLimits b] [PreservesFiniteColimits b]
    (DF : DerivedCategory A ⥤ DerivedCategory B)
    (fac : DerivedCategory.Q ⋙ DF ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (e : F ⋙ b ≅ a ⋙ G) :
    Nonempty (DF ⋙ b.mapDerivedCategory ≅ a.mapDerivedCategory ⋙ G.mapDerivedCategory) := by
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory B)
  let δ : DF ≅ F.mapDerivedCategory :=
    ff.preimageIso (fac ≪≫ F.mapDerivedCategoryFactors.symm)
  exact ⟨Functor.isoWhiskerRight δ b.mapDerivedCategory ≪≫
    Functor.mapDerivedCategorySquareIso e⟩

private theorem finiteMateTransport
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    [a.IsEquivalence] [b.IsEquivalence] [c.IsEquivalence] [d.IsEquivalence]
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ≅ F ⋙ H) (E : B)
    (hfixed : ∀ α : G' ⋙ K' ≅ F' ⋙ H',
      IsIso ((mateEquiv adj' adjK' (.mk _ _ _ _ α.hom)).app (b.obj E))) :
    IsIso ((mateEquiv adj adjK (.mk _ _ _ _ θ.hom)).app E) := by
  let η : a ⋙ (G' ⋙ K') ≅ a ⋙ (F' ⋙ H') :=
    (Functor.associator a G' K').symm ≪≫
      Functor.isoWhiskerRight pG.symm K' ≪≫ Functor.associator G c K' ≪≫
      Functor.isoWhiskerLeft G pK.symm ≪≫ (Functor.associator G K d).symm ≪≫
      Functor.isoWhiskerRight θ d ≪≫ Functor.associator F H d ≪≫
      Functor.isoWhiskerLeft F pH ≪≫ (Functor.associator F b H').symm ≪≫
      Functor.isoWhiskerRight pF H' ≪≫ Functor.associator a F' H'
  let ff := (Equivalence.congrLeft (E := D') a.asEquivalence).fullyFaithfulInverse
  let α : G' ⋙ K' ≅ F' ⋙ H' := ff.preimageIso η
  have hα (X : A) : α.hom.app (a.obj X) = η.hom.app X :=
    congr_app (ff.map_preimage η.hom) X
  have hc (X : A) :
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.hom.app X) =
        α.hom.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X) := by
    rw [hα]
    simp only [η, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    simp only [← H'.map_comp_assoc, Iso.hom_inv_id_app, H'.map_id,
      Category.id_comp]
    simp only [Functor.comp_obj, Category.comp_id]
  have h := exchangeMate_cube adj adjK adj' adjK' a b c d pF pG pH pK
    θ.hom α.hom hc E
  have hmF : IsIso (mateEquiv adj adj' (.mk _ _ _ _ pF.inv)) :=
    isIso_mateEquiv_of_isEquivalence adj adj' (.mk _ _ _ _ pF.inv)
  have hmK : IsIso (mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)) :=
    isIso_mateEquiv_of_isEquivalence adjK adjK' (.mk _ _ _ _ pK.inv)
  have := hfixed α
  have hi : IsIso
      (c.map ((mateEquiv adj adjK (.mk _ _ _ _ θ.hom)).app E) ≫
        (mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)).app (H.obj E) ≫
        S'.map (pH.hom.app E)) := by
    rw [h]
    infer_instance
  have : IsIso (c.map ((mateEquiv adj adjK (.mk _ _ _ _ θ.hom)).app E)) := by
    simpa only [isIso_comp_right_iff] using hi
  exact isIso_of_reflects_iso _ c

private theorem finiteCounitImage
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) (X : C) [IsIso (a.unit.app X)] {Y : D} (e : Y ≅ F.obj X) :
    IsIso (a.counit.app Y) := by
  have : IsIso (a.counit.app (F.obj X)) := by
    have h := a.left_triangle_components X
    have : IsIso (F.map (a.unit.app X) ≫ a.counit.app (F.obj X)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (F.map (a.unit.app X)) _
  have h := a.counit.naturality e.hom
  simp only [Functor.id_map] at h
  have : IsIso (a.counit.app Y ≫ e.hom) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ e.hom

private theorem finiteFixedMate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (α : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hM : ∃ n : ℤ, M.IsGE n) :
    IsIso ((mateEquiv
      (Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction
      (ProEtale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction
      (.mk _ _ _ _ α.hom)).app M) := by
  have hr : DerivedCategory.TStructure.t.plus
      ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj M) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso
      (((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlusCompatibility).app
        ⟨M, hM⟩)
      ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlus.obj ⟨M, hM⟩).property
  have hx := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) X M hM
  have hy := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) Y
      ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj M) hr
  obtain ⟨n, hn⟩ := hM
  have := hn
  have := ProEtale.unboundedDirectImageComparison_boundedBelow A g M n
  have hs : IsIso ((ProEtale.derivedComparisonAdjunction
      (ModuleCat.{u + 1} A) Y).counit.app
      ((ProEtale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M))) :=
    finiteCounitImage (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y)
      ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj M)
      (asIso (ProEtale.unboundedDirectImageComparisonMap A g M)).symm
  exact Adjunction.isIso_mateEquiv_app_of_isIso
    (Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction
    (ProEtale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction α
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y)
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X) M

/-- The proper mate is invertible on bounded-below finite etale coefficient objects.
Source: Stacks 099R and 0B65; the canonical finite-coefficient direct-image comparison;
Zheng Lemma 4.10 and Construction 5.15.
(blueprint: lem-sf-exceptional-finite-proper-mate).

Proof: identify modules over the constant quotient-ring sheaf with fixed-ring
module-valued sheaves. The ordinary transpose and scalar conditions identify the
supplied inverse images with the geometric ones. Localize these squares and
transport the supplied proper square along the realization equivalences. For any
such fixed-coefficient square, the comparison units are invertible at a
bounded-below object and its derived etale direct image. The canonical finite
comparison identifies its proetale direct image with an object in the image of
the comparison inverse image, so the counit there is invertible by the triangle
identity. The unit-and-counit criterion proves the mate is invertible. Transport
this conclusion back through the realization equivalences. -/
theorem exceptionalFiniteProperMate
    {O : Type (u + 1)} [CommRing O] {ell : O}
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S : StrictEtaleCompactSupport O ell c}
    {CX : ExceptionalSystemSiteComparison O ell X S.PX}
    {CY : ExceptionalSystemSiteComparison O ell Y S.PY}
    {CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ}
    {P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation}
    (R : ExceptionalSystemCompactificationComparison S CX CY CZ P)
    (n : ℕ) (M : DerivedCategory (strictEtaleLevel c.Z O ell n))
    (hM : ∃ a : ℤ, M.IsGE a) :
    IsIso ((mateEquiv (S.properDerived.level n).adjunction
      (P.val.properDerived.level n).adjunction
      (.mk _ _ _ _ (R.properSquare.derivedLevel n).hom)).app M) := by
  let A := O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)
  let B := CommRingCat.of A
  let rEY : strictEtaleLevel Y O ell n ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A) :=
    finiteConstantModule Y.smallEtaleTopology B
  let rEZ : strictEtaleLevel c.Z O ell n ⥤
      Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A) :=
    finiteConstantModule c.Z.smallEtaleTopology B
  let rPY : coefficientLevelModules (J := Scheme.ProEt.topology Y) O ell n ⥤
      Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A) :=
    finiteConstantModule (Scheme.ProEt.topology Y) B
  let rPZ : coefficientLevelModules (J := Scheme.ProEt.topology c.Z) O ell n ⥤
      Sheaf (Scheme.ProEt.topology c.Z) (ModuleCat.{u + 1} A) :=
    finiteConstantModule (Scheme.ProEt.topology c.Z) B
  have : rEY.Additive := finiteConstantAdditive Y.smallEtaleTopology B
  have : rEZ.Additive := finiteConstantAdditive c.Z.smallEtaleTopology B
  have : rPY.Additive := finiteConstantAdditive (Scheme.ProEt.topology Y) B
  have : rPZ.Additive := finiteConstantAdditive (Scheme.ProEt.topology c.Z) B
  have : rEY.IsEquivalence := finiteConstantEquivalence Y.smallEtaleTopology B
  have : rEZ.IsEquivalence := finiteConstantEquivalence c.Z.smallEtaleTopology B
  have : rPY.IsEquivalence := finiteConstantEquivalence (Scheme.ProEt.topology Y) B
  have : rPZ.IsEquivalence := finiteConstantEquivalence (Scheme.ProEt.topology c.Z) B
  let pEt := MorphismProperty.Over.pullback @Etale ⊤ c.g
  let pPro := MorphismProperty.Over.pullback @WeaklyEtale ⊤ c.g
  have : pEt.IsContinuous Y.smallEtaleTopology c.Z.smallEtaleTopology :=
    Etale.isContinuous_overPullback c.g
  have : PreservesFiniteLimits (S.properImage.lift n).modules :=
    (S.properImage.inverseExact n).1
  have : PreservesFiniteColimits (S.properImage.lift n).modules :=
    (S.properImage.inverseExact n).2
  have : PreservesFiniteLimits (P.val.properImage.lift n).modules :=
    (P.val.properImage.inverseExact n).1
  have : PreservesFiniteColimits (P.val.properImage.lift n).modules :=
    (P.val.properImage.inverseExact n).2
  have : PreservesFiniteLimits (CY.ordinary.lift n).modules :=
    (CY.ordinary.inverseExact n).1
  have : PreservesFiniteColimits (CY.ordinary.lift n).modules :=
    (CY.ordinary.inverseExact n).2
  have : PreservesFiniteLimits (CZ.ordinary.lift n).modules :=
    (CZ.ordinary.inverseExact n).1
  have : PreservesFiniteColimits (CZ.ordinary.lift n).modules :=
    (CZ.ordinary.inverseExact n).2
  obtain ⟨eF⟩ := finiteConstantLeft pEt O ell S.properImage n
  obtain ⟨eK⟩ := finiteConstantLeft pPro O ell P.val.properImage n
  obtain ⟨eG⟩ := finiteConstantLeft (Scheme.toProEt Y) O ell CY.ordinary n
  obtain ⟨eH⟩ := finiteConstantLeft (Scheme.toProEt c.Z) O ell CZ.ordinary n
  obtain ⟨pF⟩ := finiteLocalizedSquare (S.properImage.lift n).modules
    (Etale.upperStar (ModuleCat.{u + 1} A) c.g) rEY rEZ
    (S.properDerived.level n).inverse (S.properDerived.level n).inverseFactors eF
  obtain ⟨pK⟩ := finiteLocalizedSquare (P.val.properImage.lift n).modules
    (ProEtale.upperStar (ModuleCat.{u + 1} A) c.g) rPY rPZ
    (P.val.properDerived.level n).inverse (P.val.properDerived.level n).inverseFactors eK
  obtain ⟨pG⟩ := finiteLocalizedSquare (CY.ordinary.lift n).modules
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y) rEY rPY
    (CY.image.level n).inverse (CY.image.level n).inverseFactors eG
  obtain ⟨pH⟩ := finiteLocalizedSquare (CZ.ordinary.lift n).modules
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) c.Z) rEZ rPZ
    (CZ.image.level n).inverse (CZ.image.level n).inverseFactors eH
  refine finiteMateTransport
    (S.properDerived.level n).adjunction (P.val.properDerived.level n).adjunction
    (Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) c.g).mapDerivedCategoryRightDerivedAdjunction
    (ProEtale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) c.g).mapDerivedCategoryRightDerivedAdjunction
    rEY.mapDerivedCategory rEZ.mapDerivedCategory
    rPY.mapDerivedCategory rPZ.mapDerivedCategory pF pG pH pK
    (R.properSquare.derivedLevel n) M ?_
  intro α
  obtain ⟨a, ha⟩ := hM
  have := ha
  have : IsProper c.g := c.isProper
  exact finiteFixedMate A c.g α (rEZ.mapDerivedCategory.obj M)
    ⟨a, rEZ.isGE_mapDerivedCategory_obj M a⟩

end AlgebraicGeometry
