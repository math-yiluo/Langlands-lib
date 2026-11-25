/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! Ordinary part of the normalized image realization.

(blueprint: lem-pur-etale-brown-image-realization-ordinary)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

/-- Evaluating a constant generator on a singleton section gives its sheafification image.
Proof: the constant singleton is already a sheaf, so every section comes from its unit.
The assertion then follows from the sheafification adjunction triangle identity. -/
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

/-- Construction of the section-normalized ordinary comparison.
Source: Zheng, Construction 5.15; Stacks 03CY and 07A4.
(blueprint: lem-pur-etale-brown-image-realization-ordinary).

The comparison is induced by the ordinary right-underlying comparison and its
section formula. The construction is independent of properness and finiteness.
-/
theorem etaleBrownImageRealization_ordinaryRight_exists
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW) :
    ∃ ordinaryRight : A.right n ⋙ strictEtaleBrownConstant O t W n ≅
        strictEtaleBrownConstant O t V n ⋙
          Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g,
      ∀ (M : strictEtaleLevel V O t n) (U : W.Etaleᵒᵖ)
        (x : ((A.right n).obj M).val.obj U),
        (ordinaryRight.hom.app M).hom.app U x =
          ((A.rightUnderlying n).hom.app M).hom.app U x := by
  let _ := RV
  let _ := RW
  let p := MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g
  let L := Scheme.etaleSetPullback g
  let adj := strictEtaleSetAdjunction g
  let Q := coefficientUnderlying (J := W.smallEtaleTopology)
    O t n
  let QV := coefficientUnderlying (J := V.smallEtaleTopology)
    O t n
  let I := A.lift n
  let R := A.right n
  let β := A.rightUnderlying n
  have hβ (M) : β.hom.app M = adj.homEquiv _ _
      (I.moduleUnderlying.inv.app (R.obj M) ≫
        QV.map ((A.levelAdj n).counit.app M)) := by
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
  have hunit (M) (T : Sheaf W.smallEtaleTopology (Type (u + 1)))
      (a : T ⟶ Q.obj (R.obj M)) (U : W.Etaleᵒᵖ) (z : T.obj.obj U) :
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
  have hadd (M) (U : W.Etaleᵒᵖ) (x y : (R.obj M).val.obj U) :
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
  have hsmul (M) (U : W.Etaleᵒᵖ) (q : strictEtaleBrownRing O t n)
      (x : (R.obj M).val.obj U) :
      (β.hom.app M).hom.app U
        ((toSheafify W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj
          (CommRingCat.of (strictEtaleBrownRing O t n)))).app U q • x) =
      (toSheafify (V.smallEtaleTopology) ((Functor.const V.Etaleᵒᵖ).obj
        (CommRingCat.of (strictEtaleBrownRing O t n)))).app
          (p.op.obj U) q •
        (show M.val.obj (p.op.obj U) from
          (β.hom.app M).hom.app U x) := by
    let Tmod := Q.obj (R.obj M)
    let S := (constantSheaf W.smallEtaleTopology (Type (u + 1))).obj PUnit
    let T := CategoryTheory.MonoidalCategory.tensorObj S Tmod
    let a : T ⟶ _ := CartesianMonoidalCategory.fst S Tmod ≫
      coefficientConstantSection (J := W.smallEtaleTopology)
        O t n q
    let b : T ⟶ Tmod := CartesianMonoidalCategory.snd S Tmod
    let mulMap : T ⟶ Tmod := ⟨{
      app := fun U₀ ↦ ↾fun z ↦
        (show (coefficientQuotientSheaf (J := W.smallEtaleTopology)
          O t n).obj.obj U₀
            from a.hom.app U₀ z) • (show (R.obj M).val.obj U₀ from z.2)
      naturality := by
        intro U₀ Z f
        ext z
        have hn := congrArg (fun k ↦ k z) (a.hom.naturality f).symm
        change (coefficientQuotientSheaf (J := W.smallEtaleTopology)
          O t n).obj.map f
            (a.hom.app U₀ z) = a.hom.app Z (T.obj.map f z) at hn
        symm
        change (R.obj M).val.map f
          ((show (coefficientQuotientSheaf (J := W.smallEtaleTopology)
            O t n).obj.obj U₀
              from a.hom.app U₀ z) • (show (R.obj M).val.obj U₀ from z.2)) =
          (show (coefficientQuotientSheaf (J := W.smallEtaleTopology)
            O t n).obj.obj Z
              from a.hom.app Z (T.obj.map f z)) •
                (show (R.obj M).val.obj Z from (R.obj M).val.map f z.2)
        rw [(R.obj M).val.map_smul]
        exact congrArg (fun c : (coefficientQuotientSheaf
          (J := W.smallEtaleTopology) O
          t n).obj.obj Z ↦
            c • (show (R.obj M).val.obj Z from (R.obj M).val.map f z.2)) hn }⟩
    let z : T.obj.obj U :=
      ((toSheafify W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj
        (PUnit.{u + 2} : Type (u + 1)))).app U PUnit.unit, x)
    have ha : a.hom.app U z =
        (toSheafify W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj
          (CommRingCat.of (strictEtaleBrownRing O t n)))).app U q :=
      constantSection_apply W.smallEtaleTopology _ q U z.1
    have h := I.moduleSMul (R.obj M) T a b mulMap (fun _ _ ↦ rfl)
      (p.op.obj U) ((adj.unit.app T).hom.app U z)
    have hc : L.map a ≫ I.ringUnderlying.hom =
        L.map (CartesianMonoidalCategory.fst S Tmod) ≫ A.singleton.hom ≫
          coefficientConstantSection (J := V.smallEtaleTopology)
            O t n q := by
      dsimp only [a]
      rw [L.map_comp, Category.assoc, A.constants]
    have hc' := congrArg (fun f ↦ f.hom.app (p.op.obj U)
      ((adj.unit.app T).hom.app U z)) hc
    have ht := hunit M T mulMap U z
    have hb := hunit M T b U z
    change (β.hom.app M).hom.app U
      ((show (coefficientQuotientSheaf (J := W.smallEtaleTopology)
        O t n).obj.obj U from a.hom.app U z) • x) = _ at ht
    change (β.hom.app M).hom.app U x = _ at hb
    dsimp only [id] at h
    have hconst := constantSection_apply (V.smallEtaleTopology)
      (strictEtaleBrownRing O t n) q (p.op.obj U)
      ((A.singleton.hom).hom.app (p.op.obj U)
        ((L.map (CartesianMonoidalCategory.fst S Tmod)).hom.app
          (p.op.obj U) ((adj.unit.app T).hom.app U z)))
    change (I.ringUnderlying.hom).hom.app (p.op.obj U)
      ((L.map a).hom.app (p.op.obj U)
        ((adj.unit.app T).hom.app U z)) = _ at hc'
    have hs := hc'.trans hconst
    have ht' := (congrArg (fun a : (coefficientQuotientSheaf (J := W.smallEtaleTopology)
      O t n).obj.obj U ↦ (β.hom.app M).hom.app U (a • x)) ha).symm.trans ht
    exact ht'.trans ((congrArg
      (fun x ↦ ((A.levelAdj n).counit.app M).val.app (p.op.obj U) x) h).trans
        ((((A.levelAdj n).counit.app M).val.app (p.op.obj U)).hom.map_smul _ _ |>.trans
          (congrArg₂ (fun a : (coefficientQuotientSheaf (J := V.smallEtaleTopology)
            O t n).obj.obj (p.op.obj U) ↦ fun x : M.val.obj (p.op.obj U) ↦ a • x)
              hs hb.symm)))
  let F := R ⋙ strictEtaleBrownConstant O t W n
  let G := strictEtaleBrownConstant O t V n ⋙
    Etale.lowerStar (ModuleCat.{u + 1}
      (strictEtaleBrownRing O t n)) g
  let γ : F ⟶ G := {
    app := fun M ↦ { hom := {
      app := fun U ↦ ModuleCat.ofHom
        (X := (F.obj M).obj.obj U) (Y := (G.obj M).obj.obj U) {
        toFun := fun x ↦ (β.hom.app M).hom.app U x
        map_add' := fun x y ↦ hadd M U x y
        map_smul' := by
          intro c x
          exact hsmul M U c x }
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
    have : IsIso ((sheafToPresheaf W.smallEtaleTopology _).map (γ.app M)) :=
      NatIso.isIso_of_isIso_app (γ.app M).hom
    exact isIso_of_reflects_iso (γ.app M) (sheafToPresheaf W.smallEtaleTopology _)
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  refine ⟨asIso γ, ?_⟩
  · intro M U x
    rfl

end AlgebraicGeometry
