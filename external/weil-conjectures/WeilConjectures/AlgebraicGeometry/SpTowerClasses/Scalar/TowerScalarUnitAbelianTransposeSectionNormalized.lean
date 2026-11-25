/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerRestrictedScalarAdjunction
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPullback
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerRestrictedScalarAdjunction
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Line.TowerLineTransitionTensor

/-! # Normalized coefficient-unit transpose section calculation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem forgetMapSection (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) {M N : Systems T B} (a : M ⟶ N)
    (n : ℕ) (U : T.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop)))
    (x' : ((F.F.obj M).obj (op n)).obj.obj U) (hx : HEq x' x) :
    HEq (((F.F.map a).app (op n)).hom.app U x')
      (a.val.app (op (n, U.unop)) x) := by
  exact heq_app (F.sections M n U) (F.sections N n U) (F.morphisms a n U) hx

private theorem integerGenerator_cancel (T : Scheme.{u})
    (F : Forget T (Rrings l T)) {N : Systems T (Rrings l T)}
    (a b : F.F.obj (coefficient T (Rrings l T)) ⟶ F.F.obj N)
    (h : integerGenerator T (Rrings l T) F ≫ a =
      integerGenerator T (Rrings l T) F ≫ b) : a = b := by
  let ff := integralForgetFullyFaithful l T F
  obtain ⟨a', ha⟩ := ff.map_surjective a
  obtain ⟨b', hb⟩ := ff.map_surjective b
  rw [← ha, ← hb] at h ⊢
  apply congrArg F.F.map
  apply (SheafOfModules.unitHomEquiv N).injective
  apply PresheafOfModules.sections_ext
  intro V
  let one : (coefficient T (Rrings l T)).val.obj V :=
    (1 : ((Rrings l T).obj (op V.unop.1)).obj.obj (op V.unop.2))
  let n := V.unop.1
  let U := op V.unop.2
  let k := (toSheafify (Scheme.ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U
      (ULift.up 1)
  let y := ((integerGenerator T (Rrings l T) F).app (op n)).hom.app U k
  change a'.val.app V one = b'.val.app V one
  have hy : HEq y one := by
    change HEq y (1 : ((Rrings l T).obj (op n)).obj.obj U)
    dsimp only [y, k, integerGenerator]
    simpa only [Int.cast_one] using
      (integerGenerator_existsUnique T (Rrings l T) F).exists.choose_spec n U (ULift.up 1)
  have hh := congrArg (fun t ↦ (t.app (op n)).hom.app U k) h
  change ((F.F.map a').app (op n)).hom.app U y =
    ((F.F.map b').app (op n)).hom.app U y at hh
  exact eq_of_heq ((forgetMapSection T _ F a' n U one y hy).symm.trans
    ((heq_of_eq hh).trans (forgetMapSection T _ F b' n U one y hy)))

private theorem scalarIntegerSection (T : Scheme.{u})
    (F : Forget T (Rrings l T)) (n : ℕ) (U : T.ProEtᵒᵖ) (k : ULift.{u + 1} ℤ) :
    HEq (((F.F.map (scalarGenerator l E T)).app (op n)).hom.app U
      (((integerGenerator T (Rrings l T) F).app (op n)).hom.app U
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U k)))
      (k.down : ((Arings l E T).obj (op n)).obj.obj U) := by
  let x : (coefficient T (Rrings l T)).val.obj (op (n, U.unop)) :=
    (k.down : ((Rrings l T).obj (op n)).obj.obj U)
  have hx := (integerGenerator_existsUnique T (Rrings l T) F).exists.choose_spec n U k
  have hf := forgetMapSection T _ F (scalarGenerator l E T) n U x _ hx
  have hs := (scalarGenerator_existsUnique l E T).exists.choose_spec (op (n, U.unop)) x
  exact hf.trans (hs.trans (heq_of_eq (map_intCast
    ((coefficientSystemMap l E T).hom.app (op (n, U.unop))).hom k.down)))

private theorem coefficientAdjoint_int
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f) (θ : CoefficientPullback l E b f g)
    (n : ℕ) (U : Y.ProEtᵒᵖ) (k : ℤ) :
    HEq ((((g.ordinaryAdjunction.homEquiv _ _) θ.iso.hom).val.app (op (n, U.unop)))
      (show (coefficient Y (Arings l E Y)).val.obj (op (n, U.unop)) from
        (k : ((Arings l E Y).obj (op n)).obj.obj U)))
      (k : ((Arings l E X).obj (op n)).obj.obj (chart f U)) := by
  let x : ((SpTowerShriek.ev l E Y n).obj
      (coefficient Y (Arings l E Y))).val.obj U :=
    (k : ((Arings l E Y).obj (op n)).obj.obj U)
  have hn := θ.normalization n U (k : ((Arings l E Y).obj (op n)).obj.obj U) x HEq.rfl
  have he := pushEvaluationSections l E g n (coefficient X (Arings l E X)) U
    (((SpTowerShriek.ev l E Y n).map
      ((g.ordinaryAdjunction.homEquiv _ _) θ.iso.hom)).val.app U x)
  exact he.symm.trans (hn.trans (heq_of_eq (map_intCast
    ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} f CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n)))).hom.app U).hom k)))

private theorem constantIntegerDirect_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.ProEtᵒᵖ) (k : ULift.{u + 1} ℤ) :
    (Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom.app U
      ((toSheafify (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U k) =
    (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (chart f U) k := by
  have h := ((sheafificationAdjunction (Scheme.ProEt.topology Y)
    AddCommGrpCat.{u + 1}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      ((Scheme.proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
        ((constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))))).apply_symm_apply
    (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))))
  exact congrArg (fun t ↦ t.app U k) h

private theorem integerPull_adjoint {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕᵒᵖ) :
    (((abAdjunction f).homEquiv _ _) (integerPull f)).app n =
      Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  change ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _)
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm
      (Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) = _
  exact Equiv.apply_symm_apply _ _

/-- The canonical ordinary scalar map whose adjunct is `scalarGenerator`. -/
noncomputable def canonicalScalarUnit {T : Scheme.{u}} (c : Chern l E T) :
    c.scalar.model.E.obj (coefficient T (Rrings l T)) ⟶
      coefficient T (Arings l E T) :=
  (c.scalar.ordinaryAdjunction.homEquiv _ _).symm (scalarGenerator l E T)

/--
The sectionwise transpose identity in the normalized case, where the two scalar
maps are the canonical adjuncts of `scalarGenerator`.  This is the ordinary
coefficient-unit calculation: use adjunction naturality and the normalization
fields to identify the two maps on constant integer sections. Cancel the integer
generator using integral-forgetful full faithfulness: maps from the regular module
are determined by their values on one, by `SheafOfModules.unitHomEquiv`.
Empty charts and zero rings are included.

Source: blueprint classes proof (2), ordinary coefficient-unit normalization;
Stacks 03EL. (blueprint: lem-sp-tower-scalar-unit-abelian-transpose-section-normalized)
-/
theorem scalarUnit_abelianTranspose_section_normalized
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (d : IntegralCoefficientPullback l E f cY cX)
    (χ : (g.push ⋙ SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E Y)) ⋙ cY.reduction.forget.F ≅
      (SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E X) ⋙ cX.reduction.forget.F) ⋙ abPush f)
    (hχ : ∀ (N : Systems X (Arings l E X)) (n : ℕ) (U : Y.ProEtᵒᵖ)
      (x : (((cY.reduction.forget.F.obj
        ((SemilinearSections.res.{u + 1, u, u + 1}
          (coefficientSystemMap l E Y)).obj (g.push.obj N))).obj (op n)).obj.obj U)),
      HEq ((((χ.hom.app N).app (op n)).hom.app U) x) x)
    (θ₀ : CoefficientPullback l E b f g)
    (n : ℕᵒᵖ) (U : Y.ProEtᵒᵖ)
    (x : ((cY.reduction.forget.F.obj (coefficient Y (Rrings l Y))).obj n).obj.obj U) :
    (AddCommGrpCat.Hom.hom
      (((cY.reduction.forget.F.map
        (((cY.scalar.ordinaryAdjunction.comp g.ordinaryAdjunction).homEquiv _ _)
          (g.pull.map (canonicalScalarUnit l E cY) ≫ θ₀.iso.hom)) ≫
        χ.hom.app (coefficient X (Arings l E X))).app n).hom.app U)) x =
      (AddCommGrpCat.Hom.hom
        (((((abAdjunction f).homEquiv _ _)
          (d.forgetIso.hom.app (coefficient Y (Rrings l Y)) ≫
            cX.reduction.forget.F.map
              ((cX.scalar.ordinaryAdjunction.homEquiv _ _)
                (cX.scalar.model.E.map d.unitIso.hom ≫
              canonicalScalarUnit l E cX)))).app n).hom.app U)) x := by
  let FY := cY.reduction.forget
  let FX := cX.reduction.forget
  let RY := SemilinearSections.res.{u + 1, u, u + 1} (coefficientSystemMap l E Y)
  let N := coefficient X (Arings l E X)
  let t := (g.ordinaryAdjunction.homEquiv _ _) θ₀.iso.hom
  have hl : ((cY.scalar.ordinaryAdjunction.comp g.ordinaryAdjunction).homEquiv _ _)
      (g.pull.map (canonicalScalarUnit l E cY) ≫ θ₀.iso.hom) =
        scalarGenerator l E Y ≫ RY.map t := by
    rw [Adjunction.comp_homEquiv]
    change (cY.scalar.ordinaryAdjunction.homEquiv _ _)
      ((g.ordinaryAdjunction.homEquiv _ _)
        (g.pull.map (canonicalScalarUnit l E cY) ≫ θ₀.iso.hom)) = _
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [canonicalScalarUnit, Equiv.apply_symm_apply]
    rfl
  have hr : (cX.scalar.ordinaryAdjunction.homEquiv _ _)
      (cX.scalar.model.E.map d.unitIso.hom ≫ canonicalScalarUnit l E cX) =
        d.unitIso.hom ≫ scalarGenerator l E X := by
    rw [Adjunction.homEquiv_naturality_left]
    simp only [canonicalScalarUnit, Equiv.apply_symm_apply]
  rw [hl, hr]
  let a := FY.F.map (scalarGenerator l E Y ≫ RY.map t) ≫ χ.hom.app N
  let b' := ((abAdjunction f).homEquiv _ _)
    (d.forgetIso.hom.app (coefficient Y (Rrings l Y)) ≫
      FX.F.map (d.unitIso.hom ≫ scalarGenerator l E X))
  have hb : integerGenerator Y (Rrings l Y) FY ≫ b' =
      ((abAdjunction f).homEquiv _ _) (integerPull f) ≫
        (abPush f).map (integerGenerator X (Rrings l X) FX ≫
          FX.F.map (scalarGenerator l E X)) := by
    dsimp only [b']
    rw [Functor.map_comp, ← Adjunction.homEquiv_naturality_left]
    calc
      _ = ((abAdjunction f).homEquiv _ _)
          (((abPull f).map (integerGenerator Y (Rrings l Y) FY) ≫
            d.forgetIso.hom.app (coefficient Y (Rrings l Y)) ≫
              FX.F.map d.unitIso.hom) ≫ FX.F.map (scalarGenerator l E X)) := by
        simp only [Category.assoc]
      _ = ((abAdjunction f).homEquiv _ _)
          ((integerPull f ≫ integerGenerator X (Rrings l X) FX) ≫
            FX.F.map (scalarGenerator l E X)) := by rw [d.unit_normalization]
      _ = _ := by rw [Category.assoc, Adjunction.homEquiv_naturality_right]
  have hab : integerGenerator Y (Rrings l Y) FY ≫ a =
      integerGenerator Y (Rrings l Y) FY ≫ b' := by
    rw [hb]
    apply NatTrans.ext
    funext j
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (Scheme.ProEt.topology Y) _ _
      (((abPush f).obj (FX.F.obj
        ((SemilinearSections.res.{u + 1, u, u + 1}
          (coefficientSystemMap l E X)).obj N))).obj j).property
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro k
    let y := (((FY.F.map (scalarGenerator l E Y)).app j).hom.app V)
      ((((integerGenerator Y (Rrings l Y) FY).app j).hom.app V)
        ((toSheafify (Scheme.ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V k))
    let z := (((FY.F.map (RY.map t)).app j).hom.app V) y
    have hy := scalarIntegerSection l E Y FY j.unop V k
    have hz := forgetMapSection Y _ FY (RY.map t) j.unop V
      (show (RY.obj (coefficient Y (Arings l E Y))).val.obj
          (op (j.unop, V.unop)) from
        (k.down : ((Arings l E Y).obj j).obj.obj V)) y hy
    have ht := coefficientAdjoint_int l E g θ₀ j.unop V k.down
    have hleft := (hχ N j.unop V z).trans (hz.trans ht)
    have hright := scalarIntegerSection l E X FX j.unop (chart f V) k
    dsimp only [a]
    rw [Functor.map_comp]
    change (((χ.hom.app N).app j).hom.app V) z = _
    rw [NatTrans.comp_app, NatTrans.comp_app, integerPull_adjoint]
    change _ = (((FX.F.map (scalarGenerator l E X)).app j).hom.app (chart f V))
      ((((integerGenerator X (Rrings l X) FX).app j).hom.app (chart f V))
        ((Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom.app V
            ((toSheafify (Scheme.ProEt.topology Y)
              ((Functor.const Y.ProEtᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V k)))
    rw [constantIntegerDirect_section]
    exact eq_of_heq (hleft.trans hright.symm)
  have he : a = b' := by
    apply (cancel_mono (χ.inv.app N)).mp
    apply integerGenerator_cancel l Y FY
    simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ χ.inv.app N) hab
  exact congrArg (fun t ↦ (t.app n).hom.app U x) he

end AlgebraicGeometry.ProEtale.SpTowerClasses
