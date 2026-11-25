/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Coefficient.FiniteCoefficientScalarComparison
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Integral normalization of the finite additive coordinate

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-coefficient-unit-coordinate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] finiteScalarComparison integerComparison
attribute [local implicit_reducible] Functor.sheafPushforwardContinuous

private theorem unit_coordinate_sheafification_lift_app
    {C E : Type*} [Category* C] [Category* E]
    (J : GrothendieckTopology C) [HasWeakSheafify J E]
    {P : Cᵒᵖ ⥤ E} (F : Sheaf J E) (t : P ⟶ F.obj) (U : Cᵒᵖ) :
    (toSheafify J P).app U ≫
        (((sheafificationAdjunction J E).homEquiv P F).symm t).hom.app U = t.app U := by
  have h := Equiv.apply_symm_apply ((sheafificationAdjunction J E).homEquiv P F) t
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k ↦ k.app U) h

private theorem unit_coordinate_constant_comparison_mate
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J E] [HasWeakSheafify K E]
    (G : C ⥤ D) [G.IsContinuous J K]
    {L : Sheaf J E ⥤ Sheaf K E}
    (adj : L ⊣ G.sheafPushforwardContinuous E J K)
    {T : C} {S : D} (hT : IsTerminal T) (hS : IsTerminal S)
    (e : G.sheafPushforwardContinuous E J K ⋙ (sheafSections J E).obj (op T) ≅
      (sheafSections K E).obj (op S)) (a : E)
    (h : (toSheafify K ((Functor.const Dᵒᵖ).obj a)).app (op (G.obj T)) ≫
      e.hom.app ((constantSheaf K E).obj a) =
        (toSheafify K ((Functor.const Dᵒᵖ).obj a)).app (op S)) :
    adj.homEquiv _ _
        (((((constantSheafAdj J E hT).comp adj).ofNatIsoRight e).leftAdjointUniq
          (constantSheafAdj K E hS)).hom.app a) =
      ((sheafificationAdjunction J E).homEquiv _ _).symm
        (Functor.whiskerLeft G.op (toSheafify K ((Functor.const Dᵒᵖ).obj a))) := by
  -- Uniqueness of left adjoints determines the mate by its value on constant sections.
  apply ((constantSheafAdj J E hT).homEquiv _ _).injective
  apply (cancel_mono (e.hom.app ((constantSheaf K E).obj a))).mp
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafAdj J E hT).comp adj).ofNatIsoRight e)
    (constantSheafAdj K E hS) a
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hu
  refine hu.trans ?_
  rw [constantSheafAdj_homEquiv_apply]
  have hs : (constantSheafAdj K E hS).unit.app a =
      (toSheafify K ((Functor.const Dᵒᵖ).obj a)).app (op S) := by
    rw [← Adjunction.homEquiv_id, constantSheafAdj_homEquiv_apply]
    exact Category.comp_id _
  rw [hs]
  have hc := unit_coordinate_sheafification_lift_app J
    ((G.sheafPushforwardContinuous E J K).obj ((constantSheaf K E).obj a))
    (Functor.whiskerLeft G.op (toSheafify K ((Functor.const Dᵒᵖ).obj a))) (op T)
  exact h.symm.trans (congrArg (fun k ↦ k ≫ e.hom.app _) hc).symm

private theorem integerComparison_section (T : Scheme.{u}) (k : ULift.{u + 1} ℤ) :
    (integerComparison T).hom.hom.app ((Scheme.toProEt T).op.obj (op (Scheme.Etale.mk (𝟙 T))))
      (((comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
        ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).hom.app (op (Scheme.Etale.mk (𝟙 T)))
          ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op (Scheme.Etale.mk (𝟙 T))) k)) =
      (toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
          ((Scheme.toProEt T).op.obj (op (Scheme.Etale.mk (𝟙 T)))) k := by
  let Z := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let U := op (Scheme.Etale.mk (𝟙 T))
  let P := (Functor.const T.Etaleᵒᵖ).obj Z
  have hm : (comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _
      (integerComparison T).hom =
        ((sheafificationAdjunction T.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
          _ _).symm (Functor.whiskerLeft (Scheme.toProEt T).op
            (toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj Z))) := by
    unfold integerComparison
    apply unit_coordinate_constant_comparison_mate T.smallEtaleTopology (Scheme.ProEt.topology T)
      (Scheme.toProEt T) (comparisonAdjunction AddCommGrpCat.{u + 1} T)
      (Scheme.Etale.isTerminalMkId T) (Scheme.ProEt.isTerminalMkId T)
      ((Scheme.toProEt T).sheafPushforwardContinuousCompSheafSectionsObjIso
        AddCommGrpCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)
        (op (Scheme.Etale.mk (𝟙 T))))
    exact Category.comp_id _
  have h := congrArg (fun f ↦ (toSheafify T.smallEtaleTopology P).app U ≫ f.hom.app U) hm
  rw [Adjunction.homEquiv_unit] at h
  have hs := unit_coordinate_sheafification_lift_app T.smallEtaleTopology
    ((comparisonLowerStar AddCommGrpCat.{u + 1} T).obj
      ((constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj Z))
    (Functor.whiskerLeft (Scheme.toProEt T).op
      (toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj Z))) U
  have hh := h.trans hs
  have hh' := ConcreteCategory.congr_hom hh k
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, AddCommGrpCat.comp_apply,
    comparisonLowerStar, Functor.sheafPushforwardContinuous_map_hom_app,
    Functor.op_obj,
    Functor.whiskerLeft_app, Z, U, P] at hh'
  convert hh' using 1 <;> rfl

/-- The source coordinate carries the integral generator to the actual finite
quotient. This is an equality of degree-zero sheaf maps, with no cohomology class.
Source: diagonal-tower trace (1), constant-section normalization
(blueprint: lem-sfb-finite-coefficient-unit-coordinate).

Proof: move integerComparison to the other side of the equality and apply the
comparison adjunction. The mate equation for finiteScalarComparison identifies
its adjunction-unit sections with the actual associated-module-sheaf unit.
The two constant-sheaf adjunctions defining integerComparison identify the etale
integer generator with the same pro-etale integer generator, including its sign.
The map ordinaryFiniteIntegralGenerator sends the integer k to k times one.
Apply unit_sections to this scalar and the identity restriction: the result is
the pro-etale constant-ring section k times one. This is precisely the section
formula in finiteQuotient_existsUnique. Constant-sheaf adjunction and the
comparison adjunction are injective on Hom, so the maps coincide. This argument
also applies to the zero ring and the empty scheme. -/
theorem finiteScalarUnitCoordinate (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT) :
    finiteQuotient l E T n =
      (integerComparison T).inv ≫
        (comparisonUpperStar AddCommGrpCat.{u + 1} T).map
          (Etale.ordinaryFiniteIntegralGenerator (FiniteRing l E n) T) ≫
        (finiteScalarComparison l E n T).hom.app
          (Etale.ordinaryFiniteConstant (FiniteRing l E n) T) ≫
        (finiteForget l E T n).map (finiteOrdinaryUnitCoordinate l E n T c).hom := by
  apply (cancel_epi (integerComparison T).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply ((comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _).injective
  apply ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (Scheme.Etale.isTerminalMkId T)).homEquiv _ _).injective
  let U := op (Scheme.Etale.mk (𝟙 T))
  let W := (Scheme.toProEt T).op.obj U
  let Z := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let η := (comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
    ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj Z)
  let g := Etale.ordinaryFiniteIntegralGenerator (FiniteRing l E n) T
  ext k
  change (finiteQuotient l E T n).hom.app W
      ((integerComparison T).hom.hom.app W
        (η.hom.app U ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj Z)).app U k))) =
    c.unit.hom.val.app W
      (((finiteScalarComparison l E n T).hom.app _).hom.app W
        (((comparisonUpperStar AddCommGrpCat.{u + 1} T).map g).hom.app W
          (η.hom.app U ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj Z)).app U k))))
  have hn := (comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.naturality g
  have hn' := congrArg (fun f ↦ f.hom.app U
    ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj Z)).app U k)) hn
  have hn'' :
      (((comparisonUpperStar AddCommGrpCat.{u + 1} T).map g).hom.app W
        (η.hom.app U ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj Z)).app U k))) =
      (((comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
        ((Etale.moduleAbelianForget (FiniteRing l E n) T).obj
          (Etale.ordinaryFiniteConstant (FiniteRing l E n) T))).hom.app U
        (g.hom.app U ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj Z)).app U k))) := hn'.symm
  have hi := integerComparison_section T k
  change (integerComparison T).hom.hom.app W
      (η.hom.app U ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj Z)).app U k)) = _ at hi
  rw [hi, hn'']
  have hf := finiteScalarComparison_unit_section l E n T
    (Etale.ordinaryFiniteConstant (FiniteRing l E n) T) U
    (g.hom.app U ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj Z)).app U k))
  rw [hf]
  let p : Z ⟶ ((Etale.moduleAbelianForget (FiniteRing l E n) T).obj
      (Etale.ordinaryFiniteConstant (FiniteRing l E n) T)).obj.obj U :=
    AddCommGrpCat.ofHom
      ((((forget₂ (ModuleCat.{u + 1} (FiniteRing l E n)) AddCommGrpCat.{u + 1}).map
        ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of (FiniteRing l E n) (FiniteRing l E n)))).app U)).hom).comp
            ((Int.castAddHom (FiniteRing l E n)).comp AddEquiv.ulift.toAddMonoidHom))
  have hg : ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
      (Scheme.Etale.isTerminalMkId T)).homEquiv _ _) g = p := by
    exact Equiv.apply_symm_apply _ _
  have hg' := congrArg (fun f ↦ f k) hg
  change g.hom.app U ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj Z)).app U k) =
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
      (ModuleCat.of (FiniteRing l E n) (FiniteRing l E n)))).app U (k.down : FiniteRing l E n)
    at hg'
  rw [hg']
  have hc := c.unit_sections U W (𝟙 _) (k.down : FiniteRing l E n)
  have hm := ((comparisonUpperStar (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n)) T).obj
    (Etale.ordinaryFiniteConstant (SpTowerP1.levelRing l E n) T)).obj.map_id W
  simp only [op_id, op_unop, hm, map_intCast] at hc
  have hq := Classical.choose_spec (finiteQuotient_existsUnique l E T n).exists W k
  exact (eq_of_heq hq).trans hc.symm

end AlgebraicGeometry.ProEtale.DiagonalTrace
