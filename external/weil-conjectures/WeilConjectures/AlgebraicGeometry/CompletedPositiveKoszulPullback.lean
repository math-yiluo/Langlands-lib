/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import all WeilConjectures.AlgebraicGeometry.ConstantPullbackScalar
import WeilConjectures.AlgebraicGeometry.RingedComplexTensorPullback
import WeilConjectures.CategoryTheory.ConstantRingSectionRigidity
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex

/-! # The augmented positive Koszul diagram under completed inverse image

Source: Stacks Project, algebraization.tex, Tag 0A0E, finite Koszul calculation;
sites-cohomology.tex, Tag 07A4, tensor pullback.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe v u₁ u₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod MonoidalCategory

namespace CategoryTheory.ConstantCompletion

section ScalarTransport

variable {C D : Type v} [SmallCategory C] [SmallCategory D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)} [PreservesFiniteLimits L]
variable (F : InverseImageData L)

private theorem transportedSection_naturality {R S : Sheaf J CommRingCat.{v}}
    (φ : R ⟶ S) (a : (R.obj ⋙ forget CommRingCat).sections)
    (b : (S.obj ⋙ forget CommRingCat).sections)
    (hab : ∀ U, φ.hom.app U (a.val U) = b.val U) (U : Dᵒᵖ) :
    (F.rings.map φ).hom.app U ((inverseImageSection F R a).val U) =
      (inverseImageSection F S b).val U := by
  let T := Sheaf.terminal J Types.isTerminalPUnit
  let T' := Sheaf.terminal K Types.isTerminalPUnit
  let hT := (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).isTerminalObj L T
  let x := (hT.from T').hom.app U PUnit.unit
  have hs : sectionMap R a T ≫ (sheafCompose J (forget CommRingCat)).map φ =
      sectionMap S b T := by
    ext V y
    exact hab V
  have h := congrArg (fun f ↦ f.hom.app U ((L.map (sectionMap R a T)).hom.app U x))
    (F.ring_naturality φ)
  change (F.algebra S).ringUnderlying.hom.hom.app U
      ((L.map ((sheafCompose J (forget CommRingCat)).map φ)).hom.app U
        ((L.map (sectionMap R a T)).hom.app U x)) =
    (F.rings.map φ).hom.app U ((inverseImageSection F R a).val U) at h
  have hh : (L.map (sectionMap R a T ≫
      (sheafCompose J (forget CommRingCat)).map φ)).hom.app U x =
        (L.map (sectionMap S b T)).hom.app U x := congrArg (fun z ↦ (L.map z).hom.app U x) hs
  rw [L.map_comp] at hh
  change (L.map ((sheafCompose J (forget CommRingCat)).map φ)).hom.app U
      ((L.map (sectionMap R a T)).hom.app U x) = _ at hh
  rw [hh] at h
  exact h.symm

private noncomputable def transportedConstantHom (U : Dᵒᵖ) (A : CommRingCat.{v}) :
    A ⟶ (constant K A).obj.obj U := by
  let T := Sheaf.terminal J Types.isTerminalPUnit
  let T' := Sheaf.terminal K Types.isTerminalPUnit
  let hT := (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).isTerminalObj L T
  let x := (hT.from T').hom.app U PUnit.unit
  let t (a : A) : (F.rings.obj (constant J A)).obj.obj U :=
    (F.algebra (constant J A)).ringUnderlying.hom.hom.app U
    ((L.map (sectionMap (constant J A) (constantSection (J := J) a) T)).hom.app U x)
  refine CommRingCat.ofHom
    { toFun := fun a ↦ (constantMap F A).hom.app U (t a)
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }
  · have h := (F.algebra (constant J A)).ringOne T
      (sectionMap (constant J A) (constantSection (J := J) (1 : A)) T)
      (fun V _ ↦ map_one
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app V).hom) U x
    change t 1 = 1 at h
    rw [h, map_one]
  · intro a b
    have h := (F.algebra (constant J A)).ringMul T
      (sectionMap (constant J A) (constantSection (J := J) a) T)
      (sectionMap (constant J A) (constantSection (J := J) b) T)
      (sectionMap (constant J A) (constantSection (J := J) (a * b)) T)
      (fun V _ ↦ map_mul
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app V).hom a b) U x
    change t (a * b) = t a * t b at h
    rw [h, map_mul]
  · have h := (F.algebra (constant J A)).ringZero T
      (sectionMap (constant J A) (constantSection (J := J) (0 : A)) T)
      (fun V _ ↦ map_zero
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app V).hom) U x
    change t 0 = 0 at h
    rw [h, map_zero]
  · intro a b
    have h := (F.algebra (constant J A)).ringAdd T
      (sectionMap (constant J A) (constantSection (J := J) a) T)
      (sectionMap (constant J A) (constantSection (J := J) b) T)
      (sectionMap (constant J A) (constantSection (J := J) (a + b)) T)
      (fun V _ ↦ map_add
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app V).hom a b) U x
    change t (a + b) = t a + t b at h
    rw [h, map_add]

private theorem transportedConstantHom_naturality (U : Dᵒᵖ)
    {A B : CommRingCat.{v}} (f : A ⟶ B) :
    f ≫ transportedConstantHom F U B = transportedConstantHom F U A ≫
      ((constantSheaf K CommRingCat.{v}).map f).hom.app U := by
  apply CommRingCat.hom_ext
  ext a
  have hs (V : Cᵒᵖ) :
      ((constantSheaf J CommRingCat.{v}).map f).hom.app V
          ((constantSection (J := J) a).val V) =
        (constantSection (J := J) (f a)).val V := by
    exact (ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_naturality J ((Functor.const Cᵒᵖ).map f)) V) a).symm
  have hn := transportedSection_naturality F ((constantSheaf J CommRingCat.{v}).map f)
    (constantSection (J := J) a) (constantSection (J := J) (f a)) hs U
  have hc := congrArg (fun z ↦ z.hom.app U
    ((inverseImageSection F (constant J A) (constantSection (J := J) a)).val U))
      (F.constants.hom.naturality f)
  change (constantMap F B).hom.app U
      ((F.rings.map ((constantSheaf J CommRingCat.{v}).map f)).hom.app U
        ((inverseImageSection F (constant J A) (constantSection (J := J) a)).val U)) =
    ((constantSheaf K CommRingCat.{v}).map f).hom.app U
      ((constantMap F A).hom.app U
        ((inverseImageSection F (constant J A) (constantSection (J := J) a)).val U)) at hc
  change (constantMap F B).hom.app U
      ((inverseImageSection F (constant J B) (constantSection (J := J) (f a))).val U) = _
  exact (congrArg ((constantMap F B).hom.app U) hn).symm.trans hc

private theorem transportedConstant_eq (A : Type v) [CommRing A] (a : A) (U : Dᵒᵖ) :
    (transportedConstantSection F A a).val U = (constantSection (J := K) a).val U := by
  exact ConcreteCategory.congr_hom
    (constantRingSectionRigidity K U (transportedConstantHom F U)
      (transportedConstantHom_naturality F U) (CommRingCat.of A)) a

omit [PreservesFiniteLimits L] in
private theorem completedMap_coefficients (A : Type v) [CommRing A] (I : Ideal A) :
    F.rings.map (coefficientMap J A I) ≫ completedMap F A I =
      constantMap F A ≫ coefficientMap K A I := by
  apply limit.hom_ext
  intro n
  have hcoeff (T : GrothendieckTopology C) (k : ℕ) :
      coefficientMap T A I ≫ projection T A I k = quotient T A I k := by
    exact limit.lift_π _ _
  have hcoeff' (k : ℕ) :
      coefficientMap K A I ≫ projection K A I k = quotient K A I k := by
    exact limit.lift_π _ _
  have hmap (k : ℕ) : completedMap F A I ≫ projection K A I k =
      F.rings.map (projection J A I k) ≫ constantMap F (A ⧸ I ^ (k + 1)) := by
    exact limit.lift_π _ _
  change (F.rings.map (coefficientMap J A I) ≫ completedMap F A I) ≫
      projection K A I n.unop =
    (constantMap F A ≫ coefficientMap K A I) ≫ projection K A I n.unop
  rw [Category.assoc, hmap, ← Category.assoc, ← F.rings.map_comp, hcoeff,
    Category.assoc, hcoeff']
  exact F.constants.hom.naturality _

private theorem completedSection (A : Type v) [CommRing A] (I : Ideal A)
    (a : A) (U : Dᵒᵖ) :
    (completedMap F A I).hom.app U
        ((inverseImageSection F (completed J A I)
          (algebraSection (baseMap J A I true) a)).val U) =
      (algebraSection (baseMap K A I true) a).val U := by
  have h := transportedSection_naturality F (coefficientMap J A I)
    (constantSection (J := J) a) (algebraSection (coefficientMap J A I) a)
    (fun _ ↦ rfl) U
  have he := congrArg (fun z ↦ z.hom.app U
      ((inverseImageSection F (constant J A) (constantSection (J := J) a)).val U))
    (completedMap_coefficients F A I)
  change (completedMap F A I).hom.app U
      ((F.rings.map (coefficientMap J A I)).hom.app U
        ((inverseImageSection F (constant J A) (constantSection (J := J) a)).val U)) =
    (coefficientMap K A I).hom.app U ((transportedConstantSection F A a).val U) at he
  rw [h, transportedConstant_eq F A a U] at he
  exact he

private theorem pull_section_smul {R : Sheaf J CommRingCat.{v}}
    {S : Sheaf K CommRingCat.{v}} (c : F.rings.obj R ⟶ S)
    (a : (R.obj ⋙ forget CommRingCat).sections)
    (b : (S.obj ⋙ forget CommRingCat).sections)
    (hb : ∀ U, c.hom.app U ((inverseImageSection F R a).val U) = b.val U)
    (M : Mod R) :
    (pull F c).map ⟨PresheafOfModules.sectionsSMul M.val a⟩ =
      ⟨PresheafOfModules.sectionsSMul ((pull F c).obj M).val b⟩ := by
  let AI := F.algebra R
  let μ : M ⟶ M := ⟨PresheafOfModules.sectionsSMul M.val a⟩
  let aI := inverseImageSection F R a
  have hi : AI.modules.map μ =
      ⟨PresheafOfModules.sectionsSMul (AI.modules.obj M).val aI⟩ := by
    apply (underlying (F.rings.obj R)).map_injective
    apply (cancel_epi (AI.moduleUnderlying.inv.app M)).mp
    have hn := AI.moduleUnderlying.inv.naturality μ
    change L.map ((underlying R).map μ) ≫ AI.moduleUnderlying.inv.app M =
      AI.moduleUnderlying.inv.app M ≫
        (underlying (F.rings.obj R)).map (AI.modules.map μ) at hn
    rw [← hn]
    ext U x
    have hsm := AI.moduleSMul M ((underlying R).obj M)
      (sectionMap R a _) (𝟙 _) ((underlying R).map μ) (fun _ _ ↦ rfl) U x
    have hx : AI.ringUnderlying.hom.hom.app U
        ((L.map (sectionMap R a ((underlying R).obj M))).hom.app U x) = aI.val U :=
      congrArg (fun f ↦ f.hom.app U x) (inverseImageSection_map F R a ((underlying R).obj M))
    change (AI.moduleUnderlying.inv.app M).hom.app U
        ((L.map ((underlying R).map μ)).hom.app U x) =
      aI.val U • (show (AI.modules.obj M).val.obj U from
        (AI.moduleUnderlying.inv.app M).hom.app U x)
    simp only [Functor.map_id] at hsm
    change (AI.moduleUnderlying.inv.app M).hom.app U
        ((L.map ((underlying R).map μ)).hom.app U x) =
      (show (F.rings.obj R).obj.obj U from
        AI.ringUnderlying.hom.hom.app U
          ((L.map (sectionMap R a ((underlying R).obj M))).hom.app U x)) •
        (show (AI.modules.obj M).val.obj U from
          (AI.moduleUnderlying.inv.app M).hom.app U x) at hsm
    rw [hx] at hsm
    exact hsm
  change (change c).map (AI.modules.map μ) = _
  rw [hi]
  exact change_scalar c aI b hb (AI.modules.obj M)

private theorem scalar_eq_smul {R : Sheaf J CommRingCat.{v}}
    (a : (R.obj ⋙ forget CommRingCat).sections) :
    ringedKoszulScalar R a =
      (End.of ⟨PresheafOfModules.sectionsSMul (SheafOfModules.unit (siteModuleRings R)).val a⟩ :
        End (SheafOfModules.unit (siteModuleRings R))) := by
  apply End.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change R.obj.obj U at x
  let av : R.obj.obj U := a.val U
  change x * av = av * x
  exact mul_comm _ _

private theorem completedScalar_intertwines (A : Type v) [CommRing A] (I : Ideal A)
    (a : A)
    (e : (pull F (completedMap F A I)).obj
        (SheafOfModules.unit (siteModuleRings (completed J A I))) ≅
      SheafOfModules.unit (siteModuleRings (completed K A I))) :
    (pull F (completedMap F A I)).map
        (ringedKoszulScalar (completed J A I) (algebraSection (baseMap J A I true) a)).asHom ≫
        e.hom = e.hom ≫
      (ringedKoszulScalar (completed K A I) (algebraSection (baseMap K A I true) a)).asHom := by
  rw [scalar_eq_smul, scalar_eq_smul]
  rw [pull_section_smul F _ _ _ (completedSection F A I a)]
  ext U x
  exact (e.hom.val.app U).hom.map_smul _ _

end ScalarTransport

section DoubleComparison

variable {E : Type u₁} [Category.{w₁} E] [Preadditive E] [HasZeroObject E]
variable {E' : Type u₂} [Category.{w₂} E'] [Preadditive E'] [HasZeroObject E']
variable (P : E ⥤ E') [P.Additive] {X : E} {Y : E'}

omit [Preadditive E] [HasZeroObject E] [Preadditive E'] [HasZeroObject E'] [P.Additive] in
private theorem map_power_intertwines (f : End X) (g : End Y) (e : P.obj X ≅ Y)
    (h : P.map f.asHom ≫ e.hom = e.hom ≫ g.asHom) (n : ℕ) :
    P.map (f ^ n).asHom ≫ e.hom = e.hom ≫ (g ^ n).asHom := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, End.mul_asHom, P.map_comp, Category.assoc, ih]
    rw [← Category.assoc, h, Category.assoc]

private noncomputable def doubleComparisonX (f : End X) (g : End Y)
    (e : P.obj X ≅ Y) (n : ℤ) :
    P.obj ((HomologicalComplex.double f.asHom (by decide : (ComplexShape.up ℤ).Rel 0 1)).X n) ≅
      (HomologicalComplex.double g.asHom (by decide : (ComplexShape.up ℤ).Rel 0 1)).X n := by
  classical
  by_cases h : n = 0
  · subst n
    exact P.mapIso (HomologicalComplex.doubleXIso₀ f.asHom _) ≪≫ e ≪≫
      (HomologicalComplex.doubleXIso₀ g.asHom _).symm
  · by_cases h' : n = 1
    · subst n
      exact P.mapIso (HomologicalComplex.doubleXIso₁ f.asHom _ (by decide)) ≪≫ e ≪≫
        (HomologicalComplex.doubleXIso₁ g.asHom _ (by decide)).symm
    · exact (P.map_isZero (HomologicalComplex.isZero_double_X f.asHom _ n h h')).iso
        (HomologicalComplex.isZero_double_X g.asHom _ n h h')

private noncomputable def doubleComparison (f : End X) (g : End Y)
    (e : P.obj X ≅ Y) (h : P.map f.asHom ≫ e.hom = e.hom ≫ g.asHom) :
    (P.mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.double f.asHom (by decide : (ComplexShape.up ℤ).Rel 0 1)) ≅
      HomologicalComplex.double g.asHom (by decide : (ComplexShape.up ℤ).Rel 0 1) :=
  HomologicalComplex.Hom.isoOfComponents (doubleComparisonX P f g e) (by
    intro n k hnk
    have hk : n + 1 = k := hnk
    subst k
    by_cases hn : n = 0
    · subst n
      simp only [Int.reduceAdd, doubleComparisonX, ↓reduceDIte, Iso.trans_hom,
        Functor.mapIso_hom, Iso.symm_hom, ne_eq, zero_ne_one, not_false_eq_true,
        HomologicalComplex.double_d, Category.assoc, Iso.inv_hom_id_assoc,
        Functor.mapHomologicalComplex_obj_d, P.map_comp, zero_add, one_ne_zero,
        Iso.inv_hom_id_map_assoc]
      rw [reassoc_of% h]
    · change _ ≫ _ = P.map _ ≫ _
      rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ hn,
        HomologicalComplex.double_d_eq_zero₀ _ _ _ _ hn, P.map_zero, comp_zero, zero_comp])

end DoubleComparison

section FactorComparison

variable {C D : Type v} [SmallCategory C] [SmallCategory D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {R : Sheaf J CommRingCat.{v}} {S : Sheaf K CommRingCat.{v}}
variable (P : Mod R ⥤ Mod S) [P.Additive]
variable (s : (R.obj ⋙ forget CommRingCat).sections)
variable (t : (S.obj ⋙ forget CommRingCat).sections)

private noncomputable def factorIso
    (e : P.obj (SheafOfModules.unit (siteModuleRings R)) ≅
      SheafOfModules.unit (siteModuleRings S))
    (h : P.map (ringedKoszulScalar R s).asHom ≫ e.hom =
      e.hom ≫ (ringedKoszulScalar S t).asHom) (m : ℕ) :
    (P.mapHomologicalComplex (.up ℤ)).obj (ringedKoszulFactor R s m) ≅
      ringedKoszulFactor S t m :=
  doubleComparison P _ _ e (map_power_intertwines P _ _ e h (m + 1))

private theorem factorIso_step
    (e : P.obj (SheafOfModules.unit (siteModuleRings R)) ≅
      SheafOfModules.unit (siteModuleRings S))
    (h : P.map (ringedKoszulScalar R s).asHom ≫ e.hom =
      e.hom ≫ (ringedKoszulScalar S t).asHom) (m : ℕ) :
    (P.mapHomologicalComplex (.up ℤ)).map (ringedKoszulFactorStep R s m) ≫
        (factorIso P s t e h (m + 1)).hom =
      (factorIso P s t e h m).hom ≫ ringedKoszulFactorStep S t m := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp [factorIso, doubleComparison, doubleComparisonX,
      ringedKoszulFactorStep, ringedKoszulFactorStepF, Category.assoc, P.map_comp]
  · by_cases hn' : n = 1
    · subst n
      simp only [ringedKoszulFactorStep, factorIso, doubleComparison,
        HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        ringedKoszulFactorStepF, one_ne_zero, ↓reduceDIte, eqToHom_refl,
        Category.comp_id, Category.id_comp, P.map_comp,
        HomologicalComplex.Hom.isoOfComponents_hom_f, doubleComparisonX,
        Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id_map_assoc, Iso.inv_hom_id_assoc]
      rw [reassoc_of% h]
    · exact (HomologicalComplex.isZero_double_X _ _ n hn hn').eq_of_tgt _ _

private noncomputable def factorsIso
    (e : P.obj (SheafOfModules.unit (siteModuleRings R)) ≅
      SheafOfModules.unit (siteModuleRings S))
    (h : P.map (ringedKoszulScalar R s).asHom ≫ e.hom =
      e.hom ≫ (ringedKoszulScalar S t).asHom) :
    ringedKoszulFactors R s ⋙ P.mapHomologicalComplex (.up ℤ) ≅
      ringedKoszulFactors S t := by
  refine NatIso.ofComponents (factorIso P s t e h) ?_
  intro m n f
  exact (NatTrans.ofSequence
    (F := ringedKoszulFactors R s ⋙ P.mapHomologicalComplex (.up ℤ))
    (G := ringedKoszulFactors S t) (fun m ↦ (factorIso P s t e h m).hom) (fun m ↦ by
    simpa only [Functor.comp_map, ringedKoszulFactors,
      Functor.ofSequence_map_homOfLE_succ] using factorIso_step P s t e h m)).naturality f

private noncomputable def rankOneIso
    (u : (P.mapHomologicalComplex (.up ℤ)).obj (ringedSiteRingComplex R) ≅
      ringedSiteRingComplex S) :
    P.obj (SheafOfModules.unit (siteModuleRings R)) ≅
      SheafOfModules.unit (siteModuleRings S) :=
  (P.mapIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _)).symm ≪≫
    HomologicalComplex.Hom.isoApp u 0 ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) 0 _

private theorem factorIso_projection
    (u : (P.mapHomologicalComplex (.up ℤ)).obj (ringedSiteRingComplex R) ≅
      ringedSiteRingComplex S)
    (h : P.map (ringedKoszulScalar R s).asHom ≫ (rankOneIso P u).hom =
      (rankOneIso P u).hom ≫ (ringedKoszulScalar S t).asHom) (m : ℕ) :
    (P.mapHomologicalComplex (.up ℤ)).map (ringedKoszulFactorProjection R s m) ≫
        u.hom =
      (factorIso P s t (rankOneIso P u) h m).hom ≫
        ringedKoszulFactorProjection S t m := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp [factorIso, doubleComparison, doubleComparisonX, rankOneIso,
      ringedKoszulFactorProjection, ringedKoszulFactorProjectionF,
      P.map_comp, Category.assoc]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn).eq_of_tgt _ _

end FactorComparison

section TensorDiagrams

variable {E : Type u₁} [Category.{w₁} E]
variable {E' : Type u₂} [Category.{w₂} E']
variable {P : E ⥤ E'} {T : E ⥤ E ⥤ E} {T' : E' ⥤ E' ⥤ E'}
variable {R : E} {S : E'} {ρ : ∀ N : E, (T.obj N).obj R ≅ N}
variable {ρ' : ∀ N : E', (T'.obj N).obj S ≅ N}

private def tensorNatIso
    (H : TensorPullbackComparison.{u₁, w₁, u₂, w₂} P T T' R S ρ ρ') :
    Functor.uncurry.obj T ⋙ P ≅ P.prod P ⋙ Functor.uncurry.obj T' :=
  NatIso.ofComponents (fun x ↦ H.t x.1 x.2) (by
    intro x y f
    change P.map ((T.map f.1).app x.2 ≫ (T.obj y.1).map f.2) ≫ _ = _
    rw [P.map_comp, Category.assoc, H.rightNaturality,
      ← Category.assoc, H.leftNaturality, Category.assoc]
    rfl)

private theorem tensor_naturality
    (H : TensorPullbackComparison.{u₁, w₁, u₂, w₂} P T T' R S ρ ρ') {X X' Y Y' : E}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    P.map ((Functor.uncurry.obj T).map (f ×ₘ g)) ≫ (H.t X' Y').hom =
      (H.t X Y).hom ≫ (Functor.uncurry.obj T').map (P.map f ×ₘ P.map g) :=
  (tensorNatIso H).hom.naturality (f ×ₘ g)

private def tensorDiagramIso
    (H : TensorPullbackComparison.{u₁, w₁, u₂, w₂} P T T' R S ρ ρ') {X Y : ℕ ⥤ E} {X' Y' : ℕ ⥤ E'}
    (e : X ⋙ P ≅ X') (d : Y ⋙ P ≅ Y') :
    (X.prod' Y ⋙ Functor.uncurry.obj T) ⋙ P ≅
      X'.prod' Y' ⋙ Functor.uncurry.obj T' :=
  NatIso.ofComponents (fun m ↦ H.t (X.obj m) (Y.obj m) ≪≫
    (Functor.uncurry.obj T').mapIso (Iso.prod (e.app m) (d.app m))) (by
    intro m n f
    change P.map ((Functor.uncurry.obj T).map (X.map f ×ₘ Y.map f)) ≫
        ((H.t _ _).hom ≫ (Functor.uncurry.obj T').map
          (e.hom.app n ×ₘ d.hom.app n)) =
      ((H.t _ _).hom ≫ (Functor.uncurry.obj T').map
        (e.hom.app m ×ₘ d.hom.app m)) ≫
          (Functor.uncurry.obj T').map (X'.map f ×ₘ Y'.map f)
    rw [← Category.assoc, tensor_naturality H, Category.assoc,
      ← Functor.map_comp, Category.assoc, ← Functor.map_comp]
    congr 2
    apply Prod.ext
    · exact e.hom.naturality f
    · exact d.hom.naturality f)

private theorem tensor_augmented
    (H : TensorPullbackComparison.{u₁, w₁, u₂, w₂} P T T' R S ρ ρ') {X Y : E} {X' Y' : E'}
    (f : X ⟶ R) (g : Y ⟶ R) (f' : X' ⟶ S) (g' : Y' ⟶ S)
    (e : P.obj X ≅ X') (d : P.obj Y ≅ Y') (u : P.obj R ≅ S)
    (hf : P.map f ≫ u.hom = e.hom ≫ f')
    (hg : P.map g ≫ H.j.hom = d.hom ≫ g')
    (hρ : ∀ {M N : E'} (a : M ⟶ N),
      (T'.map a).app S ≫ (ρ' N).hom = (ρ' M).hom ≫ a) :
    P.map ((Functor.uncurry.obj T).map (f ×ₘ g) ≫ (ρ R).hom) ≫ u.hom =
      ((H.t X Y).hom ≫ (Functor.uncurry.obj T').map (e.hom ×ₘ d.hom)) ≫
        (Functor.uncurry.obj T').map (f' ×ₘ g') ≫ (ρ' S).hom := by
  have hu : (H.t R R).hom ≫ (T'.obj (P.obj R)).map H.j.hom ≫
      (ρ' (P.obj R)).hom = P.map (ρ R).hom := by
    have h := H.unit R
    apply (cancel_epi (P.map (ρ R).inv)).1
    simpa only [Category.assoc, ← P.map_comp, Iso.inv_hom_id, P.map_id,
      Category.id_comp, Iso.inv_hom_id_assoc] using
      congrArg (fun z ↦ z ≫ (ρ' (P.obj R)).hom) h
  rw [P.map_comp, Category.assoc, ← hu]
  rw [← Category.assoc, ← Category.assoc,
    tensor_naturality H, Category.assoc, Category.assoc]
  simp only [Category.assoc]
  rw [← hρ u.hom]
  change (H.t X Y).hom ≫
      (Functor.uncurry.obj T').map (P.map f ×ₘ P.map g) ≫
        (T'.obj (P.obj R)).map H.j.hom ≫ (T'.map u.hom).app S ≫ (ρ' S).hom = _
  rw [NatTrans.naturality_assoc]
  rw [← Category.assoc ((T'.map u.hom).app (P.obj R))]
  change (H.t X Y).hom ≫
      (Functor.uncurry.obj T').map (P.map f ×ₘ P.map g) ≫
        (Functor.uncurry.obj T').map (u.hom ×ₘ H.j.hom) ≫ (ρ' S).hom = _
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  have hp : (P.map f ×ₘ P.map g) ≫ (u.hom ×ₘ H.j.hom) =
      (e.hom ×ₘ d.hom) ≫ (f' ×ₘ g') := by
    apply Prod.ext
    · exact hf
    · exact hg
  rw [hp]

end TensorDiagrams

section KoszulInduction

variable {C D : Type v} [SmallCategory C] [SmallCategory D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

private theorem koszulUnit_right (R : Sheaf J CommRingCat.{v}) :
    (ringedKoszulUnitTensorIso R).hom =
      (ringedKoszulRightUnitIso R (ringedSiteRingComplex R)).hom := by
  let := SheafOfModules.isGrothendieckAbelian (siteModuleRings R)
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := Classical.choice (SheafOfModules.tensorClosed R).2.1
  let : HasColimitsOfSize.{0, 0} (Mod R) := hasColimitsOfSizeShrink.{0, 0, v, v} _
  change (MonoidalCategory.leftUnitor (𝟙_ (Cx R))).hom =
    (MonoidalCategory.rightUnitor (𝟙_ (Cx R))).hom
  exact MonoidalCategory.unitors_equal

private theorem koszulRight_natural (S : Sheaf K CommRingCat.{v})
    {M N : Cx S} (f : M ⟶ N) :
    ((ringedKoszulTensor S).map f).app (ringedSiteRingComplex S) ≫
        (ringedKoszulRightUnitIso S N).hom =
      (ringedKoszulRightUnitIso S M).hom ≫ f := by
  let := SheafOfModules.isGrothendieckAbelian (siteModuleRings S)
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.symmetricCategory S
  let := Classical.choice (SheafOfModules.tensorClosed S).1
  let := Classical.choice (SheafOfModules.tensorClosed S).2.1
  let : HasColimitsOfSize.{0, 0} (Mod S) := hasColimitsOfSizeShrink.{0, 0, v, v} _
  exact MonoidalCategory.rightUnitor_naturality f

end KoszulInduction

/-- Completed inverse image preserves the positive ordered Koszul diagram and
its projections. This assertion contains no duals or internal Hom complexes.

Source: Stacks Project, algebraization.tex, Tag 0A0E, positive finite free tensors;
sites-cohomology.tex, Tag 07A4, tensor pullback.
(auxiliary; not a blueprint node).

Proof in words: the comparison of constant rings, composed with transport of
sections, is natural in every commutative ring. Constant-ring section rigidity,
proved using the universal element of Z[X] and evaluation maps, shows that this
transport fixes constant elements. The limit projection equations for
completedMap identify their completed images. Algebraic inverse image and
extension of scalars transport scalar multiplication accordingly. Every module
isomorphism of the pulled-back rank-one module with the target rank-one module
therefore intertwines multiplication by each a_i and all its positive powers.

For an arbitrary supplied u, use its degree-zero component to compare each
rank-one term of the first two-term factor, and the unique zero-object
comparisons in the remaining degrees. The scalar identity gives the chain-map
equation and compatibility with the forward maps (1,a_i). The degree-zero
projection commutes with u; the other components of its target vanish.

Induct on the number of factors, retaining arbitrary u in the induction
hypothesis. The empty diagram is constant with comparison u. In the successor
case compare the first factor using u, compare the tail using the canonical
ring-complex comparison from ordinary tensor pullback, and tensor these
comparisons. Tensor naturality gives compatibility with transitions. Its right
unit compatibility, naturality of the target right unitor, and equality of the
two unitors on the unit object give the projection equation. Thus no separate
classification or extension of automorphisms of the ring complex is required.
Empty lists, repeated or zero scalars, and zero rings use the same formulas. -/
theorem completedPositiveKoszulPullback
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}
    (F : InverseImageData L) (V : Sheaf K (Type v) ⥤ Sheaf J (Type v))
    (adj : L ⊣ V) [PreservesFiniteLimits L]
    (A : Type v) [CommRing A] (I : Ideal A) [IsIso (completedMap F A I)]
    (r : ℕ) (a : Fin r → A)
    (u : ((pull F (completedMap F A I)).mapHomologicalComplex (.up ℤ)).obj
      (ringedSiteRingComplex (completed J A I)) ≅
        ringedSiteRingComplex (completed K A I)) :
    let P := (pull F (completedMap F A I)).mapHomologicalComplex (.up ℤ)
    ∃ e : ringedKoszulDiagram (completed J A I) r
          (fun i ↦ algebraSection (baseMap J A I true) (a i)) ⋙ P ≅
        ringedKoszulDiagram (completed K A I) r
          (fun i ↦ algebraSection (baseMap K A I true) (a i)),
      ∀ m : ℕ,
        P.map (ringedKoszulProjection (completed J A I) r
            (fun i ↦ algebraSection (baseMap J A I true) (a i)) m) ≫ u.hom =
          e.hom.app m ≫ ringedKoszulProjection (completed K A I) r
            (fun i ↦ algebraSection (baseMap K A I true) (a i)) m := by
  let P := (pull F (completedMap F A I)).mapHomologicalComplex (.up ℤ)
  obtain ⟨H⟩ := ringedComplexTensorPullback F V adj (completedMap F A I)
  change ∃ e : ringedKoszulDiagram (completed J A I) r
      (fun i ↦ algebraSection (baseMap J A I true) (a i)) ⋙ P ≅
      ringedKoszulDiagram (completed K A I) r
        (fun i ↦ algebraSection (baseMap K A I true) (a i)), _
  induction r generalizing u with
  | zero =>
    let e : ringedKoszulDiagram (completed J A I) 0
          (fun i ↦ algebraSection (baseMap J A I true) (a i)) ⋙ P ≅
        ringedKoszulDiagram (completed K A I) 0
          (fun i ↦ algebraSection (baseMap K A I true) (a i)) :=
      NatIso.ofComponents (fun _ ↦ u) (by
        intro m n f
        simp [ringedKoszulDiagram])
    refine ⟨e, ?_⟩
    intro m
    simp [ringedKoszulProjection, e]
  | succ r ih =>
    obtain ⟨d, hd⟩ := ih (fun i ↦ a i.succ) H.j
    let P₀ := pull F (completedMap F A I)
    let s := algebraSection (baseMap J A I true) (a 0)
    let t := algebraSection (baseMap K A I true) (a 0)
    have h : P₀.map (ringedKoszulScalar (completed J A I) s).asHom ≫
          (rankOneIso P₀ u).hom =
        (rankOneIso P₀ u).hom ≫ (ringedKoszulScalar (completed K A I) t).asHom :=
      completedScalar_intertwines F A I (a 0) (rankOneIso P₀ u)
    let e := factorsIso P₀ s t (rankOneIso P₀ u) h
    refine ⟨tensorDiagramIso H e d, ?_⟩
    intro m
    have hp := tensor_augmented H
      (ringedKoszulFactorProjection (completed J A I) s m)
      (ringedKoszulProjection (completed J A I) r
        (fun i ↦ algebraSection (baseMap J A I true) (a i.succ)) m)
      (ringedKoszulFactorProjection (completed K A I) t m)
      (ringedKoszulProjection (completed K A I) r
        (fun i ↦ algebraSection (baseMap K A I true) (a i.succ)) m)
      (e.app m) (d.app m) u (factorIso_projection P₀ s t u h m) (hd m)
      (koszulRight_natural (completed K A I))
    dsimp only [s, t] at hp
    simpa only [ringedKoszulProjection, ← koszulUnit_right, tensorDiagramIso,
      NatIso.ofComponents_hom_app, Iso.trans_hom, Functor.mapIso_hom,
      Functor.uncurry_obj_map, Iso.app_hom, Iso.prod, Functor.prod'_obj,
      Functor.comp_obj, ringedKoszulDiagram, ringedKoszulFactors,
      Functor.ofSequence, s, t, Category.assoc] using hp

end CategoryTheory.ConstantCompletion
