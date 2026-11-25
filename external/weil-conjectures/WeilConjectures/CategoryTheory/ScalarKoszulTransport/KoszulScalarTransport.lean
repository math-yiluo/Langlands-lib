/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Strict.StrictScalarKoszulInstances
import all WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement

/-! # KoszulScalarTransport for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-f5-koszul-scalar-transport).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}

open MonoidalCategory
open scoped CategoryTheory.Prod

attribute [local irreducible] homComplexFunctor
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  Localization.Monoidal.tensorBifunctor

attribute [local instance] gradedTensorCache gradedGoodTensorLeftCache
  gradedGoodTensorRightCache gradedFourCache tensorPreservesEmptyLeftCache
  tensorPreservesEmptyRightCache cachedModuleMonoidal cachedModuleSymmetric
  cachedModulePreadditive cachedModuleClosed cachedComplexMonoidal
  cachedComplexBraided cachedComplexClosed

namespace ScalarKoszulTransport

universe v u₁ w₁ u₂ w₂ u' w w'

abbrev siteModuleRings {C : Type v} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{v}) :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj O

structure TensorPullbackComparison
    {E : Type u} [Category.{w} E] {E' : Type u'} [Category.{w'} E']
    (P : E ⥤ E') (T : E ⥤ E ⥤ E) (T' : E' ⥤ E' ⥤ E')
    (R : E) (S : E') (ρ : ∀ N : E, (T.obj N).obj R ≅ N)
    (ρ' : ∀ N : E', (T'.obj N).obj S ≅ N) where
  j : P.obj R ≅ S
  t : ∀ N M : E, P.obj ((T.obj N).obj M) ≅ (T'.obj (P.obj N)).obj (P.obj M)
  rightNaturality : ∀ (N M M' : E) (g : M ⟶ M'),
    P.map ((T.obj N).map g) ≫ (t N M').hom =
      (t N M).hom ≫ (T'.obj (P.obj N)).map (P.map g)
  leftNaturality : ∀ (N N' M : E) (f : N ⟶ N'),
    P.map ((T.map f).app M) ≫ (t N' M).hom =
      (t N M).hom ≫ (T'.map (P.map f)).app (P.obj M)
  unit : ∀ N : E, P.map (ρ N).inv ≫ (t N R).hom ≫
    (T'.obj (P.obj N)).map j.hom = (ρ' (P.obj N)).inv

/-- Cancel two comparison isomorphisms from the inverse composite identity.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-transport). -/
theorem normalizedComposite
    {E : Type u} [Category.{w} E] {X U V W : E}
    (a : X ⟶ U) (b : U ≅ V) (c : V ≅ W) (d : X ⟶ W)
    (h : d ≫ c.inv ≫ b.inv = a) : a ≫ b.hom ≫ c.hom = d := by
  rw [← h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- Transport of ordered two-term tensor diagrams.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-transport). -/
theorem tensorUnitInverse
    {E : Type u} [Category.{w} E] [MonoidalCategory E]
    {E' : Type u'} [Category.{w'} E'] [MonoidalCategory E']
    (P : E ⥤ E') (μ : ∀ X Y : E, P.obj (X ⊗ Y) ≅ P.obj X ⊗ P.obj Y)
    (j₀ : P.obj (𝟙_ E) ≅ 𝟙_ E')
    (h : ∀ M : E, (μ M (𝟙_ E)).hom ≫ (𝟙 (P.obj M) ⊗ₘ j₀.hom) ≫
      (MonoidalCategory.rightUnitor (P.obj M)).hom =
        P.map (MonoidalCategory.rightUnitor M).hom) (M : E) :
    (MonoidalCategory.rightUnitor (P.obj M)).inv ≫
        (P.obj M ◁ j₀.inv) ≫ (μ M (𝟙_ E)).inv =
      P.map (MonoidalCategory.rightUnitor M).inv := by
  let q := μ M (𝟙_ E) ≪≫ (MonoidalCategory.tensorLeft (P.obj M)).mapIso j₀ ≪≫
    MonoidalCategory.rightUnitor (P.obj M)
  have hq : q = P.mapIso (MonoidalCategory.rightUnitor M) := by
    apply Iso.ext
    simpa only [q, Iso.trans_hom, Functor.mapIso_hom, MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorLeft, MonoidalCategory.curriedTensor_obj_map] using h M
  simpa only [q, Iso.trans_inv, Functor.mapIso_inv, MonoidalCategory.tensorLeft,
    MonoidalCategory.curriedTensor_obj_map, Category.assoc] using congrArg Iso.inv hq

/-- Transport of ordered two-term tensor diagrams.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-transport). -/
theorem inverseNaturality
    {E : Type u} [Category.{w} E] {A B C D : E}
    (i : A ≅ B) (j : C ≅ D) (f : A ⟶ C) (g : B ⟶ D)
    (h : f ≫ j.hom = i.hom ≫ g) : g ≫ j.inv = i.inv ≫ f := by
  apply (cancel_mono j.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

-- Prove the component calculation abstractly, before specializing to module sheaves.
private theorem tensorTotalRightUnit
    {E : Type u} [Category.{w} E] [Abelian E] [MonoidalCategory E]
    {E' : Type u'} [Category.{w'} E'] [Abelian E'] [MonoidalCategory E']
    [MonoidalPreadditive E] [MonoidalPreadditive E']
    [MonoidalClosed E] [MonoidalClosed E']
    [HasCoproducts.{0} E] [HasCoproducts.{0} E']
    (P : E ⥤ E') [P.Additive]
    (μ : ∀ X Y : E, P.obj (X ⊗ Y) ≅ P.obj X ⊗ P.obj Y)
    (hμ : ∀ {X X' Y Y' : E} (f : X ⟶ X') (g : Y ⟶ Y'),
      P.map (f ⊗ₘ g) ≫ (μ X' Y').hom = (μ X Y).hom ≫ (P.map f ⊗ₘ P.map g))
    (j₀ : P.obj (𝟙_ E) ≅ 𝟙_ E')
    (hunit : ∀ M : E, (MonoidalCategory.rightUnitor (P.obj M)).inv ≫
      (P.obj M ◁ j₀.inv) ≫ (μ M (𝟙_ E)).inv =
        P.map (MonoidalCategory.rightUnitor M).inv)
    (N : CochainComplex E ℤ) :
    let Pc := P.mapHomologicalComplex (.up ℤ)
    let RX := (HomologicalComplex.single E (.up ℤ) 0).obj (𝟙_ E)
    let j := (HomologicalComplex.singleMapHomologicalComplex P (.up ℤ) 0).app (𝟙_ E) ≪≫
      (HomologicalComplex.single E' (.up ℤ) 0).mapIso j₀
    (HomologicalComplex.rightUnitor (Pc.obj N)).inv ≫
        HomologicalComplex.mapBifunctorMap (𝟙 (Pc.obj N)) j.inv
          (MonoidalCategory.curriedTensor E') (.up ℤ) ≫
        tensorPullbackTotal P μ hμ N RX =
      Pc.map (HomologicalComplex.rightUnitor N).inv := by
  let Pc := P.mapHomologicalComplex (.up ℤ)
  let RX := (HomologicalComplex.single E (.up ℤ) 0).obj (𝟙_ E)
  let j := (HomologicalComplex.singleMapHomologicalComplex P (.up ℤ) 0).app (𝟙_ E) ≪≫
    (HomologicalComplex.single E' (.up ℤ) 0).mapIso j₀
  apply HomologicalComplex.hom_ext
  intro n
  have hj : j.inv.f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ E')).hom ≫ j₀.inv ≫
      P.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ E)).inv := by
    simp only [j, Iso.trans_inv, HomologicalComplex.comp_f,
      Functor.mapIso_inv, Iso.app_inv, HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Category.assoc,
      Iso.inv_hom_id_assoc]
  have hn := hμ (𝟙 (N.X n))
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (𝟙_ E)).inv
  have hn' :
      (P.obj (N.X n) ◁ P.map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (𝟙_ E)).inv) ≫
          (μ (N.X n) (RX.X 0)).inv =
        (μ (N.X n) (𝟙_ E)).inv ≫
          P.map (N.X n ◁
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0
              (𝟙_ E)).inv) := by
    apply (cancel_mono (μ (N.X n) (RX.X 0)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [MonoidalCategory.tensorHom_def, MonoidalCategory.id_whiskerRight,
      P.map_id, Category.id_comp, Iso.inv_hom_id_assoc] using
      congrArg (fun z ↦
        (μ (N.X n) (𝟙_ E)).inv ≫ z) hn.symm
  simp only [HomologicalComplex.comp_f]
  change (HomologicalComplex.rightUnitor' (Pc.obj N)).inv n ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 (Pc.obj N)) j.inv
      (MonoidalCategory.curriedTensor E') (.up ℤ)).f n ≫
        (tensorPullbackTotal P μ hμ N RX).f n =
      P.map ((HomologicalComplex.rightUnitor N).inv.f n)
  erw [HomologicalComplex.rightUnitor'_inv]
  erw [Category.assoc, Category.assoc, HomologicalComplex.ι_mapBifunctorMap_assoc]
  erw [HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app, Category.id_comp]
  erw [tensorPullbackTotal]
  change _ ≫ _ ≫ _ ≫ _ ≫ tensorPullbackTotalComponent P μ N RX n = _
  erw [tensorPullbackTotalComponent, HomologicalComplex.ι_mapBifunctorDesc]
  erw [hj, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  change (MonoidalCategory.rightUnitor (P.obj (N.X n))).inv ≫
      (P.obj (N.X n) ◁ _) ≫ (P.obj (N.X n) ◁ _) ≫
      (P.obj (N.X n) ◁ j₀.inv) ≫ (P.obj (N.X n) ◁ _) ≫
      (μ (N.X n) (RX.X 0)).inv ≫ _ =
    P.map ((HomologicalComplex.rightUnitor N).inv.f n)
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id]
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [← Category.assoc _ (μ (N.X n) (RX.X 0)).inv,
    hn', Category.assoc]
  have hu := hunit (N.X n)
  simp only [← Category.assoc] at hu ⊢
  rw [hu, ← P.map_comp, ← P.map_comp]
  congr 1
  simp only [Category.assoc]
  exact (HomologicalComplex.rightUnitor'_inv N n).symm

-- Keep total-complex constructions abstract until their one sheaf specialization.
private def tensorComparisonFamily
    {E : Type u} [Category.{w} E] [Abelian E] [MonoidalCategory E]
    {E' : Type u'} [Category.{w'} E'] [Abelian E'] [MonoidalCategory E']
    [MonoidalPreadditive E] [MonoidalPreadditive E']
    [MonoidalClosed E] [MonoidalClosed E']
    [HasCoproducts.{0} E] [HasCoproducts.{0} E']
    (P : E ⥤ E') [P.Additive]
    (μ : ∀ X Y : E, P.obj (X ⊗ Y) ≅ P.obj X ⊗ P.obj Y)
    (hμ : ∀ {X X' Y Y' : E} (f : X ⟶ X') (g : Y ⟶ Y'),
      P.map (f ⊗ₘ g) ≫ (μ X' Y').hom = (μ X Y).hom ≫ (P.map f ⊗ₘ P.map g))
    (G : E' ⥤ E) (am : P ⊣ G) (j₀ : P.obj (𝟙_ E) ≅ 𝟙_ E')
    (hunit : ∀ M : E, (MonoidalCategory.rightUnitor (P.obj M)).inv ≫
      (P.obj M ◁ j₀.inv) ≫ (μ M (𝟙_ E)).inv =
        P.map (MonoidalCategory.rightUnitor M).inv) :
    TensorPullbackComparison (P.mapHomologicalComplex (.up ℤ))
      ((MonoidalCategory.curriedTensor E).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ))
      ((MonoidalCategory.curriedTensor E').map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ))
      ((HomologicalComplex.single E (.up ℤ) 0).obj (𝟙_ E))
      ((HomologicalComplex.single E' (.up ℤ) 0).obj (𝟙_ E'))
      (fun N ↦ HomologicalComplex.rightUnitor N)
      (fun N ↦ HomologicalComplex.rightUnitor N) := by
  let Pc := P.mapHomologicalComplex (.up ℤ)
  let RX := (HomologicalComplex.single E (.up ℤ) 0).obj (𝟙_ E)
  let j := (HomologicalComplex.singleMapHomologicalComplex P (.up ℤ) 0).app (𝟙_ E) ≪≫
    (HomologicalComplex.single E' (.up ℤ) 0).mapIso j₀
  let β (N M : CochainComplex E ℤ) :=
    @asIso _ _ _ _ (tensorPullbackTotal P μ hμ N M)
      (tensorPullbackTotal_isIso P μ hμ G am N M)
  have hβ {N N' M M' : CochainComplex E ℤ} (f : N ⟶ N') (g : M ⟶ M') :
      HomologicalComplex.mapBifunctorMap (Pc.map f) (Pc.map g)
          (MonoidalCategory.curriedTensor E') (.up ℤ) ≫ (β N' M').hom =
        (β N M).hom ≫ Pc.map (HomologicalComplex.mapBifunctorMap f g
          (MonoidalCategory.curriedTensor E) (.up ℤ)) := by
    exact SheafOfModules.CanonicalTensorPullbackProof.tensorPullbackTotal_naturality
      P μ hμ f g
  refine ⟨j, fun N M ↦ (β N M).symm, ?_, ?_, ?_⟩
  · intro N M M' g
    dsimp only [Functor.map₂HomologicalComplex]
    apply inverseNaturality
    simpa only [Pc.map_id] using hβ (𝟙 N) g
  · intro N N' M f
    dsimp only [Functor.map₂HomologicalComplex]
    apply inverseNaturality
    simpa only [Pc.map_id] using hβ f (𝟙 M)
  · intro N
    let T := (MonoidalCategory.curriedTensor E').map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)
    exact normalizedComposite _ (β N RX).symm ((T.obj (Pc.obj N)).mapIso j) _
      (tensorTotalRightUnit P μ hμ j₀ hunit N)

section DoubleComparison

variable {E : Type u₁} [Category.{w₁} E] [Preadditive E] [HasZeroObject E]
variable {E' : Type u₂} [Category.{w₂} E'] [Preadditive E'] [HasZeroObject E']
variable (P : E ⥤ E') [P.Additive] {X : E} {Y : E'}

omit [Preadditive E] [HasZeroObject E] [Preadditive E'] [HasZeroObject E'] [P.Additive] in
/-- Transport of ordered two-term tensor diagrams.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-transport). -/
theorem map_power_intertwines (f : End X) (g : End Y) (e : P.obj X ≅ Y)
    (h : P.map f.asHom ≫ e.hom = e.hom ≫ g.asHom) (n : ℕ) :
    P.map (f ^ n).asHom ≫ e.hom = e.hom ≫ (g ^ n).asHom := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, End.mul_asHom, P.map_comp, Category.assoc, ih]
    rw [← Category.assoc, h, Category.assoc]

noncomputable def doubleComparisonX (f : End X) (g : End Y)
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

noncomputable def doubleComparison (f : End X) (g : End Y)
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
variable (P : Modules R ⥤ Modules S) [P.Additive]
variable (s : (R.obj ⋙ forget CommRingCat).sections)
variable (t : (S.obj ⋙ forget CommRingCat).sections)

noncomputable def factorIso
    (e : P.obj (SheafOfModules.unit (siteModuleRings R)) ≅
      SheafOfModules.unit (siteModuleRings S))
    (h : P.map (ringedKoszulScalar R s).asHom ≫ e.hom =
      e.hom ≫ (ringedKoszulScalar S t).asHom) (m : ℕ) :
    (P.mapHomologicalComplex (.up ℤ)).obj (ringedKoszulFactor R s m) ≅
      ringedKoszulFactor S t m :=
  doubleComparison P _ _ e (map_power_intertwines P _ _ e h (m + 1))

/-- Transport of ordered two-term tensor diagrams.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-transport). -/
theorem factorIso_step
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

noncomputable def factorsIso
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

noncomputable def rankOneIso
    (u : (P.mapHomologicalComplex (.up ℤ)).obj (ringedSiteRingComplex R) ≅
      ringedSiteRingComplex S) :
    P.obj (SheafOfModules.unit (siteModuleRings R)) ≅
      SheafOfModules.unit (siteModuleRings S) :=
  (P.mapIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _)).symm ≪≫
    HomologicalComplex.Hom.isoApp u 0 ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) 0 _

/-- Transport of ordered two-term tensor diagrams.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-transport). -/
theorem factorIso_projection
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

/-- Transport of ordered two-term tensor diagrams.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-transport). -/
def tensorNatIso
    (H : TensorPullbackComparison.{u₁, u₂, w₁, w₂} P T T' R S ρ ρ') :
    Functor.uncurry.obj T ⋙ P ≅ P.prod P ⋙ Functor.uncurry.obj T' :=
  NatIso.ofComponents (fun x ↦ H.t x.1 x.2) (by
    intro x y f
    change P.map ((T.map f.1).app x.2 ≫ (T.obj y.1).map f.2) ≫ _ = _
    rw [P.map_comp, Category.assoc, H.rightNaturality,
      ← Category.assoc, H.leftNaturality, Category.assoc]
    rfl)

/-- Transport of ordered two-term tensor diagrams.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-transport). -/
theorem tensor_naturality
    (H : TensorPullbackComparison.{u₁, u₂, w₁, w₂} P T T' R S ρ ρ') {X X' Y Y' : E}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    P.map ((Functor.uncurry.obj T).map (f ×ₘ g)) ≫ (H.t X' Y').hom =
      (H.t X Y).hom ≫ (Functor.uncurry.obj T').map (P.map f ×ₘ P.map g) :=
  (tensorNatIso H).hom.naturality (f ×ₘ g)

/-- Transport of ordered two-term tensor diagrams.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
Proof step 1: Lift the binary comparison to total complexes using the existing coproduct-
preserving tensor pullback map and its invertibility. Check inverse right-unit coherence after
every total-tensor inclusion: only the zero-degree unit summand survives, where the asserted
formula reduces to module right-unit coherence. Convert forward naturality to inverse naturality
by cancelling isomorphisms. Package these maps in TensorPullbackComparison.
Proof step 2: Intertwining endomorphisms also intertwine their powers, by induction. Compare each
degree of the two-term complex using singleMapHomologicalComplex and the specified unit
isomorphism; commutation with its differential is the intertwining identity. Its two transition
components are an identity and the scalar power, so the same calculations prove factor
naturality. The projection comparison is checked in the two nonzero degrees.
Proof step 3: Induct on the length of the ordered tensor list. The empty list is the unit
comparison. For a successor, compose the binary tensor comparison with the factor and tail
isomorphisms. Naturality follows by tensor bifunctoriality and the induction hypothesis. For
projection compatibility, use right-naturality, the factor projection identity, the tail
projection identity and right-unit coherence.
(blueprint: lem-f5-koszul-scalar-transport). -/
def tensorDiagramIso
    (H : TensorPullbackComparison.{u₁, u₂, w₁, w₂} P T T' R S ρ ρ') {X Y : ℕ ⥤ E} {X' Y' : ℕ ⥤ E'}
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

/-- Transport of ordered two-term tensor diagrams.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-transport). -/
theorem tensor_augmented
    (H : TensorPullbackComparison.{u₁, u₂, w₁, w₂} P T T' R S ρ ρ') {X Y : E} {X' Y' : E'}
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

/-- Transport of ordered two-term tensor diagrams.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-transport). -/
theorem koszulUnit_right (R : Sheaf J CommRingCat.{v}) :
    (ringedKoszulUnitTensorIso R).hom =
      (ringedKoszulRightUnitIso R (ringedSiteRingComplex R)).hom := by
  let := SheafOfModules.isGrothendieckAbelian (siteModuleRings R)
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := SheafOfModules.monoidalClosed (R := R)
  let : HasColimitsOfSize.{0, 0} (Modules R) := hasColimitsOfSizeShrink.{0, 0, v, v} _
  change (MonoidalCategory.leftUnitor (𝟙_ (ringedSiteComplex R))).hom =
    (MonoidalCategory.rightUnitor (𝟙_ (ringedSiteComplex R))).hom
  exact MonoidalCategory.unitors_equal

/-- Transport of ordered two-term tensor diagrams.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-transport). -/
theorem koszulRight_natural (S : Sheaf K CommRingCat.{v})
    {M N : ringedSiteComplex S} (f : M ⟶ N) :
    ((ringedKoszulTensor S).map f).app (ringedSiteRingComplex S) ≫
        (ringedKoszulRightUnitIso S N).hom =
      (ringedKoszulRightUnitIso S M).hom ≫ f := by
  let := SheafOfModules.isGrothendieckAbelian (siteModuleRings S)
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.symmetricCategory S
  let := Classical.choice (SheafOfModules.tensorClosed S).1
  let := SheafOfModules.monoidalClosed (R := S)
  let : HasColimitsOfSize.{0, 0} (Modules S) := hasColimitsOfSizeShrink.{0, 0, v, v} _
  exact MonoidalCategory.rightUnitor_naturality f

end KoszulInduction

/-- Transport of ordered two-term tensor diagrams.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-transport). -/
theorem scalar_eq_smul {C : Type v} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{v}}
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

end ScalarKoszulTransport

end CategoryTheory.FlatScalarKoszul
