/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionTensorRightComputation
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison

/-! # Section realization of the restricted scalar computation counit

(auxiliary; not a blueprint node)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  CategoryTheory.Localization.Monoidal.tensorBifunctor

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapHomologicalComplexUpToQuasiIso
  CategoryTheory.Functor.mapHomologicalComplexUpToQuasiIsoFactors
  ModuleRingedComparison.tensor
  ModuleRingedComparison.qTensor ModuleRingedComparison.tensorComparison
  Mod.inducingFunctorData SheafOfModules.monoidalCategory
  sectionScalarCoefficient compute
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local irreducible] sectionTensorRightLocalization

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

private theorem internalGenerator_hom_ext
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [UnivLE.{max v w, u}] [HasSheafify J AddCommGrpCat.{u}]
    [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S] (a : R ⟶ S) [IsMonHom a]
    (M : Mod (Sheaf J AddCommGrpCat.{u}) R) {N : Sheaf J AddCommGrpCat.{u}}
    {f g : ((Mod.extendScalars a).obj M).X ⟶ N}
    (h : ∀ (U : Cᵒᵖ) (z : S.obj.obj U) (x : M.X.obj.obj U),
      (f.hom.app U) (internalScalarGenerator J a M U z x) =
        (g.hom.app U) (internalScalarGenerator J a M U z x)) : f = g := by
  apply (cancel_epi (Mod.extendπ a M)).mp
  apply Sheaf.tensor_hom_ext
  ext U y
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | tmul z x => exact h U z x

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)] in
private theorem internal_tensor_generator (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) (t : TensorNormalization a T) (M : Modules Λ T)
    (U : T.ProEtᵒᵖ) (z : (condensedRingObj Λ' T).obj.obj U) (x : M.X.obj.obj U) :
    ((t.ordinary.hom.app M).hom.hom.app U)
      (internalScalarGenerator (Scheme.ProEt.topology T) (coefficientMap a T) M U z x) =
    ModuleRingedComparison.internalPureTensor Λ T M (B₀ a T) U x z := by
  let J := Scheme.ProEt.topology T
  let F := sheafToPresheaf J Ab.{u + 1}
  have hc : Mod.extendπ (coefficientMap a T) M ≫
      (Mod.extendForgetTensorObjIso (coefficientMap a T) M).hom =
      Mod.tensorObjπ (B₀ a T) M := Mod.extendπ_extendDescHom _ _ _
  have h := congrArg (fun k ↦ Functor.LaxMonoidal.μ F (condensedRingObj Λ' T) M.X ≫
    F.map k) hc
  simp only [CategoryTheory.Functor.map_comp] at h
  have he := congrArg (fun k ↦ (k.app U).hom (z ⊗ₜ[ℤ] x)) h
  change ((Mod.extendForgetTensorObjIso (coefficientMap a T) M).hom.hom.app U)
      (internalScalarGenerator J (coefficientMap a T) M U z x) =
    comparison_internalTmul J (condensedRingObj Λ T) (B₀ a T) M U z x at he
  rw [t.ordinary_hom M]
  change ((β_ (B₀ a T) M).hom.hom.hom.app U)
    (((Mod.extendForgetTensorObjIso (coefficientMap a T) M).hom.hom.app U) _) = _
  rw [he]
  exact comparison_internalTmul_braiding J (condensedRingObj Λ T) (B₀ a T) M U z x

-- Generator comparisons elaborate both internal and section module tensor structures.
private theorem ordinary_computation_transport (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) (s : SectionScalarComparison a T)
    (hs : SectionScalarNormalized a T s) (t : TensorNormalization a T)
    (o : s.pair.extension ⋙ SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) ≅
        tensorRight ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)))
    (ho : (∀ (M : ModuleRingedComparison.modules Λ T) (U : T.ProEtᵒᵖ)
      (z : (ModuleRingedComparison.ring Λ' T).obj.obj U) (x : M.val.obj U),
    (o.hom.app M).val.app U
      ((eqToHom (s.pair.extension_obj M).symm).val.app U
        ((toSheafify (Scheme.ProEt.topology T)
          (SheafOfModules.changeOfRingsPresheaf
            (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
              (coefficientMap a T)) M).presheaf).app U
              (z ⊗ₜ[(ModuleRingedComparison.ring Λ T).obj.obj U,((sectionScalarMap.{u + 1, u + 1, u}
                  (Scheme.ProEt.topology T) (coefficientMap a T)).hom.app U).hom] x))) =
      ModuleRingedComparison.sectionPureTensor Λ T M
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) U x z))
    (M : Modules Λ T) :
    (ModuleRingedComparison.equivalence Λ T).functor.map (t.ordinary.hom.app M) ≫
        (sectionTensorRightComparison a T).hom.app M =
      s.restriction.hom.app ((extension a T).obj M) ≫
        (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))).map
            (s.ordinary.hom.app M) ≫
        o.hom.app ((ModuleRingedComparison.equivalence Λ T).functor.obj M) := by
  apply (SheafOfModules.toSheaf _).map_injective
  apply internalGenerator_hom_ext (Scheme.ProEt.topology T) (coefficientMap a T) M
  intro U z x
  change ((sectionTensorRightComparison a T).hom.app M).val.app U
      (((t.ordinary.hom.app M).hom.hom.app U)
        (internalScalarGenerator (Scheme.ProEt.topology T) (coefficientMap a T)
          M U z x)) =
    (o.hom.app ((ModuleRingedComparison.equivalence Λ T).functor.obj M)).val.app U
      ((s.ordinary.hom.app M).val.app U
        ((s.restriction.hom.app ((extension a T).obj M)).val.app U
          (internalScalarGenerator (Scheme.ProEt.topology T) (coefficientMap a T)
            M U z x)))
  have htensor := congrArg
    (((sectionTensorRightComparison a T).hom.app M).val.app U)
    (internal_tensor_generator a T t M U z x)
  have hgen := congrArg
    ((eqToHom (s.pair.extension_obj
      ((ModuleRingedComparison.equivalence Λ T).functor.obj M)).symm).val.app U)
    (hs.2.1 M U z x)
  simp only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, eqToHom_trans, eqToHom_refl,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hgen
  have hscalar := congrArg
    ((o.hom.app ((ModuleRingedComparison.equivalence Λ T).functor.obj M)).val.app U) hgen
  have hr := congrArg (fun y ↦
    (o.hom.app ((ModuleRingedComparison.equivalence Λ T).functor.obj M)).val.app U
      ((s.ordinary.hom.app M).val.app U y))
    (hs.1 ((extension a T).obj M) U
      (internalScalarGenerator (Scheme.ProEt.topology T) (coefficientMap a T) M U z x))
  have hord := (ModuleRingedComparison.ordinaryTensorComparison_existsUnique Λ T M
    (B₀ a T)).exists.choose_spec U x z
  exact htensor.trans (hord.trans
    ((ho ((ModuleRingedComparison.equivalence Λ T).functor.obj M) U z x).symm.trans
      (hscalar.symm.trans hr.symm)))

attribute [local implicit_reducible] ModuleRingedComparison.sectionLocalizationComparison
  CategoryTheory.Functor.map₂HomologicalComplex

attribute [local irreducible] sectionTensorRightComparison

private theorem complexSquare
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    (L : A ⥤ B) (V : B ⥤ A) (E : A ⥤ C) (E' : B ⥤ D)
    (G : C ⥤ D) (U : D ⥤ C) (S : A ⥤ A) (R : C ⥤ C)
    [L.Additive] [V.Additive] [E.Additive] [E'.Additive]
    [G.Additive] [U.Additive] [S.Additive] [R.Additive]
    (c : L ⋙ V ≅ S) (r : V ⋙ E ≅ E' ⋙ U) (d : L ⋙ E' ≅ E ⋙ G)
    (q : S ⋙ E ≅ E ⋙ R) (k : G ⋙ U ≅ R)
    (h : ∀ M, E.map (c.hom.app M) ≫ q.hom.app M =
      r.hom.app (L.obj M) ≫ U.map (d.hom.app M) ≫ k.hom.app (E.obj M))
    (P : CochainComplex A ℤ) :
    (E.mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso c (.up ℤ)).hom.app P) ≫
      (Functor.mapHomologicalComplexCompIso q (.up ℤ)).hom.app P =
    (Functor.mapHomologicalComplexCompIso r (.up ℤ)).hom.app
        ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
      (U.mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex d (.up ℤ)).hom.app P) ≫
      (Functor.mapHomologicalComplexCompIso k (.up ℤ)).hom.app
        ((E.mapHomologicalComplex (.up ℤ)).obj P) := by
  ext n : 1
  exact h (P.X n)

private theorem exactSquareFactors
    {C D E H : Type*} [Category* C] [Category* D] [Category* E] [Category* H]
    [Abelian C] [Abelian D] [Abelian E] [Abelian H]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory H]
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ H) (G' : H ⥤ E)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (r : F ⋙ G ≅ F' ⋙ G') (P : CochainComplex C ℤ) :
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app P) =
    ((Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj P) ≫
      (Functor.mapDerivedCategoryNatIso r).hom.app (DerivedCategory.Q.obj P) ≫
      (Functor.mapDerivedCategoryCompIso F' G').inv.app (DerivedCategory.Q.obj P)) ≫
      G'.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app P) ≫
      G'.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj P) := by
  simp only [Category.assoc]
  apply (cancel_epi
    ((Functor.mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj P))).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]

private theorem mapTwoThree
    {C D : Type*} [Category* C] [Category* D] (Q : C ⥤ D)
    {A B Z E F : C} {f : A ⟶ B} {g : B ⟶ Z}
    {r : A ⟶ E} {u : E ⟶ F} {k : F ⟶ Z} (h : f ≫ g = r ≫ u ≫ k) :
    Q.map f ≫ Q.map g = Q.map r ≫ Q.map u ≫ Q.map k := by
  simpa only [Q.map_comp] using congrArg Q.map h

private theorem mapTriple
    {C D : Type*} [Category* C] [Category* D] (Q : C ⥤ D)
    {A B C' Z E F : C} {f : A ⟶ B} {g : B ⟶ C'} {h : C' ⟶ Z}
    {r : A ⟶ E} {s : E ⟶ F} {t : F ⟶ Z} (e : f ≫ g ≫ h = r ≫ s ≫ t) :
    Q.map f ≫ Q.map g ≫ Q.map h = Q.map r ≫ Q.map s ≫ Q.map t := by
  simpa only [Q.map_comp] using congrArg Q.map e

private theorem scalarPasteMapped
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (Q : E ⥤ D) {X₀ X₁ X₂ X₃ : C} {R H : E}
    {A B C' L M N O P P' : D}
    {f : X₀ ⟶ X₁} {g : X₁ ⟶ X₂} {c : X₂ ⟶ X₃}
    (α : F.obj X₃ ≅ Q.obj R) (q : R ≅ H)
    {α₀ : F.obj X₂ ⟶ A} {e : A ⟶ Q.obj R}
    {r : A ⟶ B} {u : B ⟶ C'} {k : C' ⟶ Q.obj H}
    {v : F.obj X₁ ⟶ L} {a : L ⟶ M} {b : M ⟶ B}
    {w : F.obj X₀ ⟶ N} {l : N ⟶ L} {d : M ⟶ O} {b' : O ⟶ C'}
    {x : N ⟶ P} {y : P ⟶ P'} {z : P' ⟶ O}
    (hloc : F.map c ≫ α.hom = α₀ ≫ e)
    (ho : e ≫ Q.map q.hom = r ≫ u ≫ k)
    (hr : F.map g ≫ α₀ ≫ r = v ≫ a ≫ b)
    (hn : F.map f ≫ v = w ≫ l) (hd : d ≫ b' = b ≫ u)
    (hs : l ≫ a ≫ d = x ≫ y ≫ z) :
    F.map (f ≫ g ≫ c) ≫ (α ≪≫ Q.mapIso q).hom =
      w ≫ x ≫ y ≫ z ≫ b' ≫ k := by
  simp only [F.map_comp, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% hloc, ho, reassoc_of% hr, reassoc_of% hn,
    ← reassoc_of% hd, reassoc_of% hs]

private theorem restriction_computation_transport (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) (s : SectionScalarComparison a T)
    (P : CochainComplex (Modules Λ' T) ℤ) :
    (ModuleRingedComparison.derivedEquivalence Λ T).functor.map
        ((V₀ a T).mapDerivedCategoryFactors.hom.app P) ≫
      (ModuleRingedComparison.sectionLocalizationComparison Λ T
        (((V₀ a T).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso s.restriction (.up ℤ)).hom.app P) =
    (sectionScalarRestriction a T s).hom.app (DerivedCategory.Q.obj P) ≫
      (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))).map
          (ModuleRingedComparison.sectionLocalizationComparison Λ' T P).hom ≫
      (SheafOfModules.scalarRestrictionComparison.{u + 1, u, u + 1, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology T) (coefficientMap a T))).hom.app
          (((ModuleRingedComparison.equivalence Λ' T).functor.mapHomologicalComplex
                (.up ℤ)).obj P) := by
  exact exactSquareFactors (V₀ a T) (ModuleRingedComparison.equivalence Λ T).functor
    (ModuleRingedComparison.equivalence Λ' T).functor
    (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)))
    s.restriction P

attribute [local irreducible] sectionScalarRestriction

-- Generator comparisons elaborate both internal and section module tensor structures.
/-- Scalar normalization and ordinary generators identify the restricted scalar
computation after the section equivalence. Source: Stacks 03EK, 06YY, 07A6;
scalar and ordinary part of the conjugate-computation node's first step.
(auxiliary; not a blueprint node).

Proof: substitute the K-flat computation clause of hs. Naturality of exact
restriction moves the scalar computation counit through its section comparison.
The composition and natural-isomorphism factor equations for mapDerivedCategory
identify the remaining localization factors with the termwise restriction
comparison. It remains to compare the ordinary maps in each degree. Precompose
with scalar-extension generators. The ordinary clauses of hs identify the scalar
comparison and restriction with their actual section maps. The prescribed formula
for o and the balanced-tensor formula for t.ordinary then send z tensor x to
x tensor z. Tensor induction and sheafification extend this equality to all
sections; equality degreewise gives equality of chain maps. Apply Q and compose
with the scalar counit. Only P being flat-term K-flat is used, to apply hs;
there is no derived tensor comparison or derived e in this assertion. -/
theorem section_scalar_computation_transport (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) (s : SectionScalarComparison a T)
    (hs : SectionScalarNormalized a T s) (t : TensorNormalization a T)
    (o : s.pair.extension ⋙ SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) ≅
        tensorRight ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)))
    (ho : (∀ (M : ModuleRingedComparison.modules Λ T) (U : T.ProEtᵒᵖ)
      (z : (ModuleRingedComparison.ring Λ' T).obj.obj U) (x : M.val.obj U),
    (o.hom.app M).val.app U
      ((eqToHom (s.pair.extension_obj M).symm).val.app U
        ((toSheafify (Scheme.ProEt.topology T)
          (SheafOfModules.changeOfRingsPresheaf
            (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
              (coefficientMap a T)) M).presheaf).app U
              (z ⊗ₜ[(ModuleRingedComparison.ring Λ T).obj.obj U,((sectionScalarMap.{u + 1, u + 1, u}
                  (Scheme.ProEt.topology T) (coefficientMap a T)).hom.app U).hom] x))) =
      ModuleRingedComparison.sectionPureTensor Λ T M
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) U x z))
    (P : CochainComplex (Modules Λ T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := ModuleRingedComparison.ring Λ T)
      (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex
                (.up ℤ)).obj P))
    (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := ModuleRingedComparison.ring Λ T)
      ((ModuleRingedComparison.equivalence Λ T).functor.obj (P.X n))) :
    (ModuleRingedComparison.derivedEquivalence Λ T).functor.map
      ((V a T).map (compute a T P) ≫
        (V₀ a T).mapDerivedCategoryFactors.hom.app
          (((extension a T).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso t.ordinary (.up ℤ)).hom.app P)) ≫
        (sectionTensorRightLocalization a T P).hom =
      (sectionScalarRestriction a T s).hom.app ((D a T).obj (DerivedCategory.Q.obj P)) ≫
        (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))).map
            (s.derived.hom.app (DerivedCategory.Q.obj P)) ≫
        (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))).map
            (s.pair.derived.map
              (ModuleRingedComparison.sectionLocalizationComparison Λ T P).hom) ≫
        (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))).map
            (SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
              s.pair.extension s.pair.extension_additive s.pair.derived s.pair.counit
              (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex
                (.up ℤ)).obj P)) ≫
        (SheafOfModules.scalarRestrictionComparison.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology T) (coefficientMap a T))).hom.app
            ((SheafOfModules.scalarComplex.{u + 1, u, u + 1}
              s.pair.extension s.pair.extension_additive).obj
              (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex
                (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso o (.up ℤ)).hom.app
          (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex
                (.up ℤ)).obj P)) := by
  let E := (ModuleRingedComparison.equivalence Λ T).functor
  let E' := (ModuleRingedComparison.equivalence Λ' T).functor
  let F := E.mapDerivedCategory
  let F' := E'.mapDerivedCategory
  let U₀ := SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
    (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))
  let U := SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
    (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))
  let A := (E.mapHomologicalComplex (.up ℤ)).obj P
  let C := ((extension a T).mapHomologicalComplex (.up ℤ)).obj P
  let G := SheafOfModules.scalarComplex.{u + 1, u, u + 1} s.pair.extension s.pair.extension_additive
  let c := (Functor.mapHomologicalComplexCompIso t.ordinary (.up ℤ)).hom.app P
  let d := (NatIso.mapHomologicalComplex s.ordinary (.up ℤ)).hom.app P
  let r := (Functor.mapHomologicalComplexCompIso s.restriction (.up ℤ)).hom.app C
  let q := (Functor.mapHomologicalComplexCompIso (sectionTensorRightComparison a T)
    (.up ℤ)).hom.app P
  let k := (Functor.mapHomologicalComplexCompIso o (.up ℤ)).hom.app A
  have hord := complexSquare (extension a T) (V₀ a T) E E' s.pair.extension U₀
      (tensorRight (B₀ a T))
      (tensorRight (E.obj (B₀ a T))) t.ordinary s.restriction s.ordinary
      (sectionTensorRightComparison a T) o
      (ordinary_computation_transport a T s hs t o ho) P
  have hloc := E.mapDerivedCategoryFactors.hom.naturality c
  change F.map (DerivedCategory.Q.map c) ≫
      (ModuleRingedComparison.sectionLocalizationComparison Λ T _).hom =
    (ModuleRingedComparison.sectionLocalizationComparison Λ T _).hom ≫
      DerivedCategory.Q.map ((E.mapHomologicalComplex (.up ℤ)).map c) at hloc
  have hr := restriction_computation_transport a T s C
  have hn := (sectionScalarRestriction a T s).hom.naturality (compute a T P)
  change F.map ((V a T).map (compute a T P)) ≫
      (sectionScalarRestriction a T s).hom.app (DerivedCategory.Q.obj C) =
    (sectionScalarRestriction a T s).hom.app ((D a T).obj (DerivedCategory.Q.obj P)) ≫
      U.map (F'.map (compute a T P)) at hn
  have hd := U₀.mapDerivedCategoryFactors.hom.naturality d
  change U.map (DerivedCategory.Q.map d) ≫
      (SheafOfModules.scalarRestrictionComparison.{u + 1, u, u + 1, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology T) (coefficientMap a T))).hom.app (G.obj A) =
    (SheafOfModules.scalarRestrictionComparison.{u + 1, u, u + 1, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology T) (coefficientMap a T))).hom.app
        ((E'.mapHomologicalComplex (.up ℤ)).obj C) ≫
      DerivedCategory.Q.map ((U₀.mapHomologicalComplex (.up ℤ)).map d) at hd
  have hsP := hs.2.2 P hP hflat
  have hoQ := mapTwoThree DerivedCategory.Q hord
  have hsU := mapTriple U hsP
  unfold sectionTensorRightLocalization
  have hcomputed := scalarPasteMapped F DerivedCategory.Q
    (ModuleRingedComparison.sectionLocalizationComparison Λ T _)
    ((Functor.mapHomologicalComplexCompIso (sectionTensorRightComparison a T)
      (.up ℤ)).app P)
    hloc hoQ hr hn hd hsU
  -- Reuse the inferred proof without a second elaborator expansion of section data.
  -- The kernel still checks it against the displayed computation equation.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hcomputed
      | Lean.throwError "missing scalar computation proof"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.ProEtale.QuotientChange
