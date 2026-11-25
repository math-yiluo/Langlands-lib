/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjectionInterfaces
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import all WeilConjectures.CategoryTheory.Localized.LocalizedExtensionZeroLinearDerived
import all WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownLevelRealizationData
import all WeilConjectures.CategoryTheory.Finite.FiniteFreeExceptionalMate
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
/-! # Finite-free strict etale scalar comparison -/
@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
@[instance_reducible] private def levelLinear (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) (n : ℕ) :
    Linear (O ⧸ Ideal.span {ell} ^ (n + 1)) (strictEtaleLevel T O ell n) := by
  let R := coefficientQuotientSheaf (J := T.smallEtaleTopology) O ell n
  let sigma := fun V : T.Etaleᵒᵖ ↦
    ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
      (CommRingCat.of (O ⧸ Ideal.span {ell} ^ (n + 1))))).app V).hom
  exact CategoryTheory.sectionLinear R _ sigma (by
    intro V W f b
    exact congrArg (fun g ↦ g b)
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (CommRingCat.of (O ⧸ Ideal.span {ell} ^ (n + 1))))).naturality f).symm)

private theorem constantSection_apply (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n : ℕ) (r : O ⧸ Ideal.span {ell} ^ (n + 1)) (V : T.Etaleᵒᵖ)
    (x : ((constantSheaf T.smallEtaleTopology (Type (u + 1))).obj PUnit).obj.obj V) :
    (coefficientConstantSection (J := T.smallEtaleTopology) O ell n r).hom.app V x =
      (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (CommRingCat.of (O ⧸ Ideal.span {ell} ^ (n + 1))))).app V r := by
  let J := T.smallEtaleTopology
  let P := (Functor.const T.Etaleᵒᵖ).obj PUnit.{u + 2}
  let R := coefficientQuotientSheaf (J := J) O ell n
  let Rset := (sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj R
  have : IsIso (toSheafify J P) :=
    isIso_toSheafify J (Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit)
  obtain ⟨p, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((toSheafify J P).app V)).2 x
  let t : P ⟶ Rset.obj :=
    (Functor.const T.Etaleᵒᵖ).map (TypeCat.ofHom (fun _ : PUnit.{u + 2} ↦ r)) ≫
      whiskerRight (toSheafify J ((Functor.const T.Etaleᵒᵖ).obj
        (CommRingCat.of (O ⧸ Ideal.span {ell} ^ (n + 1)))))
          (CategoryTheory.forget CommRingCat.{u + 1})
  have h := ((sheafificationAdjunction J (Type (u + 1))).homEquiv P Rset)
    |>.apply_symm_apply t
  exact congrArg (fun f ↦ f.app V p) h

private theorem transportBasis
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [Preadditive C] [Preadditive D] [Preadditive C'] [Preadditive D']
    [HasFiniteBiproducts C] [HasFiniteBiproducts C']
    {B : Type*} [Ring B] [Linear B D] [Linear B D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (F : C ⥤ C') (G : D ⥤ D') [F.Additive]
    [F.IsEquivalence] [G.IsEquivalence] [G.Linear B]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (beta : R ⋙ F ≅ G ⋙ R')
    (r : ℕ) (coeff : Fin r → B)
    (h : ∀ M, IsIso (biproduct.desc fun i : Fin r ↦
      adj'.unit.app M ≫ R'.map (coeff i • 𝟙 _))) (M : C) :
    IsIso (biproduct.desc fun i : Fin r ↦ adj.unit.app M ≫ R.map (coeff i • 𝟙 _)) := by
  let alpha := ((mateEquiv adj adj').symm beta.hom)
  have : IsIso alpha := isIso_inverseMate_of_equivalences adj adj' beta
  have hu := unit_mateEquiv_symm adj adj' beta.hom M
  change F.map (adj.unit.app M) ≫ beta.hom.app (L.obj M) =
    adj'.unit.app (F.obj M) ≫ R'.map (alpha.app M) at hu
  have hc (i : Fin r) :
      F.map (adj.unit.app M ≫ R.map (coeff i • 𝟙 _)) ≫
          beta.hom.app (L.obj M) =
        (adj'.unit.app (F.obj M) ≫ R'.map (coeff i • 𝟙 _)) ≫
          R'.map (alpha.app M) := by
    rw [F.map_comp, Category.assoc]
    have hn := beta.hom.naturality (coeff i • 𝟙 (L.obj M))
    change F.map (R.map _) ≫ beta.hom.app _ =
      beta.hom.app _ ≫ R'.map (G.map _) at hn
    rw [hn, ← Category.assoc, hu, G.map_smul, G.map_id]
    simp only [Category.assoc, ← R'.map_comp]
    congr 2
    rw [Linear.comp_smul, Linear.smul_comp, Category.id_comp]
    exact congrArg (fun t ↦ coeff i • t) (Category.comp_id (alpha.app M))
  have he : (biproduct.desc fun i : Fin r ↦
      F.map (adj.unit.app M ≫ R.map (coeff i • 𝟙 _))) ≫ beta.hom.app (L.obj M) =
        (biproduct.desc fun i : Fin r ↦ adj'.unit.app (F.obj M) ≫
          R'.map (coeff i • 𝟙 _)) ≫ R'.map (alpha.app M) := by
    ext i
    simpa only [biproduct.ι_desc_assoc] using hc i
  have : IsIso (biproduct.desc fun i : Fin r ↦
      F.map (adj.unit.app M ≫ R.map (coeff i • 𝟙 _))) := by
    have := h (F.obj M)
    have : IsIso ((biproduct.desc fun i : Fin r ↦
        F.map (adj.unit.app M ≫ R.map (coeff i • 𝟙 _))) ≫
          beta.hom.app (L.obj M)) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (beta.hom.app (L.obj M))
  have := (Functor.isIso_map_biproductDesc F
    (fun i : Fin r ↦ adj.unit.app M ≫ R.map (coeff i • 𝟙 _))).2 this
  exact isIso_of_reflects_iso _ F

private theorem scalarBasis
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u}) (n r : ℕ)
    (basis : Module.Basis (Fin r) (O ⧸ Ideal.span {ell} ^ (index n + 1))
      ((ModuleCat.restrictScalars (a.ring n)).obj
        (ModuleCat.of (O' ⧸ Ideal.span {mu} ^ (n + 1))
          (O' ⧸ Ideal.span {mu} ^ (n + 1)))))
    (D : StrictEtaleLevelScalar a T n) :
    let := levelLinear T O' mu n
    ∀ M, IsIso (biproduct.desc fun i : Fin r ↦
      D.derivedAdj.unit.app M ≫ D.restriction.map
        (ModuleCat.restrictScalarsSelfVal (a.ring n) (basis i) • 𝟙 (D.derived.obj M))) := by
  let := levelLinear T O' mu n
  let A := O ⧸ Ideal.span {ell} ^ (index n + 1)
  let B := O' ⧸ Ideal.span {mu} ^ (n + 1)
  let : Algebra A B := (a.ring n).toAlgebra
  change Module.Basis (Fin r) A B at basis
  let FA : strictEtaleLevel T O ell (index n) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat A) :=
    strictEtaleBrownConstant O ell T (index n)
  let FB : strictEtaleLevel T O' mu n ⥤
      Sheaf T.smallEtaleTopology (ModuleCat B) := strictEtaleBrownConstant O' mu T n
  have : FA.Additive := brownConstantAdditive T A
  have : FB.Additive := brownConstantAdditive T B
  have : FA.IsEquivalence := brownConstantEquivalence T A
  have : FB.IsEquivalence := brownConstantEquivalence T B
  have : FB.Linear B := by
    constructor
    intro M N f b
    ext U x
    rfl
  obtain ⟨SC⟩ := CategoryTheory.exceptionalScalarPresentation.{u + 1, u + 1, u + 1, u}
    T.smallEtaleTopology r basis
  let R := SheafOfModules.restrictScalars
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T n))
  let e : D.restriction ≅ R.mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleLevel T O' mu n) (.up ℤ))
      (DerivedCategory.Q ⋙ D.restriction) (DerivedCategory.Q ⋙ R.mapDerivedCategory)
      D.restriction R.mapDerivedCategory (D.restrictionFactors ≪≫ R.mapDerivedCategoryFactors.symm)
  let beta : D.restriction ⋙ FA.mapDerivedCategory ≅ FB.mapDerivedCategory ⋙
      (Sheaf.restrictScalars T.smallEtaleTopology (a.ring n)).mapDerivedCategory :=
    isoWhiskerRight e FA.mapDerivedCategory ≪≫
      Functor.mapDerivedCategorySquareIso
        (A := strictEtaleLevel T O' mu n) (B := strictEtaleLevel T O ell (index n))
        (brownGenericRestriction T (.of A) (.of B) (CommRingCat.ofHom (a.ring n)))
  dsimp only
  intro M
  apply transportBasis FA.mapDerivedCategory FB.mapDerivedCategory D.derivedAdj SC.adj beta
    r (fun i ↦ basis i) (fun K ↦ ?_) M
  have he : (biproduct.desc fun i : Fin r ↦ SC.adj.unit.app K ≫
      (Sheaf.restrictScalars T.smallEtaleTopology (algebraMap A B)).mapDerivedCategory.map
        (basis i • 𝟙 (SC.T.obj K))) = (SC.coordinates K).inv := by
    ext i
    exact (biproduct.ι_desc _ i).trans (SC.column K i).symm
  rw [he]
  infer_instance

end AlgebraicGeometry
