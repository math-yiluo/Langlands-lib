/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectTransportDescent
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
import all WeilConjectures.AlgebraicGeometry.IntegralCompletedConstantModelTransport

/-! # Reductions and the uniform reduction profile along isomorphisms of coefficient data

Restriction of scalars along the completed isomorphism induced by a datum isomorphism
commutes with the finite reductions, up to the level isomorphisms, and with the constant
reductions, up to the constant quotient ring isomorphisms. Constructibility is invariant
under restriction along an isomorphism of constant finite coefficient rings.

## References

* Bhatt--Scholze, Definition 6.5.1
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective

private local instance (priority := 100000) fixedSmall' (T : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.EssentiallySmall.{u + 1} T.ProEt :=
  CategoryTheory.essentiallySmallSelf.{0} _

private noncomputable local instance (priority := 100000) fixedSheafify'
    (T : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} T

private local instance (priority := 100000) fixedLocallyBijective'
    (T : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Derived restriction along the identity. -/
def pbcDerivedRestrictIdIso {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    pbcDerivedRestrict (𝟙 R) ≅ 𝟭 (DerivedCategory (pbcModules T R)) :=
  Functor.mapDerivedCategoryNatIso (pbcRestrictIdIso R) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- Derived restriction along a ring sheaf isomorphism is an equivalence. -/
def pbcDerivedRestrictIsoEquivalence {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (e : R ≅ S) :
    DerivedCategory (pbcModules T S) ≌ DerivedCategory (pbcModules T R) :=
  CategoryTheory.Equivalence.mk (pbcDerivedRestrict e.hom) (pbcDerivedRestrict e.inv)
    (pbcDerivedRestrictComp e.inv e.hom (𝟙 S) e.inv_hom_id ≪≫ pbcDerivedRestrictIdIso S).symm
    (pbcDerivedRestrictComp e.hom e.inv (𝟙 R) e.hom_inv_id ≪≫ pbcDerivedRestrictIdIso R)

section RingEquiv

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal)

/-- The level isomorphism of finite quotient coefficient sheaves. -/
abbrev AdicCoefficientDatum.levelIso (T : Scheme.{u}) (n : ℕ) :
    (pbcAdicRings T d).obj (op n) ≅ (pbcAdicRings T d').obj (op n) :=
  asIso ((d.ringSystemHom d' φ hφ T).app (op n))

/-- Finite reduction commutes with the transport of coefficient data. -/
def AdicCoefficientDatum.reductionTransportIso (T : Scheme.{u}) (n : ℕ) :
    d.transportDerived d' φ hφ T ⋙ pbcCompletedReduction T d' n ≅
      pbcCompletedReduction T d n ⋙ pbcDerivedRestrict (d.levelIso d' φ hφ T n).inv :=
  let ρ := d.completionIso d' φ hφ T
  let lv := d.levelIso d' φ hφ T n
  let adj₁ := (pbcDerivedRestrictIsoEquivalence ρ.symm).toAdjunction.comp
    (pbcDerivedScalarAdjunction (pbcAdicProjection T d' n))
  let adj₂ := (pbcDerivedScalarAdjunction (pbcAdicProjection T d n)).comp
    (pbcDerivedRestrictIsoEquivalence lv.symm).toAdjunction
  (conjugateIsoEquiv adj₂ adj₁).symm
    (pbcDerivedRestrictComp ρ.hom (pbcAdicProjection T d' n)
        (pbcAdicProjection T d n ≫ lv.hom) (d.completionIso_hom_projection d' φ hφ T n) ≪≫
      (pbcDerivedRestrictComp (pbcAdicProjection T d n) lv.hom
        (pbcAdicProjection T d n ≫ lv.hom) rfl).symm).symm

/-- The constant quotient ring isomorphism. -/
abbrev AdicCoefficientDatum.constantLevelIso (T : Scheme.{u}) (n : ℕ) :
    adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1)) ≅
      adicLisseConstantRing T (A' ⧸ d'.ideal ^ (n + 1)) :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).mapIso
    (d.quotientRingEquiv d' φ hφ n).toCommRingCatIso

/-- The level isomorphisms are compatible with the constant level comparisons. -/
theorem AdicCoefficientDatum.levelConstant_square (T : Scheme.{u}) (n : ℕ) :
    (pbcLevelConstantComparison T d' n).hom ≫ (d.levelIso d' φ hφ T n).inv =
      (d.constantLevelIso d' φ hφ T n).inv ≫ (pbcLevelConstantComparison T d n).hom := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  let := d.quotientFinite
  let := d'.quotientFinite
  exact pbcLevelConstantComparison_naturality T d d' n (d.quotientRingEquiv d' φ hφ n).toRingHom

/-- Constant reduction commutes with the transport of coefficient data. -/
def AdicCoefficientDatum.constantReductionTransportIso (T : Scheme.{u}) (n : ℕ) :
    d.transportDerived d' φ hφ T ⋙ pbcConstantReduction T d' n ≅
      pbcConstantReduction T d n ⋙
        pbcDerivedRestrict (d.constantLevelIso d' φ hφ T n).inv :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (d.reductionTransportIso d' φ hφ T n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (pbcDerivedRestrictComp _ _ _ (d.levelConstant_square d' φ hφ T n) ≪≫
        (pbcDerivedRestrictComp _ _ _ rfl).symm) ≪≫
    (Functor.associator _ _ _).symm

end RingEquiv

section ConstantRing

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (q : Λ ≃+* Λ')

/-- The constant ring sheaf isomorphism induced by a ring isomorphism. -/
abbrev constantRingIso (X : Scheme.{u}) :
    adicLisseConstantRing X Λ ≅ adicLisseConstantRing X Λ' :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).mapIso q.toCommRingCatIso

private theorem constantRingIso_unit (X : Scheme.{u}) (U : X.ProEtᵒᵖ) (a : Λ') :
    (constantRingIso q X).hom.hom.app U
      ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of Λ))).app U (q.symm a)) =
    (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of Λ'))).app U a := by
  have hn := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality
    (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom q.toRingHom))) U)
    (q.symm a)
  simp only [NatTrans.comp_app, CategoryTheory.comp_apply] at hn
  exact hn.symm.trans (congrArg _ (q.apply_symm_apply a))

private theorem smul_congr'' {T : Scheme.{u}} {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (N : pbcModules T R) (U : T.ProEtᵒᵖ) {r s : ((adicLisseForget T).obj R).obj.obj U}
    (h : r = s) (x : N.val.obj U) : r • x = s • x := by rw [h]

private def constantGlobalSectionsIso (X : Scheme.{u}) (Tm : X.ProEt) :
    adicLisseConstantGlobalSections X Λ' Tm ≅
      pbcRestrict (constantRingIso q X).hom ⋙ adicLisseConstantGlobalSections X Λ Tm ⋙
        ModuleCat.restrictScalars q.symm.toRingHom :=
  NatIso.ofComponents (fun N ↦
    { hom := ModuleCat.ofHom (X := (adicLisseConstantGlobalSections X Λ' Tm).obj N)
        (Y := (pbcRestrict (constantRingIso q X).hom ⋙ adicLisseConstantGlobalSections X Λ Tm ⋙
          ModuleCat.restrictScalars q.symm.toRingHom).obj N)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ by
            exact smul_congr'' (R := adicLisseConstantRing X Λ') N (op Tm)
              (constantRingIso_unit q X (op Tm) a).symm x }
      inv := ModuleCat.ofHom (Y := (adicLisseConstantGlobalSections X Λ' Tm).obj N)
        (X := (pbcRestrict (constantRingIso q X).hom ⋙ adicLisseConstantGlobalSections X Λ Tm ⋙
          ModuleCat.restrictScalars q.symm.toRingHom).obj N)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ by
            exact smul_congr'' (R := adicLisseConstantRing X Λ') N (op Tm)
              (constantRingIso_unit q X (op Tm) a) x } })
    (fun f ↦ by
      ext x
      rfl)

/-- Constant module sheaves commute with restriction along a constant ring isomorphism. -/
private def adicLisseConstantModulesTransportIso (X : Scheme.{u}) :
    adicLisseConstantModules X Λ' ≅
      ModuleCat.restrictScalars q.toRingHom ⋙ adicLisseConstantModules X Λ ⋙
        pbcRestrict (constantRingIso q X).inv :=
  let Tm : X.ProEt := ⊤_ X.ProEt
  let hT : IsTerminal Tm := terminalIsTerminal
  let adj₁ := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv q).toAdjunction
  let adjG := adicLisseConstantModulesAdjunction X Λ Tm hT
  let adj₃ := (pbcRestrictEquivalence (constantRingIso q X).symm).toAdjunction
  let adjG' := adicLisseConstantModulesAdjunction X Λ' Tm hT
  (conjugateIsoEquiv (adj₁.comp (adjG.comp adj₃)) adjG').symm
    (constantGlobalSectionsIso q X Tm).symm

/-- Constructibility is invariant under isomorphism. -/
theorem isConstructibleProEtaleCoefficientModuleSheaf_of_iso (Y : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {F G : pbcModules Y (adicLisseConstantRing Y Λ)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleCoefficientModuleSheaf Y Λ F) :
    IsConstructibleProEtaleCoefficientModuleSheaf Y Λ G := by
  obtain ⟨S, hn, hc, hS⟩ := hF
  refine ⟨S, hn, hc, fun i ↦ ?_⟩
  obtain ⟨W, hW, hloc⟩ := hS i
  refine ⟨W, hW, fun V f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨e'⟩⟩ := hloc V f hf
  exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ V).mapIso
    ((proEtaleModuleInverseImage (S.immersion i) (adicLisseConstantRing Y Λ)).mapIso e.symm) ≪≫
      e'⟩⟩

/-- Constructibility is invariant under restriction along a constant ring isomorphism. -/
theorem isConstructible_restrict_constantRingIso (Y : Scheme.{u}) [Finite Λ] [Finite Λ']
    (F : pbcModules Y (adicLisseConstantRing Y Λ))
    (hF : IsConstructibleProEtaleCoefficientModuleSheaf Y Λ F) :
    IsConstructibleProEtaleCoefficientModuleSheaf Y Λ'
      ((pbcRestrict (constantRingIso q Y).inv).obj F) := by
  obtain ⟨S, hn, hc, hS⟩ := hF
  refine ⟨S, hn, hc, fun i ↦ ?_⟩
  obtain ⟨W, hW, hloc⟩ := hS i
  refine ⟨W, hW, fun V f hf ↦ ?_⟩
  obtain ⟨M, hM, he⟩ := hloc V f hf
  let M' := (ModuleCat.restrictScalars q.symm.toRingHom).obj M
  have hM' : Finite M' := hM
  obtain ⟨e₁⟩ := (localModel_iff (S.immersion i) (constantRingIso q Y).symm V F
    ((adicLisseConstantModules Y Λ).obj M)).mp he
  let c : (pbcRestrict (constantRingIso q Y).inv).obj ((adicLisseConstantModules Y Λ).obj M) ≅
      (adicLisseConstantModules Y Λ').obj M' :=
    (pbcRestrict (constantRingIso q Y).inv).mapIso ((adicLisseConstantModules Y Λ).mapIso
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv q).counitIso.app M).symm) ≪≫
      ((adicLisseConstantModulesTransportIso q Y).app M').symm
  exact ⟨M', hM', ⟨e₁ ≪≫ (SheafOfModules.overFunctor _ V).mapIso
    ((proEtaleModuleInverseImage (S.immersion i) (adicLisseConstantRing Y Λ')).mapIso c)⟩⟩

end ConstantRing

section Profile

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal)

/-- The uniform reduction profile transports along an isomorphism of coefficient data. -/
theorem AdicCoefficientDatum.transport_uniformReductionProfile (T : Scheme.{u})
    (K : PbcCompletedDerived T d) (hK : PbcUniformReductionProfile T d K) :
    PbcUniformReductionProfile T d' ((d.transportDerived d' φ hφ T).obj K) := by
  obtain ⟨a, b, h⟩ := hK
  refine ⟨a, b, fun n ↦ ?_⟩
  obtain ⟨ha, hb, hc⟩ := h n
  let e := (d.constantReductionTransportIso d' φ hφ T n).app K
  let R := pbcRestrict (d.constantLevelIso d' φ hφ T n).inv
  let Y := (pbcConstantReduction T d n).obj K
  have : Y.IsGE a := ha
  have : Y.IsLE b := hb
  let e' : (pbcDerivedRestrict (d.constantLevelIso d' φ hφ T n).inv).obj Y ≅
      (pbcConstantReduction T d' n).obj ((d.transportDerived d' φ hφ T).obj K) := e.symm
  have : ((pbcDerivedRestrict (d.constantLevelIso d' φ hφ T n).inv).obj Y).IsGE a :=
    R.isGE_mapDerivedCategory_obj Y a
  have : ((pbcDerivedRestrict (d.constantLevelIso d' φ hφ T n).inv).obj Y).IsLE b :=
    R.isLE_mapDerivedCategory_obj Y b
  refine ⟨DerivedCategory.TStructure.t.isGE_of_iso e' a,
    DerivedCategory.TStructure.t.isLE_of_iso e' b, fun m ↦ ?_⟩
  let := d.quotientFinite n
  let := d'.quotientFinite n
  have hY : IsConstructibleProEtaleCoefficientModuleSheaf T (A ⧸ d.ideal ^ (n + 1))
      ((DerivedCategory.homologyFunctor _ m).obj Y) := hc m
  have h₁ := isConstructible_restrict_constantRingIso (d.quotientRingEquiv d' φ hφ n) T _ hY
  let i₁ : R.obj ((DerivedCategory.homologyFunctor _ m).obj Y) ≅
      (DerivedCategory.homologyFunctor _ m).obj (R.mapDerivedCategory.obj Y) :=
    (R.mapDerivedCategoryHomologyFunctorIso m).app Y
  let i₂ : (DerivedCategory.homologyFunctor _ m).obj (R.mapDerivedCategory.obj Y) ≅
      (DerivedCategory.homologyFunctor _ m).obj
        ((pbcConstantReduction T d' n).obj ((d.transportDerived d' φ hφ T).obj K)) :=
    (DerivedCategory.homologyFunctor _ m).mapIso e'
  exact isConstructibleProEtaleCoefficientModuleSheaf_of_iso T _ (i₁ ≪≫ i₂) h₁

end Profile

end AlgebraicGeometry.Scheme
