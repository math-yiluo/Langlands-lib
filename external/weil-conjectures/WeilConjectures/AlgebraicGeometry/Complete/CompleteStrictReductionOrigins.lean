/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.CoefficientSheafificationSquare.CoefficientSheafificationScalarSquare

/-!
# Etale origins of restricted strict reduction towers

Compatible bounded-below etale origins of a completed object give finite constant-coefficient
etale origins at every level of its strict reduction tower, after restriction to constant
coefficients.

Source: Weil conjectures blueprint, node proposition-composition-base-change-rf-shriek--4, proof
step 8 (blueprint: proposition-composition-base-change-rf-shriek--4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
/-- The constant-coefficient scalar map followed by the n-th projection is the constant
quotient map followed by the canonical level comparison.
Source: strict normalization, proof step 5; Stacks 099M (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
theorem cbcExchangeScalar_projection (V : Scheme.{t}) (n : ℕ) :
    exchangeScalar d V ≫ completedReductionProjection V d n =
      (constantSheaf (ProEt.topology V) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
        (pbcLevelConstantComparison V d n).hom := by
  dsimp only [exchangeScalar, completedReductionProjection, pbcCompletedComparison]
  rw [Category.assoc]
  erw [HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc]
  erw [(adicDatumScalar_exists V
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite }).exists.choose_spec n]
  rfl

/-- The level comparison sends a constant section to the constant component function.
Source: blueprint order 1250 (blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem cbcLevelComparison_toSheafify (V : Scheme.{t}) (n : ℕ) :
    toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) ≫
      (pbcLevelConstantComparison V d n).hom.hom =
    AdicCoefficients.constants V (A ⧸ d.ideal ^ (n + 1)) ≫
      toSheafify (ProEt.topology V) (pbcQuotientPresheaf V d n) := by
  ext U b
  exact (pbcLevelConstantComparison_exists V d n).exists.choose_spec U b

/-- The continuous-function presentation of constants is the level comparison on constants.
Source: blueprint order 1300 (blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem cbcPbcFunctionScalars_eq (V : Scheme.{t}) (n : ℕ) :
    pbcFunctionScalars V d n =
      Functor.whiskerRight (toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))) (forget₂ CommRingCat RingCat) ≫
        ((adicLisseForget V).map (pbcLevelConstantComparison V d n).hom).hom := by
  have hη := (AdicCoefficients.finiteRingComparison_exists V
    (ProEtale.PbcQuotient d n)).choose_spec.1.2
  rw [show ((adicLisseForget V).map (pbcLevelConstantComparison V d n).hom).hom =
    Functor.whiskerRight (pbcLevelConstantComparison V d n).hom.hom
      (forget₂ CommRingCat RingCat) from rfl]
  rw [← Functor.whiskerRight_comp, cbcLevelComparison_toSheafify, Functor.whiskerRight_comp]
  unfold pbcFunctionScalars
  change _ = _ ≫ Functor.whiskerRight (toSheafify (ProEt.topology V)
    (AdicCoefficients.functionPresheaf V (ProEtale.PbcQuotient d n))) _
  rw [← cancel_mono (AdicCoefficients.finiteRingComparison V (ProEtale.PbcQuotient d n)).hom.hom]
  simp only [Category.assoc]
  rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id]
  erw [hη]
  rfl

/-- Ring maps out of the constant coefficient ring are determined on constant sections.
Source: Stacks 00W1 (blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem cbcConstRing_hom_ext (V : Scheme.{t}) {S : Sheaf (ProEt.topology V) RingCat.{t + 1}}
    (f g : (adicLisseForget V).obj (exchangeConstantRing V A) ⟶ S)
    (h : Functor.whiskerRight (toSheafify (ProEt.topology V)
        ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of A))) (forget₂ CommRingCat RingCat) ≫
          f.hom =
      Functor.whiskerRight (toSheafify (ProEt.topology V)
        ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of A))) (forget₂ CommRingCat RingCat) ≫
          g.hom) : f = g := by
  have hf := sheafComposeIso_hom_fac (ProEt.topology V) (forget₂ CommRingCat.{t + 1} RingCat)
    ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of A))
  apply Sheaf.hom_ext
  rw [← cancel_epi (sheafifyComposeIso (ProEt.topology V) (forget₂ CommRingCat.{t + 1} RingCat)
    ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of A))).hom]
  apply sheafify_hom_ext _ _ _ S.property
  simpa only [← Category.assoc, hf] using h

/-- The finite scalar map on constant sections. Source: Stacks 03DA
(blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem cbcFiniteScalarMap_unit (X : Scheme.{t}) (Λ : Type (t + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : A →+* Λ) :
    Functor.whiskerRight
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}) ≫
      (ProEtale.StrictTower.finiteScalarMap A X Λ φ).hom =
    (Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom φ) ≫
      ProEtale.finiteCoefficientScalarMap X Λ := by
  change _ ≫ ((constantCommuteCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).hom.app (CommRingCat.of A)).hom ≫
    sheafifyMap (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom φ)) ≫
    (((sheafificationAdjunction (ProEt.topology X) RingCat.{t + 1}).homEquiv
      _ _).symm (ProEtale.finiteCoefficientScalarMap X Λ)).hom = _
  rw [constantCommuteCompose_hom_app_hom]
  simp only [← Category.assoc, sheafComposeIso_inv_fac]
  have hc : (Functor.constComp X.ProEtᵒᵖ (CommRingCat.of A)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).hom = 𝟙 _ := rfl
  rw [hc, sheafifyMap_id, Category.comp_id, ← toSheafify_naturality, Category.assoc]
  congr 1
  exact Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology X) RingCat.{t + 1}).homEquiv _ _)
    (ProEtale.finiteCoefficientScalarMap X Λ)

/-- The finite constant-coefficient scalar map, composed with the finite ring comparison,
is the constant-coefficient scalar map followed by the n-th projection.
Source: Stacks 03DA, 099M (blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem cbcFiniteScalarMap_comparison (V : Scheme.{t}) (n : ℕ) :
    ProEtale.StrictTower.finiteScalarMap A V (ProEtale.PbcQuotient d n)
        (Ideal.Quotient.mk (d.ideal ^ (n + 1))) ≫
      (AdicCoefficients.finiteRingComparison V (ProEtale.PbcQuotient d n)).inv =
    (adicLisseForget V).map (exchangeScalar d V ≫ completedReductionProjection V d n) := by
  apply cbcConstRing_hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc]
  erw [cbcFiniteScalarMap_unit]
  have h1 : ProEtale.finiteCoefficientScalarMap V (ProEtale.PbcQuotient d n) ≫
      (AdicCoefficients.finiteRingComparison V (ProEtale.PbcQuotient d n)).inv.hom =
      pbcFunctionScalars V d n := rfl
  erw [Category.assoc, h1, cbcPbcFunctionScalars_eq, cbcExchangeScalar_projection]
  change _ = Functor.whiskerRight (toSheafify _ _) _ ≫
    Functor.whiskerRight (sheafifyMap _ _ ≫ _) _
  have h2 : toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫
      sheafifyMap (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))) =
      (Functor.const V.ProEtᵒᵖ).map (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
        toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj
          (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) :=
    (toSheafify_naturality _ _).symm
  have h3 := congrArg (fun k ↦
    Functor.whiskerRight k (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}) ≫
    Functor.whiskerRight (pbcLevelConstantComparison V d n).hom.hom
      (forget₂ CommRingCat RingCat)) h2
  simp only [Functor.whiskerRight_comp, Category.assoc] at h3 ⊢
  exact h3.symm

/-- Restriction of module scalars along a composite of ring sheaf maps.
Source: Stacks 03DA (blueprint: proposition-composition-base-change-rf-shriek--4). -/
def cbcSheafRestrictScalarsComp {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R R' R'' : Sheaf J RingCat.{t + 1}} (α : R ⟶ R') (β : R' ⟶ R'') :
    SheafOfModules.restrictScalars.{t + 1} (α ≫ β) ≅
      SheafOfModules.restrictScalars.{t + 1} β ⋙ SheafOfModules.restrictScalars.{t + 1} α :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun X ↦ ModuleCat.restrictScalarsComp'App _ _ _ rfl _)
      (by intros; ext; rfl))) (by intros; ext; rfl)

/-- Restriction of module presheaf scalars along the identity of a constant ring.
Source: Stacks 03DA (blueprint: proposition-composition-base-change-rf-shriek--4). -/
def cbcConstRestrictScalarsId {C : Type*} [Category C] (Λ : Type (t + 1)) [CommRing Λ] :
    PresheafOfModules.restrictScalars.{t + 1}
        ((Functor.const Cᵒᵖ).map (RingCat.ofHom (RingHom.id Λ))) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M ↦ PresheafOfModules.isoMk
    (fun X ↦ ModuleCat.restrictScalarsId'App _ rfl _) (by intros; ext; rfl))
    (by intros; ext; rfl)

attribute [local instance] ProEtale.StrictTower.finiteRestriction_finiteLimits
  ProEtale.StrictTower.finiteRestriction_finiteColimits

/-- Constant-coefficient restriction of the completed coefficient ring is exact. -/
instance exchangeScalarRestrict_finiteLimits (V : Scheme.{t}) :
    PreservesFiniteLimits (proEtaleRingRestrictScalars (exchangeScalar d V)) :=
  (proEtaleRingRestrictScalars_properties (exchangeScalar d V)).1

/-- Constant-coefficient restriction of the completed coefficient ring is exact. -/
instance exchangeScalarRestrict_finiteColimits (V : Scheme.{t}) :
    PreservesFiniteColimits (proEtaleRingRestrictScalars (exchangeScalar d V)) :=
  (proEtaleRingRestrictScalars_properties (exchangeScalar d V)).2.1

/-- The two coefficient presentations of a finite-level sheaf, restricted to constant
coefficients, agree: realization along constant sections followed by restriction along
A → A/I^(n+1), and realization along continuous functions followed by restriction along the
n-th projection and the constant-coefficient scalar map.
Source: blueprint def-cbc-finite-constant-coefficient-transport
(blueprint: proposition-composition-base-change-rf-shriek--4).
Proof sketch: `rawIso` for the finite ring comparison identifies the two realizations up to
restriction along that comparison; the composite ring maps out of the constant ring agree
on constant sections, hence agree. -/
theorem cbcFiniteRealizationRestrictIso (V : Scheme.{t}) (n : ℕ) :
    Nonempty (ProEtale.finiteCoefficientRealization V (ProEtale.PbcQuotient d n) ⋙
        ProEtale.StrictTower.finiteRestriction A V (ProEtale.PbcQuotient d n)
          (Ideal.Quotient.mk _) ≅
      pbcFunctionRealization V d n ⋙ reductionRestrict V (completedReductionProjection V d n) ⋙
        proEtaleRingRestrictScalars (exchangeScalar d V)) := by
  let J := ProEt.topology V
  let Λ := ProEtale.PbcQuotient d n
  let α := ProEtale.finiteCoefficientScalarMap V Λ
  let β := pbcFunctionScalars V d n
  let a := (AdicCoefficients.finiteRingComparison V Λ).inv
  have ha : (Functor.const V.ProEtᵒᵖ).map (RingCat.ofHom (RingHom.id Λ)) ≫ β = α ≫ a.hom :=
    Category.id_comp _
  let P := sheafToPresheaf J (ModuleCat.{t + 1} Λ) ⋙
    ProEtale.finiteCoefficientModulePresheaf V.ProEt Λ
  let raw := CoefficientSheafificationSquare.rawIso J (RingHom.id Λ) a α β ha
  let i₁ : ProEtale.finiteCoefficientRealization V Λ ≅
      pbcFunctionRealization V d n ⋙ SheafOfModules.restrictScalars.{t + 1} a :=
    Functor.isoWhiskerLeft P ((Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (cbcConstRestrictScalarsId Λ).symm _ ≪≫ raw)
  let f := ProEtale.StrictTower.finiteScalarMap A V Λ (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let i₂ := (cbcSheafRestrictScalarsComp f a).symm
  let i₃ := eqToIso (congrArg (fun z ↦ SheafOfModules.restrictScalars.{t + 1} z)
    ((cbcFiniteScalarMap_comparison d V n).trans (Functor.map_comp _ _ _)))
  let i₄ := cbcSheafRestrictScalarsComp ((adicLisseForget V).map (exchangeScalar d V))
    ((adicLisseForget V).map (completedReductionProjection V d n))
  exact ⟨Functor.isoWhiskerRight i₁ _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (i₂ ≪≫ i₃ ≪≫ i₄)⟩

/-- The n-th level of the restricted strict reduction tower of K is the constant-coefficient
restriction of the realized n-th witnessed level, given an identification of that realized
level with the n-th completed reduction of K.
Source: blueprint def-weil-pbc-bounded-constructible-complete and
def-cbc-finite-constant-coefficient-transport (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
theorem cbcStrictReductionLevel_originIso (V : Scheme.{t}) (K : d.derived V) (n : ℕ)
    (X : ProEtale.PbcWitnessAmbient V d n)
    (e : (pbcDerivedFunctionRealization V d n).obj X ≅ (pbcCompletedReduction V d n).obj K) :
    Nonempty ((ProEtale.StrictTower.finiteRestriction A V (ProEtale.PbcQuotient d n)
        (Ideal.Quotient.mk _)).mapDerivedCategory.obj
          ((ProEtale.finiteCoefficientRealization V
            (ProEtale.PbcQuotient d n)).mapDerivedCategory.obj X) ≅
      (ProEtale.StrictTower.ev A V n).obj
        ((exchangeTowerRes d V).obj ((completedReductionTower V d).obj K))) := by
  obtain ⟨b⟩ := cbcFiniteRealizationRestrictIso d V n
  let real := ProEtale.finiteCoefficientRealization V (ProEtale.PbcQuotient d n)
  let RF := ProEtale.StrictTower.finiteRestriction A V (ProEtale.PbcQuotient d n)
    (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let pbcR := pbcFunctionRealization V d n
  let resN := reductionRestrict V (completedReductionProjection V d n)
  let resA := proEtaleRingRestrictScalars (exchangeScalar d V)
  let ev := (CategoryTheory.evaluation ℕᵒᵖ
    (proEtaleRingModules V (d.completedRing V))).obj (op n)
  let i₁ := (Functor.mapDerivedCategoryCompIso real RF).app X
  let i₂ := (Functor.mapDerivedCategoryNatIso b).app X
  let i₃ := (Functor.mapDerivedCategoryCompIso pbcR (resN ⋙ resA)).symm.app X
  let i₄ := (resN ⋙ resA).mapDerivedCategory.mapIso e
  let i₅ := (Functor.mapDerivedCategoryCompIso resN resA).symm.app
    ((pbcCompletedReduction V d n).obj K)
  let i₆ := resA.mapDerivedCategory.mapIso
    ((asIso (completedReductionEvaluation V d n)).symm.app K)
  let i₇ := (Functor.mapDerivedCategoryCompIso ev resA).app
    ((completedReductionTower V d).obj K)
  let i₈ := (Functor.mapDerivedCategoryCompIso (exchangeTowerModuleRes d V)
    ((CategoryTheory.evaluation ℕᵒᵖ (ProEtale.StrictTower.Modules A V)).obj (op n))).symm.app
      ((completedReductionTower V d).obj K)
  exact ⟨i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅ ≪≫ i₆ ≪≫ i₇ ≪≫ i₈⟩


/-- Compatible etale origins of a completed object give finite constant-coefficient etale
origins of every level of its restricted strict reduction tower.
Source: blueprint step 8 (blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem cbcStrictReductionLevel_scalarEtaleOrigin (V : Scheme.{t}) (K : d.derived V)
    (origins : PbcHasCompatibleEtaleOrigins V d K) (n : ℕ) :
    Nonempty (ProEtale.StrictTower.ScalarEtaleOrigin A V
      ((ProEtale.StrictTower.ev A V n).obj
        ((exchangeTowerRes d V).obj ((completedReductionTower V d).obj K)))) := by
  obtain ⟨P, e, -⟩ := origins
  obtain ⟨iso⟩ := cbcStrictReductionLevel_originIso d V K n (P.K n) (e n)
  exact ⟨{ Λ := ProEtale.PbcQuotient d n
           φ := Ideal.Quotient.mk _
           F := ⟨_, P.boundedBelow n⟩
           origin := P.origin n
           iso := iso }⟩

end AlgebraicGeometry.Scheme
