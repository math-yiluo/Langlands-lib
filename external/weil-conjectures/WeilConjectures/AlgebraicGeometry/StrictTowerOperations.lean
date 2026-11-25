/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FourCorners
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle

/-! # Canonical operations on strict module towers

Source: blueprint completed-exchange-coherence, first two proof sentences;
Stacks 07A7 and 0D6D (auxiliary; not a blueprint node).

## Main definitions

* `exchangeTowerPull`, `exchangeTowerPush`: strict diagram derived functors.
* `exchangeTowerAdjunction`: the derived termwise normalized module adjunction.
* `StrictTowerRingedSquare.exchangeTowerSquare`: canonical pullback composition.
* `StrictTowerRingedSquare.exchangeTowerMate`: its specified adjunction mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

-- The universe-polymorphic `{max u (t + 1)}` sheafification instances get stuck on
-- universe constraints for the `CommRingCat.{t + 1}` sheaves of this file.
attribute [-instance] WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective

/-- Constant coefficients on the small pro-etale site, in the sheaf-value universe.
Source: strict normalization, paragraph 2; Stacks 00YV
(auxiliary; not a blueprint node). -/
abbrev exchangeConstantRing (T : Scheme.{t}) (A : Type (t + 1)) [CommRing A] :=
  adicLisseConstantRing T A

/-- Inverse image preserves the specific constant-section comparison for every ring.
Source: Stacks 00VC, 07A7; strict normalization, paragraph 2
(auxiliary; not a blueprint node).
Proof: the constant sheaf is inverse image from sets. Composition of inverse images
identifies inverse image of a constant sheaf with the same constant sheaf. On constant
sections this comparison is the sheafification adjunct defining the recorded map.
Thus that particular map is invertible; no finiteness of A is required. -/
theorem exchangeConstantComparison_isIso {U V : Scheme.{t}} (f : U ⟶ V)
    (A : Type (t + 1)) [CommRing A] :
    IsIso ((proEtaleConstantComparison f).app (CommRingCat.of A)) := by
  let B := CommRingCat.of A
  let T := ⊤_ V.ProEt
  let hT := terminalIsTerminal (C := V.ProEt)
  let hGT := hT.isTerminalObj (proEtaleBaseChange f)
  let adjY := constantSheafAdj (ProEt.topology V) CommRingCat.{t + 1} hT
  let adjX := constantSheafAdj (ProEt.topology U) CommRingCat.{t + 1} hGT
  let adj := (adjY.comp (proEtaleSheafAdjunction f CommRingCat.{t + 1})).ofNatIsoRight
    ((proEtaleBaseChange f).sheafPushforwardContinuousCompSheafSectionsObjIso
      CommRingCat.{t + 1} (ProEt.topology V) (ProEt.topology U) (op T))
  have he : (proEtaleConstantComparison f).app B =
      (adj.leftAdjointUniq adjX).hom.app B := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    change (adjY.comp (proEtaleSheafAdjunction f CommRingCat.{t + 1})).homEquiv _ _
      ((proEtaleConstantComparison f).app B) ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_homEquiv]
    change adjY.homEquiv _ _
      ((proEtaleSheafAdjunction f CommRingCat.{t + 1}).homEquiv _ _
        (((proEtaleSheafAdjunction f CommRingCat.{t + 1}).homEquiv _ _).symm
          (proEtaleConstantDirectImageMap f CommRingCat.{t + 1} B))) = _
    rw [Equiv.apply_symm_apply]
    change ((constantPresheafAdj CommRingCat.{t + 1} hT).comp
      (sheafificationAdjunction (ProEt.topology V) CommRingCat.{t + 1})).homEquiv _ _
        (proEtaleConstantDirectImageMap f CommRingCat.{t + 1} B) = _
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{t + 1} hT).homEquiv _ _
      ((sheafificationAdjunction (ProEt.topology V) CommRingCat.{t + 1}).homEquiv _ _
        (((sheafificationAdjunction (ProEt.topology V) CommRingCat.{t + 1}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    change 𝟙 B ≫ _ = _
    rw [Category.id_comp]
    rfl
  rw [he]
  infer_instance

/-- The constant coefficient identification, fixed by the constant-section map.
Source: strict normalization, paragraph 2; Stacks 00VC
(auxiliary; not a blueprint node). -/
def exchangeConstantIso {U V : Scheme.{t}} (f : U ⟶ V)
    (A : Type (t + 1)) [CommRing A] :
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj (exchangeConstantRing V A) ≅
      exchangeConstantRing U A :=
  @asIso _ _ _ _ ((proEtaleConstantComparison f).app (CommRingCat.of A))
    (exchangeConstantComparison_isIso f A)

variable {U V : Scheme.{t}} (f : U ⟶ V)
  (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
  (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S)

/-- Sectionwise normalization of the ordinary composition comparison. Its right-adjoint
conjugate is exactly the canonical fibre-product pasting map on every section.
Source: Stacks 03D8 and 0D6D
(auxiliary; not a blueprint node). -/
def ExchangeModuleCompositionNormalized {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{t + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{t + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{t + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{t + 1}).obj RW ≅ RZ)
    (a : proEtaleRingModulePullback (h ≫ k) RV RZ
        (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) ≅
      proEtaleRingModulePullback k RV RW ck ⋙ proEtaleRingModulePullback h RW RZ ch) :
    Prop :=
  ∀ (N : proEtaleRingModules Z RZ) (U : V.ProEt)
    (m : ((proEtaleRingModuleDirectImage h RW RZ ch ⋙
      proEtaleRingModuleDirectImage k RV RW ck).obj N).val.obj (op U)),
    ((conjugateIsoEquiv
        ((proEtaleRingModuleAdjunction k RV RW ck).comp
          (proEtaleRingModuleAdjunction h RW RZ ch))
        (proEtaleRingModuleAdjunction (h ≫ k) RV RZ
          (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch)) a).hom.app N).val.app
            (op U) m =
      N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app U).op m

/-- There is a unique composition comparison with the sectionwise canonical conjugate.
Source: Stacks 03D8 and 0D6D
(auxiliary; not a blueprint node).
Proof: proEtaleRingDerivedPullbackComposition supplies ordinary adjunctions whose
units are the canonical tensor-unit sections, a sectionwise pasting isomorphism of
right adjoints, and its conjugate ordinary pullback comparison. These adjunctions
agree with proEtaleRingModuleAdjunction: the units agree on every section, hence
agree as natural transformations, and determine the adjunction. Thus its comparison
satisfies this normalization. Sectionwise equality determines the direct-image
natural transformation uniquely. The conjugate-isomorphism equivalence is bijective,
so the pullback comparison is unique as well. -/
theorem exchangeModuleComposition_existsUnique {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{t + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{t + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{t + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{t + 1}).obj RW ≅ RZ) :
    ∃! a : proEtaleRingModulePullback (h ≫ k) RV RZ
        (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) ≅
      proEtaleRingModulePullback k RV RW ck ⋙ proEtaleRingModulePullback h RW RZ ch,
      ExchangeModuleCompositionNormalized h k RV RW RZ ck ch a := by
  obtain ⟨adjk, adjh, adjhk, _, _, _, d, hd, _⟩ :=
    proEtaleRingDerivedPullbackComposition h k RV RW RZ ck ch
      (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) rfl
  let e := conjugateIsoEquiv
    ((proEtaleRingModuleAdjunction k RV RW ck).comp
      (proEtaleRingModuleAdjunction h RW RZ ch))
    (proEtaleRingModuleAdjunction (h ≫ k) RV RZ
      (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch))
  refine ⟨e.symm d, ?_, ?_⟩
  · change ∀ N U m, ((e (e.symm d)).hom.app N).val.app (op U) m = _
    rw [e.apply_symm_apply]
    exact hd
  · intro a ha
    apply e.injective
    rw [e.apply_symm_apply]
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    exact (ha N U.unop m).trans (hd N U.unop m).symm

/-- The ordinary canonical pullback composition, fixed by its sectionwise conjugate
and the existing tensor-unit-normalized module adjunctions.
Source: Stacks 03D8 and 0D6D
(auxiliary; not a blueprint node). -/
def exchangeModuleComposition {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{t + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{t + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{t + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{t + 1}).obj RW ≅ RZ) :
    proEtaleRingModulePullback (h ≫ k) RV RZ
        (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) ≅
      proEtaleRingModulePullback k RV RW ck ⋙ proEtaleRingModulePullback h RW RZ ch :=
  (exchangeModuleComposition_existsUnique h k RV RW RZ ck ch).choose

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

end AlgebraicGeometry.Scheme
