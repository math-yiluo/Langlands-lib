/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedSupportTriangle
public import WeilConjectures.CategoryTheory.Sites.SmoothPurity.SupportLongExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedExteriorProduct
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientDerivedOpenMate
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientOpenMateQuotient
import all WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedExteriorProduct
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedProductLocalization
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientTensorQuotientSquare
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientOpenTensor
import all WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedProductNaturality
import all WeilConjectures.AlgebraicGeometry.Support.SupportQuotientPairPullback
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction

/-!
# Comparison of ordinary supported sections between the two sites

Source: Stacks Project, Tags 099W, 099V, 09B1 and 09XP, with the supported
refinement of blueprint `lem-pur-support-site-comparison`
(blueprint: lem-pur-support-site-comparison).

## Main definitions and statements

* `ProEtale.supportComparison`: the natural bounded-below comparison map.
* `ProEtale.supportComparison_isIso`: invertibility under the node's hypotheses.
* `ProEtale.supportComparison_forget`, `ProEtale.fullSupportForget_isIso`, and
  `ProEtale.supportComparison_open`: forgetting, full-support normalization, and restriction.
* `ProEtale.supportExteriorCoefficientIso`: the specified tensor/pullback comparison theta.
* `ProEtale.supportComparison_exterior`: equality of the supported exterior-product maps.
-/

@[expose] public section

set_option autoImplicit false

universe u u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A]
  {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]

/-- The etale support kernel used by the canonical comparison unit.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable abbrev etaleSupportKernel :=
  Sheaf.supportedSectionsFunctor T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (Etale.supportRestrictionArrow i)

section SupportDerivedNormalization

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  {L : C ⥤ D} {G : C ⥤ E} {H : D ⥤ E}
  [L.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

variable (R : D ⥤ C) [R.Additive] [R.PreservesInjectiveObjects] (adj : L ⊣ R)

variable [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]

end SupportDerivedNormalization

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem supportEvaluation_hom (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} A)
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)).hom.app M =
      M.ΓRes (op (Scheme.Etale.mk (𝟙 X))) := by
  let adj := constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let adj' := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
  have hc := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app adj adj' M
  apply (adj'.homEquiv _ M).symm.injective
  change (adj'.homEquiv _ M).symm ((adj.rightAdjointUniq adj').hom.app M) = _
  rw [hc]
  apply (adj'.homEquiv _ M).injective
  rw [Equiv.apply_symm_apply]
  change (CategoryTheory.constantPresheafAdj (ModuleCat.{u + 1} A)
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)).homEquiv _ _
    ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ _
      (adj.counit.app M)) = _
  rw [Adjunction.homEquiv_unit]
  change (𝟙 _) ≫ ((sheafificationAdjunction X.smallEtaleTopology
      (ModuleCat.{u + 1} A)).homEquiv _ _ (adj.counit.app M)).app
        (Opposite.op (Scheme.Etale.mk (𝟙 X))) =
    ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ _
      ((adj.homEquiv _ M).symm (𝟙 _))).app (Opposite.op (Scheme.Etale.mk (𝟙 X)))
  rw [Category.id_comp, adj.homEquiv_symm_id]
  rfl

set_option backward.isDefEq.respectTransparency.types true in
/-- The canonical identification of the global-section kernel with the restriction
kernel used by the support long exact sequence.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: the terminal-evaluation isomorphism identifies global restriction with
restriction from the terminal object. It induces an isomorphism of kernels.
The kernel inclusion determines its forward map and hence the isomorphism uniquely. -/
theorem supportKernelEvaluationIso_existsUnique :
    ∃! e : Etale.supportedEtaleSections A T i.openComplement ≅ etaleSupportKernel A i,
      e.hom ≫ Sheaf.supportedSectionsInclusion T.smallEtaleTopology
        (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) =
      Etale.supportedEtaleSectionsι A T i.openComplement ≫
        (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).hom := by
  let r := Sheaf.natTransΓRes T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (op (Scheme.Etale.mk i.openComplement.ι))
  let e := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
  have he (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      r.app F ≫ 𝟙 _ = e.hom.app F ≫ F.obj.map (Etale.supportRestrictionArrow i).op := by
    change F.ΓRes (op (Scheme.Etale.mk i.openComplement.ι)) ≫ 𝟙 _ = _
    rw [supportEvaluation_hom]
    simpa only [Category.comp_id] using
      (Sheaf.ΓRes_map F (Etale.supportRestrictionArrow i).op).symm
  let b (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      (Etale.supportedEtaleSections A T i.openComplement).obj F ≅
        (etaleSupportKernel A i).obj F :=
    PreservesKernel.iso ((evaluation _ (ModuleCat.{u + 1} A)).obj F) r ≪≫
      kernel.mapIso (r.app F) (F.obj.map (Etale.supportRestrictionArrow i).op)
        (e.app F) (Iso.refl _) (he F)
  have hb (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      (b F).hom ≫ kernel.ι (F.obj.map (Etale.supportRestrictionArrow i).op) =
        (Etale.supportedEtaleSectionsι A T i.openComplement).app F ≫ e.hom.app F := by
    change ((PreservesKernel.iso ((evaluation _ (ModuleCat.{u + 1} A)).obj F) r).hom ≫
      (kernel.mapIso (r.app F) (F.obj.map (Etale.supportRestrictionArrow i).op)
        (e.app F) (Iso.refl _) (he F)).hom) ≫
          kernel.ι (F.obj.map (Etale.supportRestrictionArrow i).op) = _
    rw [Category.assoc, kernel.mapIso_hom, kernel.lift_ι]
    rw [← Category.assoc, PreservesKernel.iso_hom]
    erw [kernelComparison_comp_ι]
    rfl
  let n : Etale.supportedEtaleSections A T i.openComplement ≅ etaleSupportKernel A i :=
    NatIso.ofComponents b (by
      intro F G f
      apply (cancel_mono (kernel.ι (G.obj.map (Etale.supportRestrictionArrow i).op))).mp
      change ((Etale.supportedEtaleSections A T i.openComplement).map f ≫
          (b G).hom) ≫ kernel.ι (G.obj.map (Etale.supportRestrictionArrow i).op) =
        ((b F).hom ≫ (etaleSupportKernel A i).map f) ≫
          kernel.ι (G.obj.map (Etale.supportRestrictionArrow i).op)
      rw [Category.assoc, hb]
      change (kernel r).map f ≫ (kernel.ι r).app G ≫ e.hom.app G =
        ((b F).hom ≫ kernel.map _ _ (f.hom.app (op (Scheme.Etale.mk (𝟙 T))))
          (f.hom.app (op (Scheme.Etale.mk i.openComplement.ι)))
          (f.hom.naturality (Etale.supportRestrictionArrow i).op)) ≫
            kernel.ι (G.obj.map (Etale.supportRestrictionArrow i).op)
      rw [Category.assoc, kernel.lift_ι]
      rw [← Category.assoc (b F).hom, hb]
      calc
        (kernel r).map f ≫ (kernel.ι r).app G ≫ e.hom.app G =
            (kernel.ι r).app F ≫ (Sheaf.Γ T.smallEtaleTopology
              (ModuleCat.{u + 1} A)).map f ≫ e.hom.app G := by
          rw [← Category.assoc, (kernel.ι r).naturality f, Category.assoc]
        _ = ((kernel.ι r).app F ≫ e.hom.app F) ≫
            f.hom.app (op (Scheme.Etale.mk (𝟙 T))) := by
          rw [e.hom.naturality f, Category.assoc]
          rfl)
  refine ⟨n, ?_, ?_⟩
  · apply NatTrans.ext
    funext F
    exact hb F
  · intro n' hn'
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply (cancel_mono (kernel.ι (F.obj.map (Etale.supportRestrictionArrow i).op))).mp
    exact (NatTrans.congr_app hn' F).trans (hb F).symm

/-- The uniquely kernel-normalized terminal-evaluation transport.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportKernelEvaluationIso :=
  Classical.choose (supportKernelEvaluationIso_existsUnique A i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
/-- Derive the recorded coefficient pullback comparison before specializing coefficients.
Source: blueprint comparison-pullback clause (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportDerivedCoefficientPullbackIso
    (D : Type v₁) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStar D f).mapDerivedCategory ⋙
        (comparisonUpperStar D X).mapDerivedCategory ≅
      (comparisonUpperStar D Y).mapDerivedCategory ⋙ (upperStar D f).mapDerivedCategory :=
  let e : Etale.upperStar D f ⋙ comparisonUpperStar D X ≅
      comparisonUpperStar D Y ⋙ upperStar D f :=
    supportSiteComparisonCoefficientPullbackIso D f
  Functor.mapDerivedCategoryCompIso (Etale.upperStar D f)
    (comparisonUpperStar D X) ≪≫
  Functor.mapDerivedCategoryNatIso e ≪≫
  (Functor.mapDerivedCategoryCompIso (comparisonUpperStar D Y) (upperStar D f)).symm

open MonoidalCategory

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
private noncomputable def coefficientComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i] [IsLocallyNoetherian T] :
    Etale.supportedCoefficients A i ⋙ comparisonUpperStar (ModuleCat.{u + 1} A) T ≅
      supportedCoefficients A i := by
  let ae : Etale.supportedCoefficients A i ⊣ etaleSupportKernel A i :=
    (Etale.supportedCoefficientAdjunction A i).ofNatIsoRight (supportKernelEvaluationIso A i)
  let a : Etale.supportedCoefficients A i ⋙ comparisonUpperStar (ModuleCat.{u + 1} A) T ⊣
      supportSections i A := ae.comp (comparisonAdjunction (ModuleCat.{u + 1} A) T)
  exact a.leftAdjointUniq (supportedCoefficientAdjunction A i)

end

section GenericOpenComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
end GenericOpenComparison

section CoefficientNormalization
open Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true

namespace CachedConstantCoherence
section
attribute [-instance] supportedSheaf_monoidalPreadditive
  supportedSheaf_isMonoidalGeneric supportedSheaf_monoidalPreadditiveGeneric
private noncomputable def constantComparison (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    (T : Scheme.{u}) :
    constantSheaf T.smallEtaleTopology D ⋙
      comparisonUpperStar D T ≅
    constantSheaf (Scheme.ProEt.topology T) D :=
  (((constantSheafΓAdj T.smallEtaleTopology D).comp
    (comparisonAdjunction D T)).ofNatIsoRight
      (comparisonLowerStarCompGlobalSectionsIso D T)).leftAdjointUniq
    (constantSheafΓAdj (Scheme.ProEt.topology T) D)

private noncomputable def constantComparisonTerminal (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    (T : Scheme.{u}) :
    constantSheaf T.smallEtaleTopology D ⋙
      comparisonUpperStar D T ≅
    constantSheaf (Scheme.ProEt.topology T) D :=
  ((constantSheafAdj T.smallEtaleTopology D
    (Scheme.Etale.isTerminalMkId T)).comp
    (comparisonAdjunction D T)).leftAdjointUniq
    (constantSheafAdj (Scheme.ProEt.topology T) D
      (Scheme.ProEt.isTerminalMkId T))

private lemma constantComparisonTerminal_eq_inverse (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    (T : Scheme.{u}) (M : D) :
    (constantComparisonTerminal D T).hom.app M =
      Scheme.constantInverse T.smallEtaleTopology (Scheme.ProEt.topology T) (Scheme.toProEt T)
        (comparisonAdjunction D T) M := by
  let ae := constantSheafAdj T.smallEtaleTopology D (Scheme.Etale.isTerminalMkId T)
  let ap := constantSheafAdj (Scheme.ProEt.topology T) D (Scheme.ProEt.isTerminalMkId T)
  let p := comparisonAdjunction D T
  apply (p.homEquiv _ _).injective
  unfold Scheme.constantInverse
  conv_rhs => erw [Equiv.apply_symm_apply]
  apply (ae.homEquiv _ _).injective
  have hc : (ae.comp p).homEquiv _ _ ((constantComparisonTerminal D T).hom.app M) =
      ae.homEquiv _ _ (p.homEquiv _ _ ((constantComparisonTerminal D T).hom.app M)) := by
    rw [Adjunction.comp_homEquiv]
    rfl
  rw [← hc]
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [Adjunction.homEquiv_apply, ae, constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, sheafificationAdjunction_unit_app, Category.id_comp]
  change (toSheafify (Scheme.ProEt.topology T)
      ((Functor.const (Scheme.ProEt T)ᵒᵖ).obj M)).app
        (op ((Scheme.toProEt T).obj (Scheme.Etale.mk (𝟙 T)))) =
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj M)).app
      (op (Scheme.Etale.mk (𝟙 T))) ≫
        (Scheme.constantDirect T.smallEtaleTopology (Scheme.ProEt.topology T)
          (Scheme.toProEt T) M).hom.app (op (Scheme.Etale.mk (𝟙 T)))
  exact (Scheme.constantDirect_unit T.smallEtaleTopology (Scheme.ProEt.topology T)
    (Scheme.toProEt T) M (op (Scheme.Etale.mk (𝟙 T)))).symm

private lemma transportedHom
    {B C D : Type*} [Category B] [Category C] [Category D]
    {L : B ⥤ C} {R : C ⥤ B} {P : C ⥤ D} {Q : D ⥤ C} {S : D ⥤ B}
    (a : L ⊣ R) (p : P ⊣ Q) (d : Q ⋙ R ≅ S)
    (M : B) (N : D) (t : L.obj M ⟶ Q.obj N) :
    ((a.comp p).ofNatIsoRight d).homEquiv M N ((p.homEquiv _ _).symm t) =
      a.homEquiv _ _ t ≫ d.hom.app N := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (p.homEquiv _ _ ((p.homEquiv _ _).symm t)) ≫ d.hom.app N = _
  rw [Equiv.apply_symm_apply]

private lemma constantComparison_eq_terminal (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    (T : Scheme.{u}) : constantComparison D T = constantComparisonTerminal D T := by
  let ae := constantSheafΓAdj T.smallEtaleTopology D
  let ap := constantSheafΓAdj (Scheme.ProEt.topology T) D
  let aet := constantSheafAdj T.smallEtaleTopology D (Scheme.Etale.isTerminalMkId T)
  let apt := constantSheafAdj (Scheme.ProEt.topology T) D (Scheme.ProEt.isTerminalMkId T)
  let ac := (ae.comp (comparisonAdjunction D T)).ofNatIsoRight
    (comparisonLowerStarCompGlobalSectionsIso D T)
  let act := aet.comp (comparisonAdjunction D T)
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (act.homEquiv _ _).injective
  have hn := Adjunction.homEquiv_leftAdjointUniq_hom_app ac ap M
  change ac.homEquiv _ _ ((constantComparison D T).hom.app M) = ap.unit.app M at hn
  have hn' := Adjunction.homEquiv_leftAdjointUniq_hom_app act apt M
  change act.homEquiv _ _ ((constantComparisonTerminal D T).hom.app M) = apt.unit.app M at hn'
  rw [hn']
  have he := ae.unit_rightAdjointUniq_hom_app aet M
  have hp := ap.unit_rightAdjointUniq_hom_app apt M
  rw [← hp, ← hn]
  have hac : ac.unit.app M =
      (ae.comp (comparisonAdjunction D T)).unit.app M ≫
        (comparisonLowerStarCompGlobalSectionsIso D T).hom.app _ := rfl
  have hact : act.unit.app M = (aet.comp (comparisonAdjunction D T)).unit.app M := by
    simp [act]
  simp only [Adjunction.homEquiv_apply, Category.assoc]
  change act.unit.app M ≫ _ = ac.unit.app M ≫ _ ≫ _
  rw [hac, hact, Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  rw [← he]
  let e := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology D
    (Scheme.Etale.isTerminalMkId T)
  let ep := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology T) D
    (Scheme.ProEt.isTerminalMkId T)
  let t := (constantComparison D T).hom.app M
  let η := (comparisonAdjunction D T).unit.app
    ((constantSheaf T.smallEtaleTopology D).obj M)
  simp only [Category.assoc]
  change ae.unit.app M ≫ e.hom.app _ ≫
      ((sheafSections T.smallEtaleTopology D).obj (op (Scheme.Etale.mk (𝟙 T)))).map η ≫
      ((sheafSections T.smallEtaleTopology D).obj (op (Scheme.Etale.mk (𝟙 T)))).map
        ((comparisonLowerStar D T).map t) =
    ae.unit.app M ≫ (Sheaf.Γ T.smallEtaleTopology D).map η ≫
      (comparisonLowerStarCompGlobalSectionsIso D T).hom.app _ ≫
      (Sheaf.Γ (Scheme.ProEt.topology T) D).map t ≫ ep.hom.app _
  have hd : (comparisonLowerStarCompGlobalSectionsIso D T).hom =
      Functor.whiskerLeft (comparisonLowerStar D T) e.hom ≫ ep.inv := by
    simp only [comparisonLowerStarCompGlobalSectionsIso, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Iso.refl_hom, Iso.symm_hom, Category.id_comp]
    have hterm : Scheme.Etale.isTerminalMkId T =
        MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T := Subsingleton.elim _ _
    simp only [e, ep, hterm]
  have hdm := congrArg (fun α ↦ α.app
    ((comparisonUpperStar D T).obj ((constantSheaf T.smallEtaleTopology D).obj M))) hd
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hdm
  rw [hdm]
  simp only [Category.assoc]
  rw [← reassoc_of% ep.inv.naturality t, Iso.inv_hom_id_app, Category.comp_id]
  have ht :
      ((sheafSections T.smallEtaleTopology D).obj (op (Scheme.Etale.mk (𝟙 T)))).map
        ((comparisonLowerStar D T).map t) =
      ((sheafSections (Scheme.ProEt.topology T) D).obj
        (op (Scheme.ProEt.mk (𝟙 T)))).map t := rfl
  rw [← ht]
  rw [reassoc_of% e.hom.naturality η]

private lemma etConstant_eq_inverse (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {X Y : Scheme.{u}} (h : X ⟶ Y) (M : D) :
    (Scheme.upperStarConstantSheafIso D h).hom.app M =
      Scheme.constantInverse Y.smallEtaleTopology X.smallEtaleTopology
        h.Etale (Etale.upperStarLowerStarAdjunction D h) M := by
  let ay := constantSheafAdj Y.smallEtaleTopology D terminalIsTerminal
  let ax := constantSheafAdj X.smallEtaleTopology D terminalIsTerminal
  let p := Etale.upperStarLowerStarAdjunction D h
  let d := Etale.lowerStarCompSheafSectionsTerminalIso D h
  let ac := (ay.comp p).ofNatIsoRight d
  apply (ac.homEquiv _ _).injective
  have hn := Adjunction.homEquiv_leftAdjointUniq_hom_app ac ax M
  change ac.homEquiv _ _ ((Scheme.upperStarConstantSheafIso D h).hom.app M) =
    ax.unit.app M at hn
  rw [hn]
  unfold Scheme.constantInverse
  conv_rhs => erw [transportedHom ay p d]
  simp only [Adjunction.homEquiv_apply, ax, ay, constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, sheafificationAdjunction_unit_app,
    Category.id_comp, Category.assoc]
  change (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
      (op (⊤_ X.Etale)) =
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
      (op (⊤_ Y.Etale)) ≫
      (Scheme.constantDirect Y.smallEtaleTopology X.smallEtaleTopology h.Etale M).hom.app
        (op (⊤_ Y.Etale)) ≫
      ((constantSheaf X.smallEtaleTopology D).obj M).obj.map
        (PreservesTerminal.iso h.Etale).inv.op
  rw [← Category.assoc, Scheme.constantDirect_unit]
  have hn := (toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj M)).naturality (PreservesTerminal.iso h.Etale).inv.op
  simpa only [constantSheaf, Functor.comp_obj, Functor.const_obj_map,
    Functor.const_obj_obj, Functor.op_obj, Category.id_comp] using hn

private lemma proConstant_eq_inverse (D : Type v₁) [Category.{u + 1} D]
    [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    {X Y : Scheme.{u}} (h : X ⟶ Y) (M : D) :
    (constantSheafCompUpperStarIso D h).hom.app M =
      Scheme.constantInverse (D := D) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
        (proEtaleBaseChange h) (upperStarLowerStarAdjunction D h) M := by
  let ay := constantSheafΓAdj (Scheme.ProEt.topology Y) D
  let ax := constantSheafΓAdj (Scheme.ProEt.topology X) D
  let p := upperStarLowerStarAdjunction D h
  let d := globalSectionsLowerStarIso D h
  let ac := (ay.comp p).ofNatIsoRight d
  apply (ac.homEquiv _ _).injective
  have hn := Adjunction.homEquiv_leftAdjointUniq_hom_app ac ax M
  change ac.homEquiv _ _ ((constantSheafCompUpperStarIso D h).hom.app M) = ax.unit.app M at hn
  rw [hn]
  unfold Scheme.constantInverse
  conv_rhs => erw [transportedHom ay p d]
  let ex : Sheaf.Γ (Scheme.ProEt.topology X) D ≅
      (sheafSections (Scheme.ProEt.topology X) D).obj
        (op (Scheme.ProEt.mk (𝟙 X))) :=
    Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) D
      (Scheme.ProEt.isTerminalMkId X)
  let ey := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology Y) D
    (Scheme.ProEt.isTerminalMkId Y)
  apply (cancel_mono (ex.hom.app ((constantSheaf (Scheme.ProEt.topology X) D).obj M))).mp
  have hx := ax.unit_rightAdjointUniq_hom_app
    (constantSheafAdj (Scheme.ProEt.topology X) D (Scheme.ProEt.isTerminalMkId X)) M
  have hy := ay.unit_rightAdjointUniq_hom_app
    (constantSheafAdj (Scheme.ProEt.topology Y) D (Scheme.ProEt.isTerminalMkId Y)) M
  dsimp only [d, globalSectionsLowerStarIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app]
  simp only [Category.comp_id, Adjunction.homEquiv_apply, Category.assoc]
  erw [ey.hom.naturality_assoc]
  rw [← Category.assoc]
  erw [hx, hy]
  simp only [constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, sheafificationAdjunction_unit_app, Category.id_comp]
  simp only [NatIso.ofComponents_hom_app, Iso.refl_hom, Category.id_comp,
    Functor.mapIso_inv]
  dsimp only [sheafSections, Functor.flip, CategoryTheory.evaluation]
  change (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const (Scheme.ProEt X)ᵒᵖ).obj M)).app (op (Scheme.ProEt.mk (𝟙 X))) =
    (toSheafify (Scheme.ProEt.topology Y)
      ((Functor.const (Scheme.ProEt Y)ᵒᵖ).obj M)).app (op (Scheme.ProEt.mk (𝟙 Y))) ≫
      (Scheme.constantDirect (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
        (proEtaleBaseChange h) M).hom.app (op (Scheme.ProEt.mk (𝟙 Y))) ≫
      ((constantSheaf (Scheme.ProEt.topology X) D).obj M).obj.map
        (overPullbackObjMkIdIso h).inv.op
  rw [← Category.assoc, Scheme.constantDirect_unit]
  have hn := (toSheafify (Scheme.ProEt.topology X)
    ((Functor.const (Scheme.ProEt X)ᵒᵖ).obj M)).naturality
      (overPullbackObjMkIdIso h).inv.op
  simpa only [constantSheaf, Functor.comp_obj, Functor.const_obj_map,
    Functor.const_obj_obj, Functor.op_obj, Category.id_comp] using hn

private theorem constantComparisonTerminal_square (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : D) :
    (ProEtale.upperStar D f).map ((constantComparisonTerminal D Y).hom.app M) ≫
        (constantSheafCompUpperStarIso D f).hom.app M =
      (ProEtale.supportSiteComparisonCoefficientPullbackIso D f).inv.app
          ((constantSheaf Y.smallEtaleTopology D).obj M) ≫
        (ProEtale.comparisonUpperStar D X).map
          ((Scheme.upperStarConstantSheafIso D f).hom.app
            M) ≫ (constantComparisonTerminal D X).hom.app M := by
  let ap := (ProEtale.comparisonAdjunction D Y).comp
    (proEtaleSheafAdjunction f D)
  let ae := (Etale.upperStarLowerStarAdjunction D f).comp
    (ProEtale.comparisonAdjunction D X)
  let d := ProEtale.supportSiteComparisonCoefficientDirectImageIso D f
  have hd (S : Sheaf (ProEt.topology X) D) (W : Y.Etaleᵒᵖ) :
      ((d.inv.app S).hom.app W) = 𝟙 _ := by
    dsimp only [d, supportSiteComparisonCoefficientDirectImageIso]
    change ((𝟙 _ ≫ S.obj.map (𝟙 _)) ≫ 𝟙 _) = 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact S.obj.map_id _
  simp only [constantComparisonTerminal_eq_inverse, proConstant_eq_inverse, etConstant_eq_inverse]
  apply (ap.homEquiv _ _).injective
  change _ = ap.homEquiv _ _
    (((conjugateIsoEquiv ap ae).symm d).inv.app _ ≫ _)
  have hm := Scheme.homEquiv_mate ap ae d.symm
    ((ProEtale.comparisonUpperStar D X).map
      (Scheme.constantInverse Y.smallEtaleTopology X.smallEtaleTopology f.Etale
        (Etale.upperStarLowerStarAdjunction D f) M) ≫
      Scheme.constantInverse X.smallEtaleTopology (ProEt.topology X) (toProEt X)
        (ProEtale.comparisonAdjunction D X) M)
  simp only [Iso.symm_symm_eq] at hm
  erw [hm]
  have hp := Scheme.constantInverse_composite_adjunct Y.smallEtaleTopology
    (ProEt.topology Y) (ProEt.topology X) (toProEt Y) (proEtaleBaseChange f)
    (ProEtale.comparisonAdjunction D Y) (proEtaleSheafAdjunction f D)
    M
  have he := Scheme.constantInverse_composite_adjunct Y.smallEtaleTopology
    X.smallEtaleTopology (ProEt.topology X) f.Etale (toProEt X)
    (Etale.upperStarLowerStarAdjunction D f)
    (ProEtale.comparisonAdjunction D X) M
  erw [hp, he]
  apply ((sheafificationAdjunction Y.smallEtaleTopology D).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext W
  simp only [sheafificationAdjunction_unit_app, NatTrans.comp_app, Category.assoc]
  change (toSheafify Y.smallEtaleTopology
      ((Functor.const Y.Etaleᵒᵖ).obj M)).app W ≫
      (Scheme.constantDirect Y.smallEtaleTopology (ProEt.topology Y) (toProEt Y)
        M).hom.app W ≫
      (Scheme.constantDirect (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f)
        M).hom.app ((toProEt Y).op.obj W) =
    (toSheafify Y.smallEtaleTopology
      ((Functor.const Y.Etaleᵒᵖ).obj M)).app W ≫
      (Scheme.constantDirect Y.smallEtaleTopology X.smallEtaleTopology f.Etale
        M).hom.app W ≫
      (Scheme.constantDirect X.smallEtaleTopology (ProEt.topology X) (toProEt X)
        M).hom.app (f.Etale.op.obj W) ≫
      ((d.inv.app ((constantSheaf (ProEt.topology X) D).obj
        M)).hom.app W)
  rw [hd]
  rw [← Category.assoc, Scheme.constantDirect_unit, Scheme.constantDirect_unit,
    ← Category.assoc, ← Category.assoc, Scheme.constantDirect_unit, Scheme.constantDirect_unit]
  erw [Category.comp_id]
  rfl

attribute [local instance] Etale.evaluationMonoidal Etale.sectionsMonoidal
  Etale.constantPresheafAdj_monoidal Etale.constantSheafAdj_monoidal
@[instance_reducible]
private noncomputable def canonicalConstantEt (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    [HasSmallSiteSheafify D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) : (constantSheaf T.smallEtaleTopology D).Monoidal :=
  monoidalConstantSheaf _ _
@[instance_reducible]
private noncomputable def canonicalConstantPro (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    [HasSmallSiteSheafify D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) D).Monoidal :=
  monoidalConstantSheaf _ _
attribute [local instance] canonicalConstantEt canonicalConstantPro

private lemma constantComparisonTerminal_monoidal (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    [HasSmallSiteSheafify D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) : NatTrans.IsMonoidal (constantComparisonTerminal D T).inv := by
  let ae := (constantSheafAdj T.smallEtaleTopology D (Scheme.Etale.isTerminalMkId T)).comp
    (comparisonAdjunction D T)
  let ap := constantSheafAdj (Scheme.ProEt.topology T) D (Scheme.ProEt.isTerminalMkId T)
  let e : comparisonLowerStar D T ⋙
      (sheafSections T.smallEtaleTopology D).obj (op (Scheme.Etale.mk (𝟙 T))) ≅
    (sheafSections (Scheme.ProEt.topology T) D).obj (op (Scheme.ProEt.mk (𝟙 T))) := Iso.refl _
  have hm := Etale.pushforwardSections_monoidal (A := D) (Scheme.toProEt T)
    T.smallEtaleTopology (Scheme.ProEt.topology T) (Scheme.Etale.mk (𝟙 T))
  have hem : (Etale.pushforwardSectionsIso (A := D) (Scheme.toProEt T)
      T.smallEtaleTopology (Scheme.ProEt.topology T) (Scheme.Etale.mk (𝟙 T))).hom = e.hom := by
    apply NatTrans.ext
    funext P
    simp [Etale.pushforwardSectionsIso, Etale.precomposeEvaluationIso,
      Etale.pushforwardUnderlying_inv_app, e]
    rfl
  rw [hem] at hm
  let : NatTrans.IsMonoidal e.hom := hm
  have h := isMonoidal_conjugateEquiv_symm ae ap e.hom
  have he : (conjugateEquiv ae ap).symm e.hom =
      (constantComparisonTerminal D T).inv := rfl
  rw [he] at h
  exact h

end
end CachedConstantCoherence

private noncomputable def constantComparison (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      comparisonUpperStar (ModuleCat.{u + 1} A) T ≅
    constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
  CachedConstantCoherence.constantComparison (ModuleCat.{u + 1} A) T

private noncomputable def constantComparisonTerminal (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      comparisonUpperStar (ModuleCat.{u + 1} A) T ≅
    constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
  CachedConstantCoherence.constantComparisonTerminal (ModuleCat.{u + 1} A) T

private lemma constantComparison_eq_terminal (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : constantComparison A T = constantComparisonTerminal A T := by
  exact CachedConstantCoherence.constantComparison_eq_terminal (ModuleCat.{u + 1} A) T

private noncomputable local instance canonicalConstantEt (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).Monoidal :=
  CachedConstantCoherence.canonicalConstantEt (ModuleCat.{u + 1} A) T
private noncomputable local instance canonicalConstantPro (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).Monoidal :=
  CachedConstantCoherence.canonicalConstantPro (ModuleCat.{u + 1} A) T

private lemma constantComparisonTerminal_monoidal (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : NatTrans.IsMonoidal (constantComparisonTerminal A T).inv := by
  exact CachedConstantCoherence.constantComparisonTerminal_monoidal (ModuleCat.{u + 1} A) T

private theorem constantComparisonTerminal_square (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : ModuleCat.{u + 1} A) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f).map ((constantComparisonTerminal A Y).hom.app M) ≫
        (constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) f).hom.app M =
      (ProEtale.supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) f).inv.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
            M) ≫ (constantComparisonTerminal A X).hom.app M := by
  exact CachedConstantCoherence.constantComparisonTerminal_square (ModuleCat.{u + 1} A) f M

end CoefficientNormalization

section ExteriorComparisonProof
attribute [local instance] canonicalConstantEt canonicalConstantPro
universe w
open MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance] supportedCoefficients_isLeftAdjoint
attribute [-instance] supportedSheaf_monoidalPreadditive
  supportedSheaf_isMonoidalGeneric supportedSheaf_monoidalPreadditiveGeneric

open MonoidalCategory
private lemma monoidalCompositeSquare
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : C ⥤ E) (H : D ⥤ E)
    [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (e : F ⋙ H ≅ G) [NatTrans.IsMonoidal e.inv] (M N : C) :
    e.inv.app (M ⊗ N) ≫ H.map (Functor.OplaxMonoidal.δ F M N) ≫
        Functor.OplaxMonoidal.δ H (F.obj M) (F.obj N) =
      Functor.OplaxMonoidal.δ G M N ≫ (e.inv.app M ⊗ₘ e.inv.app N) := by
  apply (cancel_epi (Functor.LaxMonoidal.μ G M N)).mp
  have hm := NatTrans.IsMonoidal.tensor (τ := e.inv) M N
  dsimp only [Functor.LaxMonoidal.comp_μ] at hm
  rw [← Category.assoc, ← Category.assoc, hm]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Functor.Monoidal.μ_δ]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ, Category.comp_id]

namespace CachedConstantCoherence
attribute [local instance] canonicalConstantEt canonicalConstantPro
private lemma comparison_tensor
    (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [HasSmallSiteSheafify D]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]
    [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) (M N : D) :
    (constantComparison D T).inv.app (M ⊗ N) ≫
        (comparisonUpperStar D T).map
          (Functor.OplaxMonoidal.δ (constantSheaf T.smallEtaleTopology D) M N) ≫
        Functor.OplaxMonoidal.δ (comparisonUpperStar D T)
          ((constantSheaf T.smallEtaleTopology D).obj M)
          ((constantSheaf T.smallEtaleTopology D).obj N) =
      Functor.OplaxMonoidal.δ (constantSheaf (Scheme.ProEt.topology T) D) M N ≫
        ((constantComparison D T).inv.app M ⊗ₘ (constantComparison D T).inv.app N) := by
  rw [constantComparison_eq_terminal]
  let : NatTrans.IsMonoidal (constantComparisonTerminal D T).inv :=
    constantComparisonTerminal_monoidal D T
  exact monoidalCompositeSquare (constantSheaf T.smallEtaleTopology D)
    (constantSheaf (Scheme.ProEt.topology T) D)
    (comparisonUpperStar D T) (constantComparisonTerminal D T) M N
end CachedConstantCoherence

section
variable {C D : Type*} [Category.{w + 1} C] [Category.{w + 1} D]
  [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [SymmetricCategory C] [SymmetricCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  (H : C ⥤ D) [H.Additive] [H.Monoidal] [H.PreservesFlat] [H.IsLeftAdjoint]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
private noncomputable def exactTensor :=
  conjugateTensor H.leftDerivedFunctor H.mapDerivedCategory
    H.leftDerivedFunctorIsoMapDerivedCategory H.leftDerivedTensorComparison

end

section NativeTensorConstruction
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctor
section
variable {C D : Type*} [Category.{w + 1} C] [Category.{w + 1} D]
  [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [BraidedCategory C] [BraidedCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
end
section
variable {C D : Type*} [Category.{w + 1} C] [Category.{w + 1} D]
  [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [SymmetricCategory C] [SymmetricCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
end
section NativeProTensor
variable (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (X : Scheme.{u})
    (G F₁ F₂ : D ⥤ Sheaf (Scheme.ProEt.topology X) D)
    [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
end NativeProTensor
end NativeTensorConstruction

section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
end

end ExteriorComparisonProof
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

namespace ProEtale

section OpenConstantProof
universe v
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true

private noncomputable def constantMap (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {Z X : Scheme.{u}} (i : Z ⟶ X) (M : D) :=
  (upperStarLowerStarAdjunction D i).unit.app
    ((constantSheaf (Scheme.ProEt.topology X) D).obj M) ≫
    (lowerStar D i).map ((constantSheafCompUpperStarIso D i).hom.app M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
private lemma constantMap_unit
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {Z X : Scheme.{u}}
    (i : Z ⟶ X) (M : D) :
    (constantSheafΓAdj (Scheme.ProEt.topology X) D).unit.app M ≫
      (Sheaf.Γ (Scheme.ProEt.topology X) D).map (constantMap D i M) ≫
      (globalSectionsLowerStarIso D i).hom.app _ =
    (constantSheafΓAdj (Scheme.ProEt.topology Z) D).unit.app M := by
  exact constantUnit_global D i M

attribute [local irreducible] constantMap

private theorem constantAdjunct_comp
    {B X Y Z : Type*} [Category B] [Category X] [Category Y] [Category Z]
    {LX : B ⥤ X} {LY : B ⥤ Y} {LZ : B ⥤ Z}
    {RX : X ⥤ B} {RY : Y ⥤ B} {RZ : Z ⥤ B}
    (ax : LX ⊣ RX) (ay : LY ⊣ RY) (az : LZ ⊣ RZ)
    (F : Z ⥤ Y) (G : Y ⥤ X) (H : Z ⥤ X) (p : F ⋙ G ≅ H)
    (ef : F ⋙ RY ≅ RZ) (eg : G ⋙ RX ≅ RY) (eh : H ⋙ RX ≅ RZ)
    (M : B) (f : LY.obj M ⟶ F.obj (LZ.obj M))
    (g : LX.obj M ⟶ G.obj (LY.obj M)) (h : LX.obj M ⟶ H.obj (LZ.obj M))
    (hf : ay.unit.app M ≫ RY.map f ≫ ef.hom.app _ = az.unit.app M)
    (hg : ax.unit.app M ≫ RX.map g ≫ eg.hom.app _ = ay.unit.app M)
    (hh : ax.unit.app M ≫ RX.map h ≫ eh.hom.app _ = az.unit.app M)
    (hp : RX.map (p.hom.app (LZ.obj M)) ≫ eh.hom.app _ =
      eg.hom.app _ ≫ ef.hom.app _) : g ≫ G.map f ≫ p.hom.app _ = h := by
  apply (ax.homEquiv _ _).injective
  apply (Iso.cancel_iso_hom_right _ _ (eh.app (LZ.obj M))).mp
  simp only [Adjunction.homEquiv_apply, Functor.map_comp, Iso.app_hom, Category.assoc]
  rw [hp]
  have hn := eg.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, reassoc_of% hg, hf, hh]

private lemma constantMap_comp
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {Z Y X : Scheme.{u}}
    (g : Z ⟶ Y) (h : Y ⟶ X) (M : D) :
    constantMap D h M ≫ (lowerStar D h).map (constantMap D g M) ≫
      (lowerStarComp D g h).hom.app _ = constantMap D (g ≫ h) M := by
  exact constantAdjunct_comp
    (constantSheafΓAdj (Scheme.ProEt.topology X) D)
    (constantSheafΓAdj (Scheme.ProEt.topology Y) D)
    (constantSheafΓAdj (Scheme.ProEt.topology Z) D)
    (lowerStar D g) (lowerStar D h) (lowerStar D (g ≫ h)) (lowerStarComp D g h)
    (globalSectionsLowerStarIso D g) (globalSectionsLowerStarIso D h)
    (globalSectionsLowerStarIso D (g ≫ h)) M
    (constantMap D g M) (constantMap D h M) (constantMap D (g ≫ h) M)
    (constantMap_unit D g M) (constantMap_unit D h M)
    (constantMap_unit D (g ≫ h) M) (globalSectionsLowerStarIso_comp D g h _)

end OpenConstantProof

variable (A : Type (u + 1)) [CommRing A] [Finite A] {C T U : Scheme.{u}}
  [IsLocallyNoetherian T] [IsLocallyNoetherian U]
  (i : C ⟶ T) [IsClosedImmersion i] (v : U ⟶ T) [IsOpenImmersion v]

end ProEtale

namespace ProEtale

section OpenCoefficientNormalization
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
end OpenCoefficientNormalization

end ProEtale
end AlgebraicGeometry
