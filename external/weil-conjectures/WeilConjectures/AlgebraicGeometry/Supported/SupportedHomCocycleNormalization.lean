/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import all Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.CategoryTheory.Sites.SmoothPurity.SupportLongExact
public import WeilConjectures.Algebra.Homology.SmoothPurity.ClosedSupportHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedConstantPresentation
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.CategoryTheory.R.RHomDerivedRoof
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso

/-! # Evaluation and cocycle normalization of supported Hom

Source: Milne, Lectures on Etale Cohomology, Section 9, Example 9.5 and the Ext proof
of Theorem 9.4, pp. 66--67; Stacks Tags 05TH, 05TI, 070I, 070J and 095L
(blueprint: lem-pur-supported-hom-cocycle-normalization).

The interface below specifies evaluation, the actual derived-unit transport, and the
localized cocycle map. It uses the existing kernel functor in both topologies.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

namespace AlgebraicGeometry

/-- Localize the canonical single-object cocycle without exposing its cochain construction.
Source: Stacks 070I (blueprint: lem-pur-supported-hom-cocycle-normalization). -/
@[irreducible] def supportedHomLocalizedCocycle.{uC, vC, wC}
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {B : C} (I : CochainComplex C ℤ) (a : ℤ) (f : B ⟶ I.X a)
    (hf : f ≫ I.d a (a + 1) = 0) :
    (DerivedCategory.singleFunctor C 0).obj B ⟶ (DerivedCategory.Q.obj I)⟦a⟧ :=
  ShiftedHom.map (Cocycle.equivHomShift.symm
    (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q

/-- The localized cocycle is the original shifted single-complex map.
Source: Stacks 070I (blueprint: lem-pur-supported-hom-cocycle-normalization). -/
theorem supportedHomLocalizedCocycle_eq.{uC, vC, wC}
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {B : C} (I : CochainComplex C ℤ) (a : ℤ) (f : B ⟶ I.X a)
    (hf : f ≫ I.d a (a + 1) = 0) :
    supportedHomLocalizedCocycle I a f hf =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q := by
  with_unfolding_all rfl

section Site

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
variable (A : Type (u + 1)) [CommRing A]
variable [HasSheafify J (ModuleCat.{u + 1} A)]
variable [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
variable [HasDerivedCategory.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
variable {T W : C} (hT : IsTerminal T) (j : W ⟶ T)
variable (B : Sheaf J (ModuleCat.{u + 1} A))
variable (rho : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B)

/-- A specified resolution induces this isomorphism in D+, using the canonical
quotient-to-derived comparisons on both complexes.
Source: Stacks 05TI and 070I; lem-sc-p1-rhom-hom-derived-roof
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def supportedHomResolutionIso
    (K I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
    (e : K ⟶ I) [QuasiIso e.hom] :
    DerivedCategory.Plus.Q.obj K ≅ DerivedCategory.Plus.Q.obj I :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.Plus.QCompιIso _).app K ≪≫
      asIso (DerivedCategory.Q.map e.hom) ≪≫
      (DerivedCategory.Plus.QCompιIso _).symm.app I)

/-- The type of additive evaluation isomorphisms onto the actual support kernel.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
abbrev SupportedHomEvaluationIso :=
  preadditiveCoyoneda.obj (op B) ≅
    Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j ⋙
      forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}

/-- Evaluation after the actual constant restriction, at the scalar one.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def SupportedHomEvaluation
    (theta : SupportedHomEvaluationIso J A j B) : Prop :=
  ∀ (M : Sheaf J (ModuleCat.{u + 1} A)) (f : B ⟶ M),
    kernel.ι (M.obj.map j.op) (theta.hom.app M f) =
      ((constantSheafAdj J (ModuleCat.{u + 1} A) hT).homEquiv _ _ (rho ≫ f)) 1

/-- The type of additive comparisons with derived morphisms, in all integer degrees.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
abbrev SupportedHomChi :=
  ∀ (F : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} A))) (a : ℤ),
    (Sheaf.supportHypercohomologyFunctor J (ModuleCat.{u + 1} A) j a).obj F ≃+
      ((DerivedCategory.singleFunctor (Sheaf J (ModuleCat.{u + 1} A)) 0).obj
        B ⟶ F.obj⟦a⟧)

/-- Naturality of the comparison on the bounded-below derived category.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def SupportedHomChiNatural (chi : SupportedHomChi J A j B) : Prop :=
  ∀ (F G : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} A)))
      (v : F ⟶ G) (a : ℤ)
      (s : (Sheaf.supportHypercohomologyFunctor J (ModuleCat.{u + 1} A) j a).obj F),
    chi G a ((Sheaf.supportHypercohomologyFunctor J (ModuleCat.{u + 1} A) j a).map v s) =
      chi F a s ≫ (DerivedCategory.Plus.ι.map v)⟦a⟧'

/-- The formula on every injective resolution and every supported cocycle.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def SupportedHomChiCocycle
    (theta : SupportedHomEvaluationIso J A j B)
    (chi : SupportedHomChi J A j B) : Prop :=
  ∀ (K I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
      [∀ r : ℤ, Injective (I.obj.X r)] (e : K ⟶ I) [QuasiIso e.hom] (a : ℤ)
      (x : ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj I.obj).cycles a),
    ∃! f : B ⟶ I.obj.X a,
      theta.hom.app (I.obj.X a) f =
        ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
          (ComplexShape.up ℤ) |>.obj I.obj).iCycles a x ∧
      ∃ hf : f ≫ I.obj.d a (a + 1) = 0,
        chi (DerivedCategory.Plus.Q.obj K) a
          ((Sheaf.supportSequenceModelIso J (ModuleCat.{u + 1} A)
            (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) I
            (DerivedCategory.Plus.Q.obj K) (supportedHomResolutionIso J A K I e).symm a).hom
              (((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
                (ComplexShape.up ℤ) |>.obj I.obj).homologyπ a x)) =
          supportedHomLocalizedCocycle I.obj a f hf ≫
            ((DerivedCategory.Plus.QCompιIso _).inv.app I)⟦a⟧' ≫
            (DerivedCategory.Plus.ι.map (supportedHomResolutionIso J A K I e).inv)⟦a⟧'

attribute [local irreducible] supportedHomResolutionIso

/-- Evaluation, naturality, and the roof formula, all with the canonical normalization.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
structure SupportedHomCocycleNormalization where
  theta : SupportedHomEvaluationIso J A j B
  evaluation : SupportedHomEvaluation J A hT j B rho theta
  chi : SupportedHomChi J A j B
  naturality : SupportedHomChiNatural J A j B chi
  cocycle : SupportedHomChiCocycle J A j B theta chi

/-- The actual restriction on abelian groups underlying module-valued sections.
Source: Milne, Section 9, Example 9.5
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def supportedHomAbelianRestriction :
    (sheafSections J (ModuleCat.{u + 1} A)).obj (op T) ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} ⟶
      (sheafSections J (ModuleCat.{u + 1} A)).obj (op W) ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} :=
  Functor.whiskerRight ((sheafSections J (ModuleCat.{u + 1} A)).map j.op)
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})

/-- The inclusion of the actual support kernel, after forgetting scalar multiplication.
Source: Milne, Section 9, Example 9.5
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def supportedHomAbelianInclusion :
    Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} ⟶
      (sheafSections J (ModuleCat.{u + 1} A)).obj (op T) ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} :=
  Functor.whiskerRight (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j)
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})

/-- Agreement on injective representatives with the shifted restriction cone: the
comparison is exactly kernel inclusion composed with evaluation, hence sends a supported
section to `(0,s)`. This specifies the comparison itself, including its sign.
Source: blueprint lemma-cycle-class-cartier-divisor, Hom triangle proof; Milne, Section 9
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def SupportedHomCocycleNormalization.ConeAgreement
    (N : SupportedHomCocycleNormalization J A hT j B rho) : Prop :=
  ∀ (I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
      [∀ r : ℤ, Injective (I.obj.X r)],
    ∃ h : ((supportedHomAbelianInclusion J A j).mapHomologicalComplex
          (ComplexShape.up ℤ)).app I.obj ≫
        ((supportedHomAbelianRestriction J A j).mapHomologicalComplex
          (ComplexShape.up ℤ)).app I.obj = 0,
      QuasiIso (CochainComplex.closedConeLift
        (((supportedHomAbelianRestriction J A j).mapHomologicalComplex
          (ComplexShape.up ℤ)).app I.obj)
        (((supportedHomAbelianInclusion J A j).mapHomologicalComplex
          (ComplexShape.up ℤ)).app I.obj) h) ∧
      QuasiIso (((NatIso.mapHomologicalComplex N.theta (ComplexShape.up ℤ)).app I.obj).hom ≫
        CochainComplex.closedConeLift
          (((supportedHomAbelianRestriction J A j).mapHomologicalComplex
            (ComplexShape.up ℤ)).app I.obj)
          (((supportedHomAbelianInclusion J A j).mapHomologicalComplex
            (ComplexShape.up ℤ)).app I.obj) h)

end Site

namespace Etale

/-- The scalar-preserving constant restriction to the open site, obtained by sheafification.
Source: Milne, Section 9, Example 9.5; Stacks 03DI
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def supportedHomOpenConstantMap (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶
      (openImmersionRestriction (ModuleCat.{u + 1} A) j).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) :=
  ((sheafificationAdjunction U.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ _).symm
    (Functor.whiskerLeft (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).op
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))))

/-- The actual open counit at the constant module, with the scalar-preserving restriction.
Source: Milne, Section 9, Example 9.5; Stacks 03DI
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def supportedHomOpenCounit (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _).symm
    (supportedHomOpenConstantMap A j)

/-- Under the two evaluation adjunctions, precomposition with the actual open counit
is the actual restriction of sections. The site arrow has underlying morphism `j`.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def SupportedHomOpenEvaluation (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : Prop :=
  ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (g : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A) ⟶ M),
    ((constantSheafAdj U.smallEtaleTopology (ModuleCat.{u + 1} A)
      (MorphismProperty.Over.mkIdTerminal _ _)).homEquiv _ _
        ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _
          (supportedHomOpenCounit A j ≫ g))) 1 =
      M.obj.map (MorphismProperty.Over.homMk j
        (by exact (Category.comp_id j).trans (Category.id_comp j).symm) :
          (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj
            (Scheme.Etale.mk (𝟙 U)) ⟶ Scheme.Etale.mk (𝟙 X)).op
        (((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
          (MorphismProperty.Over.mkIdTerminal _ _)).homEquiv _ _ g) 1)

/-- The prescribed etale coefficient object and its constant restriction map.
Source: Milne, Section 9, proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def supportedHomConstantRestriction (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i).obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app (ModuleCat.of A A)).hom

/-- Specialization of evaluation normalization to the etale site of the closed pair.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
abbrev supportedHomNormalization (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  SupportedHomCocycleNormalization X.smallEtaleTopology P.Coefficient
    (MorphismProperty.Over.mkIdTerminal _ _) (supportRestrictionArrow i)
    ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale Z))
    (supportedHomConstantRestriction P.Coefficient i)

end Etale

namespace ProEtale

/-- The actual open counit, adjoint to the existing scalar-preserving constant map.
Source: Milne, Section 9, Ext proof; pro-etale constant presentation
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def supportedHomOpenCounit (A : Type u) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).homEquiv
    _ _).symm (Scheme.proEtaleFixedOpenConstantMap j A)

/-- Evaluation of precomposition by the pro-etale open counit is restriction.
Source: Milne, Section 9, Example 9.5 and Ext proof, in the pro-etale topology
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def SupportedHomOpenEvaluation (A : Type u) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : Prop :=
  ∀ (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
      (g : Scheme.proEtaleFixedConstantModule X A ⟶ M),
    ((constantSheafAdj (Scheme.ProEt.topology U)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (MorphismProperty.Over.mkIdTerminal _ _)).homEquiv _ _
        ((openImmersionLowerShriekAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).homEquiv _ _
          (supportedHomOpenCounit A j ≫ g))) 1 =
      M.obj.map (MorphismProperty.Over.homMk j
        (by exact (Category.comp_id j).trans (Category.id_comp j).symm) :
          (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
            (Scheme.ProEt.mk (𝟙 U)) ⟶ Scheme.ProEt.mk (𝟙 X)).op
        (((constantSheafAdj (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1} A))
          (MorphismProperty.Over.mkIdTerminal _ _)).homEquiv _ _ g) 1)

/-- The same ordinary constant sheaf on the pro-etale site, before its canonical
identification with the etale-pullback presentation `P.constant`.
Source: Milne, Section 9, Example 9.5; pro-etale constant presentation
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
abbrev supportedHomNormalization (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  SupportedHomCocycleNormalization (Scheme.ProEt.topology X) P.Coefficient
    (MorphismProperty.Over.mkIdTerminal _ _) (supportRestrictionArrow i)
    ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (Scheme.proEtaleFixedConstantModule Z P.Ring))
    (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} P.Coefficient)
      (ModuleCat.of P.Coefficient P.Coefficient))

end ProEtale

-- Keep the canonical coefficient equivalences and unit comparisons abstract in proofs.

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem supportModule_restriction_epi
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Type (u + 1)) [Ring R] [HasSheafify J (ModuleCat.{u + 1} R)]
    (I : Sheaf J (ModuleCat.{u + 1} R)) [Injective I]
    {W V : C} (j : W ⟶ V) [Mono j] : Epi (I.obj.map j.op) := by
  have : Injective I.obj := Injective.injective_of_adjoint (sheafificationAdjunction J _) I
  let a : (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free R) ⟶
      (uliftYoneda.{u + 1}.obj V ⋙ ModuleCat.free R) :=
    Functor.whiskerRight (uliftYoneda.{u + 1}.map j) (ModuleCat.free R)
  have : Mono a := by
    have (T : Cᵒᵖ) : Mono (a.app T) := by
      rw [ModuleCat.mono_iff_injective]
      apply Finsupp.mapDomain_injective
      intro x y h
      apply ULift.ext
      exact (cancel_mono j).1 (congrArg ULift.down h)
    exact NatTrans.mono_of_mono_app a
  rw [ModuleCat.epi_iff_surjective]
  intro s
  let b : (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free R) ⟶ I.obj :=
    { app := fun T ↦ ModuleCat.freeDesc (↾fun g ↦ I.obj.map g.down.op s)
      naturality := by
        intro T T' g
        apply ModuleCat.free_hom_ext
        intro x
        simp only [Functor.comp_map, ConcreteCategory.comp_apply]
        erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        change I.obj.map ((g.unop ≫ x.down).op) s = _
        rw [op_comp, I.obj.map_comp]
        rfl }
  obtain ⟨g, hg⟩ := Injective.factors b a
  refine ⟨g.app (op V) (ModuleCat.freeMk (ULift.up (𝟙 V))), ?_⟩
  have he := congrArg (fun f ↦ f.app (op W) (ModuleCat.freeMk (ULift.up (𝟙 W)))) hg
  have hn := ConcreteCategory.congr_hom (g.naturality j.op)
    (ModuleCat.freeMk (ULift.up (𝟙 V)))
  have he' : g.app (op W) (ModuleCat.freeMk (ULift.up j)) = s := by
    simpa [a, b, ModuleCat.free_map_apply, ModuleCat.freeDesc_apply] using he
  have hn' : I.obj.map j.op (g.app (op V) (ModuleCat.freeMk (ULift.up (𝟙 V)))) =
      g.app (op W) (ModuleCat.freeMk (ULift.up j)) := by
    simpa [ModuleCat.free_map_apply] using hn.symm
  exact hn'.trans he'

@[irreducible] private noncomputable def constantHomEquiv
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R : Type (u + 1)} [CommRing R] [HasSheafify J (ModuleCat.{u + 1} R)]
    {T : C} (hT : IsTerminal T) (M : Sheaf J (ModuleCat.{u + 1} R)) :
    ((constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R) ⟶ M) ≃+
      M.obj.obj (op T) :=
  ((constantSheafAdj J (ModuleCat.{u + 1} R) hT).homAddEquiv _ M).trans
    (ModuleCat.homAddEquiv.trans (LinearMap.ringLmapEquivSelf R ℕ _).toAddEquiv)

set_option backward.isDefEq.respectTransparency false in
private theorem constantHomEquiv_apply
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R : Type (u + 1)} [CommRing R] [HasSheafify J (ModuleCat.{u + 1} R)]
    {T : C} (hT : IsTerminal T) (M : Sheaf J (ModuleCat.{u + 1} R))
    (f : (constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R) ⟶ M) :
    constantHomEquiv J hT M f = f.hom.app (op T)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R))).app (op T) (1 : R)) := by
  unfold constantHomEquiv
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizationConstantMapEvaluation
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (A : Type (u + 1)) [CommRing A]
    [HasSheafify J (ModuleCat.{u + 1} A)] [HasSheafify K (ModuleCat.{u + 1} A)]
    (F : C ⥤ D) [F.IsContinuous J K] {U : C} {T : D}
    (hU : IsTerminal U) (hT : IsTerminal T) (v : F.obj U ⟶ T)
    (M : Sheaf K (ModuleCat.{u + 1} A))
    (f : (constantSheaf K (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ M) :
    let R := F.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J K
    let c := ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const Cᵒᵖ).obj (ModuleCat.of A A))
      (R.obj ((constantSheaf K (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)))).symm
        (Functor.whiskerLeft F.op
          (toSheafify K ((Functor.const Dᵒᵖ).obj (ModuleCat.of A A))))
    constantHomEquiv J hU (R.obj M) (c ≫ R.map f) =
      M.obj.map v.op (constantHomEquiv K hT M f) := by
  dsimp only
  rw [constantHomEquiv_apply, constantHomEquiv_apply]
  let η := toSheafify K ((Functor.const Dᵒᵖ).obj (ModuleCat.of A A))
  have hn := ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv
    ((Functor.const Cᵒᵖ).obj (ModuleCat.of A A))
    ((F.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J K).obj
      ((constantSheaf K (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)))).apply_symm_apply
        (Functor.whiskerLeft F.op η)
  have hu := congrArg (fun k ↦ k.app (op U)) hn
  have hu1 := congrArg (fun k ↦ k (1 : A)) hu
  change f.hom.app (op (F.obj U)) _ = _
  change _ = _ at hu1
  erw [hu1]
  have hf := congrArg (fun k ↦ k (η.app (op T) (1 : A))) (f.hom.naturality v.op)
  have hη := congrArg (fun k ↦ k (1 : A)) (η.naturality v.op)
  simp only [Functor.const_obj_map, ModuleCat.comp_apply] at hη hf
  change η.app (op (F.obj U)) (1 : A) = _ at hη
  exact (congrArg (fun x ↦ f.hom.app (op (F.obj U)) x) hη).trans hf

private theorem normalizationOpenData
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (A : Type (u + 1)) [CommRing A]
    [HasSheafify J (ModuleCat.{u + 1} A)] [HasSheafify K (ModuleCat.{u + 1} A)]
    (F : C ⥤ D) [F.IsContinuous J K] {U : C} {T W : D}
    (hU : IsTerminal U) (hT : IsTerminal T) (v : F.obj U ⟶ T) (w : W ≅ F.obj U)
    (L : Sheaf J (ModuleCat.{u + 1} A) ⥤ Sheaf K (ModuleCat.{u + 1} A))
    [L.Additive] (adj : L ⊣ F.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J K) :
    let R := F.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J K
    let AU := (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)
    let AX := (constantSheaf K (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)
    let c := ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const Cᵒᵖ).obj (ModuleCat.of A A)) (R.obj AX)).symm
        (Functor.whiskerLeft F.op
          (toSheafify K ((Functor.const Dᵒᵖ).obj (ModuleCat.of A A))))
    let eps := (adj.homEquiv AU AX).symm c
    (∃ evalW : ∀ M : Sheaf K (ModuleCat.{u + 1} A),
        (L.obj AU ⟶ M) ≃+ M.obj.obj (op W),
      ∀ (M : Sheaf K (ModuleCat.{u + 1} A)) (g : AX ⟶ M),
        evalW M (eps ≫ g) = M.obj.map (w.hom ≫ v).op (constantHomEquiv K hT M g)) ∧
    (∀ (M : Sheaf K (ModuleCat.{u + 1} A)) (g : AX ⟶ M),
      ((constantSheafAdj J (ModuleCat.{u + 1} A) hU).homEquiv _ _
        (adj.homEquiv _ _ (eps ≫ g))) 1 =
        M.obj.map v.op (((constantSheafAdj K (ModuleCat.{u + 1} A) hT).homEquiv _ _ g) 1)) := by
  classical
  dsimp only
  let R := F.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J K
  let AU := (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)
  let AX := (constantSheaf K (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)
  let c : AU ⟶ R.obj AX := ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const Cᵒᵖ).obj (ModuleCat.of A A)) (R.obj AX)).symm
        (Functor.whiskerLeft F.op
          (toSheafify K ((Functor.const Dᵒᵖ).obj (ModuleCat.of A A))))
  let eps := (adj.homEquiv AU AX).symm c
  let e (M : Sheaf K (ModuleCat.{u + 1} A)) :=
    (adj.homAddEquiv AU M).trans (constantHomEquiv J hU (R.obj M))
  have he (M : Sheaf K (ModuleCat.{u + 1} A)) (g : AX ⟶ M) :
      e M (eps ≫ g) = M.obj.map v.op (constantHomEquiv K hT M g) := by
    dsimp only [e, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
    rw [Adjunction.homEquiv_naturality_right]
    dsimp only [eps]
    rw [Equiv.apply_symm_apply]
    exact normalizationConstantMapEvaluation J K A F hU hT v M g
  constructor
  · refine ⟨fun M ↦ (e M).trans (M.obj.mapIso w.op).toLinearEquiv.toAddEquiv, ?_⟩
    intro M g
    dsimp only [AddEquiv.trans_apply]
    rw [he]
    change M.obj.map w.hom.op (M.obj.map v.op _) = M.obj.map (w.hom ≫ v).op _
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, op_comp]
  · intro M g
    have h := he M g
    unfold e constantHomEquiv at h
    exact h

namespace ProEtale

attribute [local irreducible] Scheme.sfIntrinsicModuleEquivalence
  Scheme.proEtaleConstantModuleUnit Scheme.sfIntrinsicDirectImageComparison

set_option backward.isDefEq.respectTransparency true in
private theorem fixedConstantPresentation (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ h : supportedHomOpenCounit A i.openComplement.ι ≫
        Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} (ULift.{u + 1} A))
          (ModuleCat.of _ (ULift.{u + 1} A)) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ
        (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} (ULift.{u + 1} A))
          (ModuleCat.of _ (ULift.{u + 1} A))) h)) := by
  classical
  let E := Scheme.sfIntrinsicModuleEquivalence X A
  let EU := Scheme.sfIntrinsicModuleEquivalence i.openComplement.toScheme A
  let AZ := Scheme.proEtaleFixedConstantModule Z A
  let AX := Scheme.proEtaleFixedConstantModule X A
  let AU := Scheme.proEtaleFixedConstantModule i.openComplement.toScheme A
  let L := openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A))
    i.openComplement.ι
  let ρ := Scheme.proEtaleConstantDirectImageMap i
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) (ModuleCat.of _ (ULift.{u + 1} A))
  let k : E.functor.obj (L.obj AU) ≅
      (Scheme.sfIntrinsicExtensionByZero i.openComplement.ι A).obj
        (Scheme.proEtaleConstantModule i.openComplement.toScheme A) :=
    E.functor.mapIso (L.mapIso (EU.unitIso.app AU ≪≫
      EU.inverse.mapIso (Scheme.proEtaleConstantModuleUnit i.openComplement.toScheme A)))
  let q : E.functor.obj ((lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj AZ) ≅
        (Scheme.proEtaleConstantModuleDirectImage i A).obj
          (Scheme.proEtaleConstantModule Z A) :=
    (Scheme.sfIntrinsicDirectImageComparison i A).symm.app AZ ≪≫
      (Scheme.proEtaleConstantModuleDirectImage i A).mapIso
        (Scheme.proEtaleConstantModuleUnit Z A)
  have he : E.functor.map (supportedHomOpenCounit A i.openComplement.ι) ≫
      (Scheme.proEtaleConstantModuleUnit X A).hom =
        k.hom ≫ Scheme.proEtaleOpenConstantCounit i.openComplement.ι A := by
    calc
      _ = k.hom ≫ k.inv ≫ E.functor.map
          (supportedHomOpenCounit A i.openComplement.ι) ≫
          (Scheme.proEtaleConstantModuleUnit X A).hom := by
        rw [Iso.hom_inv_id_assoc]
      _ = _ := by
        dsimp only [k, Scheme.proEtaleOpenConstantCounit, Scheme.sfIntrinsicExtensionByZero,
          Functor.comp_map, Functor.mapIso_inv, Iso.trans_inv, Iso.app_inv]
        simp only [Functor.map_comp, Category.assoc]
        rfl
  have hr : E.functor.map ρ ≫ q.hom =
      (Scheme.proEtaleConstantModuleUnit X A).hom ≫
        Scheme.proEtaleClosedConstantRestriction i A := by
    dsimp [q, Scheme.proEtaleClosedConstantRestriction]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  obtain ⟨h, ⟨hc⟩⟩ := Scheme.proEtale_supported_constant_presentation A i
  have hz : supportedHomOpenCounit A i.openComplement.ι ≫ ρ = 0 := by
    apply E.functor.map_injective
    apply (cancel_mono q.hom).mp
    rw [Functor.map_comp, Functor.map_zero, zero_comp, Category.assoc, hr,
      ← Category.assoc, he, Category.assoc, h, comp_zero]
  refine ⟨hz, ⟨?_⟩⟩
  apply isColimitOfReflects E.functor
  refine (isColimitMapCoconeCoforkEquiv' E.functor hz).symm ?_
  exact IsCokernel.ofIso _ hc _ k.symm (Scheme.proEtaleConstantModuleUnit X A).symm
    q.symm (by
      apply (cancel_epi k.hom).mp
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
      rw [← Category.assoc, ← he]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]) (by
      apply (cancel_epi (Scheme.proEtaleConstantModuleUnit X A).hom).mp
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc, Cofork.π_ofπ]
      rw [← Category.assoc, ← hr]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])

set_option backward.isDefEq.respectTransparency false in
private theorem normalizationOpenDataAt (A : Type u) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (∃ evalW : ∀ M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)),
      ((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) i.openComplement.ι).obj
        (Scheme.proEtaleFixedConstantModule i.openComplement.toScheme A) ⟶ M) ≃+
          M.obj.obj (op (Scheme.ProEt.mk i.openComplement.ι)),
      ∀ (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
          (g : Scheme.proEtaleFixedConstantModule X A ⟶ M),
        evalW M (supportedHomOpenCounit A i.openComplement.ι ≫ g) =
          M.obj.map (supportRestrictionArrow i).op (constantHomEquiv (Scheme.ProEt.topology X)
            (MorphismProperty.Over.mkIdTerminal _ _) M g)) ∧
      SupportedHomOpenEvaluation A i.openComplement.ι := by
  let j := i.openComplement.ι
  let F := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  let : F.IsContinuous (Scheme.ProEt.topology i.openComplement.toScheme)
      (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  let w : Scheme.ProEt.mk j ≅ F.obj (Scheme.ProEt.mk (𝟙 i.openComplement.toScheme)) :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (𝟙 _ ≫ j) = j
      simp only [Category.id_comp])
  let v : F.obj (Scheme.ProEt.mk (𝟙 i.openComplement.toScheme)) ⟶ Scheme.ProEt.mk (𝟙 X) :=
    MorphismProperty.Over.homMk j
      (by exact (Category.comp_id j).trans (Category.id_comp j).symm)
  obtain ⟨⟨evalW, he⟩, h⟩ := normalizationOpenData
    (Scheme.ProEt.topology i.openComplement.toScheme) (Scheme.ProEt.topology X)
    (ULift.{u + 1} A) F
    (MorphismProperty.Over.mkIdTerminal _ _) (MorphismProperty.Over.mkIdTerminal _ _) v w
    (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
  refine ⟨⟨evalW, ?_⟩, h⟩
  intro M g
  have hv : w.hom ≫ v = supportRestrictionArrow i := by
    apply (MorphismProperty.Over.forget @WeaklyEtale ⊤ X ⋙ Over.forget X).map_injective
    exact Category.id_comp j
  simpa only [hv] using! he M g

end ProEtale

namespace Etale

private lemma unit_app_comp_lowerStarCompSheafSectionsTerminalIso_hom_app_comp
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : AlgebraicGeometry.Etale f)
    (B : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app B).hom.app
        (op (⊤_ Y.Etale)) ≫
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) f).hom.app
        ((f)^*[(ModuleCat.{u + 1} A)].obj B) ≫
      ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) f hf).hom.app B).hom.app
        (op (⊤_ X.Etale)) =
    B.obj.map (terminal.from ((MorphismProperty.Over.map ⊤ hf).obj (⊤_ X.Etale))).op := by
  let ι := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) f hf
  let P : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj (⊤_ Y.Etale) ≅
      ⊤_ X.Etale := PreservesTerminal.iso _
  have h₁ : ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app B).hom.app
        (op (⊤_ Y.Etale)) ≫ (ι.hom.app B).hom.app
          (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj
            (⊤_ Y.Etale))) =
      ((localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) f hf).unit.app
        B).hom.app (op (⊤_ Y.Etale)) :=
    congrArg (fun φ ↦ φ.hom.app (op (⊤_ Y.Etale)))
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit_leftAdjointUniq_hom_app
        (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) f hf) B)
  obtain ⟨m, hm⟩ : ∃ m, ((localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) f
      hf).unit.app B).hom.app (op (⊤_ Y.Etale)) = B.obj.map (Quiver.Hom.op m) := ⟨_, rfl⟩
  have h₂ := (ι.hom.app B).hom.naturality P.inv.op
  have h₃ : (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) f).hom.app
      ((f)^*[(ModuleCat.{u + 1} A)].obj B) =
        ((f)^*[(ModuleCat.{u + 1} A)].obj B).obj.map P.inv.op := rfl
  rw [h₃, h₂, ← Category.assoc, h₁, hm]
  change B.obj.map _ ≫ B.obj.map _ = _
  rw [← Functor.map_comp]
  congr 1
  exact Quiver.Hom.unop_inj (terminal.hom_ext _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem normalizationConstantComparison (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) j).inv.app
      (ModuleCat.of A A)) ≫
        (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A)) = supportedHomOpenConstantMap A j := by
  let AX := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (ModuleCat.of A A)
  let e := Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) j
  let ι := upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j
  have hB : (constantSheafAdj U.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).homEquiv _ _ (e.inv.app (ModuleCat.of A A) ≫ ι.hom.app AX) =
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).unit.app (ModuleCat.of A A) ≫
          AX.obj.map (terminal.from
            ((MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale j)).obj
              (⊤_ U.Etale))).op := by
    rw [Adjunction.homEquiv_naturality_right]
    simp only [e, Scheme.upperStarConstantSheafIso, Adjunction.leftAdjointUniq_inv_app,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [← unit_app_comp_lowerStarCompSheafSectionsTerminalIso_hom_app_comp A j
      (inferInstance : AlgebraicGeometry.Etale j)]
    simp [Adjunction.comp_unit_app]
    rfl
  apply (constantHomEquiv U.smallEtaleTopology terminalIsTerminal _).injective
  conv_lhs => unfold constantHomEquiv
  change ((constantSheafAdj U.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).homEquiv _ _
      (e.inv.app (ModuleCat.of A A) ≫ ι.hom.app AX)) (1 : A) = _
  rw [hB]
  rw [constantHomEquiv_apply]
  let T := ⊤_ U.Etale
  let V := (MorphismProperty.Over.map ⊤
    (inferInstance : AlgebraicGeometry.Etale j)).obj T
  let η := toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))
  let t := Functor.whiskerLeft
    (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale j)).op η
  have hn := ((sheafificationAdjunction U.smallEtaleTopology
    (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const U.Etaleᵒᵖ).obj (ModuleCat.of A A))
      ((openImmersionRestriction (ModuleCat.{u + 1} A) j).obj AX)).apply_symm_apply t
  have hu : (toSheafify U.smallEtaleTopology
      ((Functor.const U.Etaleᵒᵖ).obj (ModuleCat.of A A))).app (op T) ≫
      (supportedHomOpenConstantMap A j).hom.app (op T) = η.app (op V) :=
    congrArg (fun k ↦ k.app (op T)) hn
  have hu1 := congrArg (fun k ↦ k (1 : A)) hu
  change _ = _ at hu1
  erw [hu1]
  have hη := congrArg (fun k ↦ k (1 : A))
    (η.naturality (terminal.from V).op)
  have hunit : (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).unit.app (ModuleCat.of A A) (1 : A) =
      η.app (op (⊤_ X.Etale)) (1 : A) := by
    have h := constantHomEquiv_apply X.smallEtaleTopology terminalIsTerminal AX (𝟙 AX)
    unfold constantHomEquiv at h
    change ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).homEquiv _ AX (𝟙 AX)) 1 = _ at h
    erw [Adjunction.homEquiv_id] at h
    exact h
  change AX.obj.map _
    ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).unit.app (ModuleCat.of A A) (1 : A)) = _
  rw [hunit]
  simpa only [Functor.const_obj_map, ModuleCat.comp_apply, ModuleCat.id_apply] using! hη.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizationConstantPresentation (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ hz : supportedHomOpenCounit A i.openComplement.ι ≫
        supportedHomConstantRestriction A i = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ
        (supportedHomConstantRestriction A i) hz)) := by
  let AX := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (ModuleCat.of A A)
  let j := i.openComplement.ι
  let S := openClosedShortComplex (ModuleCat.{u + 1} A) j i
    (disjoint_range_of_range_eq_compl j i i.range_eq_compl_range_openComplement_ι) AX
  have hs : S.ShortExact := shortExact_openClosedShortComplex
    (ModuleCat.{u + 1} A) j i AX i.range_eq_compl_range_openComplement_ι
  let e₁ := (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapIso
    (((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) j).app
      (ModuleCat.of A A)).symm)
  let e₃ := (lowerStar (ModuleCat.{u + 1} A) i).mapIso
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app (ModuleCat.of A A))
  have hf : e₁.hom ≫ S.f = supportedHomOpenCounit A j := by
    apply ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _).injective
    change ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv
      _ AX) ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) j).inv.app
          (ModuleCat.of A A)) ≫
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).counit.app AX) =
      ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ AX)
        (((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ AX).symm
          (supportedHomOpenConstantMap A j))
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left]
    have hcounit : (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).counit.app AX =
        ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ AX).symm
          ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app AX) := by
      have h := (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).homEquiv_symm_id AX
      change (((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).ofNatIsoRight
        (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm).homEquiv
          _ AX).symm (𝟙 _) = _ at h
      simpa only [Adjunction.homEquiv_ofNatIsoRight_symm_apply,
        Iso.symm_inv, Category.id_comp] using h.symm
    erw [hcounit, Equiv.apply_symm_apply]
    change (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) j).inv.app
      (ModuleCat.of A A) ≫ (upperStarIsoOpenImmersionRestriction
        (ModuleCat.{u + 1} A) j).hom.app AX = supportedHomOpenConstantMap A j
    exact normalizationConstantComparison A j
  have hg : S.g ≫ e₃.hom = supportedHomConstantRestriction A i := by
    rfl
  have hz : supportedHomOpenCounit A j ≫ supportedHomConstantRestriction A i = 0 := by
    rw [← hf, ← hg, Category.assoc, ← Category.assoc S.f, S.zero, zero_comp, comp_zero]
  refine ⟨hz, ⟨?_⟩⟩
  exact IsCokernel.ofIso _ hs.gIsCokernel _ e₁.symm (Iso.refl AX) e₃
    (by simp only [Iso.refl_hom, Iso.symm_hom]
        erw [← hf, Iso.inv_hom_id_assoc, Category.comp_id])
    (by simpa only [Iso.refl_hom, Category.id_comp, Cofork.π_ofπ] using! hg.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem normalizationOpenDataAt (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (∃ evalW : ∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A)),
      ((openImmersionLowerShriek (ModuleCat.{u + 1} (A)) i.openComplement.ι).obj
        ((constantSheaf i.openComplement.toScheme.smallEtaleTopology
          (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) ⟶ M) ≃+
            M.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)),
      ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
          (g : ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A)) ⟶ M),
        evalW M (supportedHomOpenCounit A i.openComplement.ι ≫ g) =
          M.obj.map (supportRestrictionArrow i).op (constantHomEquiv X.smallEtaleTopology
            (MorphismProperty.Over.mkIdTerminal _ _) M g)) ∧
      SupportedHomOpenEvaluation A i.openComplement.ι := by
  let j := i.openComplement.ι
  let F := MorphismProperty.Over.map ⊤ (inferInstance : Etale j)
  let : F.IsContinuous i.openComplement.toScheme.smallEtaleTopology X.smallEtaleTopology :=
    Scheme.isContinuous_overMap (inferInstance : Etale j) le_rfl
  let w : Scheme.Etale.mk j ≅ F.obj (Scheme.Etale.mk (𝟙 i.openComplement.toScheme)) :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (𝟙 _ ≫ j) = j
      simp only [Category.id_comp])
  let v : F.obj (Scheme.Etale.mk (𝟙 i.openComplement.toScheme)) ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk j
      (by exact (Category.comp_id j).trans (Category.id_comp j).symm)
  obtain ⟨⟨evalW, he⟩, h⟩ := normalizationOpenData
    i.openComplement.toScheme.smallEtaleTopology X.smallEtaleTopology A F
    (MorphismProperty.Over.mkIdTerminal _ _) (MorphismProperty.Over.mkIdTerminal _ _) v w
    (openImmersionLowerShriek (ModuleCat.{u + 1} (A)) j)
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} (A)) j)
  refine ⟨⟨evalW, ?_⟩, h⟩
  intro M g
  have hv : w.hom ≫ v = supportRestrictionArrow i := by
    apply (MorphismProperty.Over.forget @Etale ⊤ X ⋙ Over.forget X).map_injective
    exact Category.id_comp j
  simpa only [hv] using! he M g

end Etale
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizationEvaluation
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    {T W : C} (hT : IsTerminal T) (j : W ⟶ T)
    (D B : Sheaf J (ModuleCat.{u + 1} A))
    (eps : D ⟶ (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))
    (rho : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B)
    (hz : eps ≫ rho = 0) (hc : IsColimit (CokernelCofork.ofπ rho hz))
    (evalW : ∀ M : Sheaf J (ModuleCat.{u + 1} A), (D ⟶ M) ≃+ M.obj.obj (op W))
    (hW : ∀ (M : Sheaf J (ModuleCat.{u + 1} A))
        (g : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ M),
      evalW M (eps ≫ g) = M.obj.map j.op (constantHomEquiv J hT M g)) :
    ∃ theta : preadditiveCoyoneda.obj (op B) ≅
        Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j ⋙
          forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1},
      ∀ (M : Sheaf J (ModuleCat.{u + 1} A)) (f : B ⟶ M),
        kernel.ι (M.obj.map j.op) (theta.hom.app M f) =
          ((constantSheafAdj J (ModuleCat.{u + 1} A) hT).homEquiv _ _ (rho ≫ f)) 1 := by
  classical
  let homKer (M : Sheaf J (ModuleCat.{u + 1} A)) :
      (B ⟶ M) →+ (M.obj.map j.op).hom.ker :=
    { toFun := fun f ↦ ⟨constantHomEquiv J hT M (rho ≫ f), by
        rw [LinearMap.mem_ker, ← hW, ← Category.assoc, hz, zero_comp, map_zero]⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := by intro f g; apply Subtype.ext; simp }
  have hbij (M : Sheaf J (ModuleCat.{u + 1} A)) : Function.Bijective (homKer M) := by
    constructor
    · intro f g hfg
      apply Cofork.IsColimit.hom_ext hc
      apply (constantHomEquiv J hT M).injective
      exact congrArg Subtype.val hfg
    · intro x
      let g := (constantHomEquiv J hT M).symm x.val
      have hg : eps ≫ g = 0 := by
        apply (evalW M).injective
        rw [hW]
        simpa only [g, AddEquiv.apply_symm_apply, map_zero] using
          (show M.obj.map j.op x.val = 0 from x.property)
      refine ⟨hc.desc (CokernelCofork.ofπ g hg), ?_⟩
      apply Subtype.ext
      change constantHomEquiv J hT M
        (rho ≫ hc.desc (CokernelCofork.ofπ g hg)) = x.val
      rw [show rho ≫ hc.desc (CokernelCofork.ofπ g hg) = g from
        Cofork.IsColimit.π_desc hc]
      exact AddEquiv.apply_symm_apply _ _
  let e (M : Sheaf J (ModuleCat.{u + 1} A)) : (B ⟶ M) ≃+
      (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).obj M :=
    (AddEquiv.ofBijective (homKer M) (hbij M)).trans
      (ModuleCat.kernelIsoKer (M.obj.map j.op)).symm.toLinearEquiv.toAddEquiv
  have he (M : Sheaf J (ModuleCat.{u + 1} A)) (f : B ⟶ M) :
      kernel.ι (M.obj.map j.op) (e M f) = constantHomEquiv J hT M (rho ≫ f) := by
    change ((ModuleCat.kernelIsoKer _).inv ≫ kernel.ι _) (homKer M f) = _
    rw [ModuleCat.kernelIsoKer_inv_kernel_ι]
    rfl
  let theta : preadditiveCoyoneda.obj (op B) ≅
      Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} :=
    NatIso.ofComponents (fun M ↦ (e M).toAddCommGrpIso) (by
      intro M N f
      ext g
      apply (ModuleCat.mono_iff_injective (kernel.ι (N.obj.map j.op))).mp inferInstance
      change kernel.ι (N.obj.map j.op) (e N (g ≫ f)) =
        (kernel.map _ _ (f.hom.app _) (f.hom.app _) (f.hom.naturality j.op) ≫
          kernel.ι _) (e M g)
      rw [kernel.lift_ι]
      change _ = f.hom.app (op T) (kernel.ι (M.obj.map j.op) (e M g))
      rw [he, he]
      simp only [constantHomEquiv_apply]
      rfl)
  refine ⟨theta, ?_⟩
  intro M f
  exact (he M f).trans (by unfold constantHomEquiv; rfl)

namespace ProEtale

private theorem normalizationTheta (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ theta : SupportedHomEvaluationIso (Scheme.ProEt.topology X) P.Coefficient
        (supportRestrictionArrow i)
        ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
          (Scheme.proEtaleFixedConstantModule Z P.Ring)),
      SupportedHomEvaluation (Scheme.ProEt.topology X) P.Coefficient
        (MorphismProperty.Over.mkIdTerminal _ _) (supportRestrictionArrow i)
        ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
          (Scheme.proEtaleFixedConstantModule Z P.Ring))
        (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} P.Coefficient)
          (ModuleCat.of P.Coefficient P.Coefficient)) theta := by
  have : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  obtain ⟨⟨evalW, hw⟩, _⟩ := normalizationOpenDataAt P.Ring i
  obtain ⟨hz, ⟨hc⟩⟩ := fixedConstantPresentation P.Ring i
  exact normalizationEvaluation (Scheme.ProEt.topology X) P.Coefficient
    (MorphismProperty.Over.mkIdTerminal _ _) (supportRestrictionArrow i) _ _ _ _ hz hc
    evalW hw

end ProEtale

namespace Etale

private theorem normalizationTheta (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ theta : SupportedHomEvaluationIso X.smallEtaleTopology P.Coefficient
        (supportRestrictionArrow i)
        ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale Z)),
      SupportedHomEvaluation X.smallEtaleTopology P.Coefficient
        (MorphismProperty.Over.mkIdTerminal _ _) (supportRestrictionArrow i)
        ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale Z))
        (supportedHomConstantRestriction P.Coefficient i) theta := by
  obtain ⟨⟨evalW, hw⟩, _⟩ := normalizationOpenDataAt P.Coefficient i
  obtain ⟨hz, ⟨hc⟩⟩ := normalizationConstantPresentation P.Coefficient i
  exact normalizationEvaluation X.smallEtaleTopology P.Coefficient
    (MorphismProperty.Over.mkIdTerminal _ _) (supportRestrictionArrow i) _ _ _ _ hz hc
    evalW hw

end Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private noncomputable def normalizationBaseComponent
    {D : Type (u + 2)} [Category.{u + 1} D] [Abelian D]
    [HasDerivedCategory.{u + 1} D]
    (A : Type (u + 1)) [CommRing A]
    (S : D ⥤ ModuleCat.{u + 1} A) [S.Additive]
    (V : D ⥤ AddCommGrpCat.{u + 1}) [V.Additive]
    (theta : V ≅ S ⋙ forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) (a : ℤ)
    (K : HomotopyCategory.Plus (D)) :
    let G : ModuleCat.{u + 1} A ⥤ AddCommGrpCat.{u + 1} := forget₂ _ _
    ((S.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a ⋙ G)).obj K ≅
      ((V.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} a).obj K := by
  classical
  let G : ModuleCat.{u + 1} A ⥤ AddCommGrpCat.{u + 1} := forget₂ _ _
  let : PreservesColimitsOfSize.{u + 1, u + 1} G :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} A
  let : PreservesFiniteColimits G :=
    PreservesColimitsOfSize.preservesFiniteColimits.{u + 1, u + 1} G
  let H (a : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} a
  let HM (a : ℤ) := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a ⋙ G
  exact G.mapIso (DerivedCategory.Plus.homologyFunctorObjQIso
        (S.mapCochainComplexPlus.obj
          ⟨K.obj.as, (HomotopyCategory.plus_quotient_obj_iff _).mp K.2⟩) a) ≪≫
      ((G.mapHomologicalComplexHomologyIso (.up ℤ) a).app
        ((S.mapHomologicalComplex (.up ℤ)).obj K.obj.as)).symm ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) a).mapIso
        ((NatIso.mapHomologicalComplex theta.symm (.up ℤ)).app K.obj.as) ≪≫
      (DerivedCategory.Plus.homologyFunctorObjQIso
        (V.mapCochainComplexPlus.obj
          ⟨K.obj.as, (HomotopyCategory.plus_quotient_obj_iff _).mp K.2⟩) a).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private noncomputable def normalizationBaseIso
    {D : Type (u + 2)} [Category.{u + 1} D] [Abelian D]
    [HasDerivedCategory.{u + 1} D]
    (A : Type (u + 1)) [CommRing A]
    (S : D ⥤ ModuleCat.{u + 1} A) [S.Additive]
    (V : D ⥤ AddCommGrpCat.{u + 1}) [V.Additive]
    (theta : V ≅ S ⋙ forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) (a : ℤ) :
    let G : ModuleCat.{u + 1} A ⥤ AddCommGrpCat.{u + 1} := forget₂ _ _
    (S.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a ⋙ G) ≅
      (V.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} a := by
  classical
  let G : ModuleCat.{u + 1} A ⥤ AddCommGrpCat.{u + 1} := forget₂ _ _
  let : PreservesColimitsOfSize.{u + 1, u + 1} G :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} A
  let : PreservesFiniteColimits G :=
    PreservesColimitsOfSize.preservesFiniteColimits.{u + 1, u + 1} G
  let H (a : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} a
  let HM (a : ℤ) := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a ⋙ G
  let FS := (S.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙ HM a
  let FV := (V.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙ H a
  change FS ≅ FV
  refine NatIso.ofComponents (normalizationBaseComponent A S V theta a) ?_
  intro K L φ
  let f : K.obj.as ⟶ L.obj.as := Quot.out φ.hom
  have hf : (HomotopyCategory.quotient _ _).map f = φ.hom :=
    HomotopyCategory.quotient_map_out φ.hom
  let f' : (⟨K.obj.as, (HomotopyCategory.plus_quotient_obj_iff _).mp K.2⟩ :
      CochainComplex.Plus _) ⟶
      ⟨L.obj.as, (HomotopyCategory.plus_quotient_obj_iff _).mp L.2⟩ :=
    ObjectProperty.homMk f
  have hφ : φ = (HomotopyCategory.Plus.quotient _).map f' := by
    apply ObjectProperty.hom_ext
    exact hf.symm
  refine (congrArg (fun z ↦ FS.map z ≫ _) hφ).trans
    (Eq.trans ?_ (congrArg (fun z ↦ _ ≫ FV.map z) hφ.symm))
  unfold normalizationBaseComponent
  let K' : CochainComplex.Plus (D) :=
    ⟨K.obj.as, (HomotopyCategory.plus_quotient_obj_iff _).mp K.2⟩
  let L' : CochainComplex.Plus (D) :=
    ⟨L.obj.as, (HomotopyCategory.plus_quotient_obj_iff _).mp L.2⟩
  change G.map ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a).map
      (DerivedCategory.Plus.Q.map (S.mapCochainComplexPlus.map f'))) ≫
      (G.map (DerivedCategory.Plus.homologyFunctorObjQIso
        (S.mapCochainComplexPlus.obj L') a).hom ≫
      (G.mapHomologicalComplexHomologyIso (.up ℤ) a).inv.app
        ((S.mapHomologicalComplex (.up ℤ)).obj L'.obj) ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) a).map
        ((NatIso.mapHomologicalComplex theta.symm (.up ℤ)).hom.app L'.obj) ≫
      (DerivedCategory.Plus.homologyFunctorObjQIso
        (V.mapCochainComplexPlus.obj L') a).inv) =
    (G.map (DerivedCategory.Plus.homologyFunctorObjQIso
        (S.mapCochainComplexPlus.obj K') a).hom ≫
      (G.mapHomologicalComplexHomologyIso (.up ℤ) a).inv.app
        ((S.mapHomologicalComplex (.up ℤ)).obj K'.obj) ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) a).map
        ((NatIso.mapHomologicalComplex theta.symm (.up ℤ)).hom.app K'.obj) ≫
      (DerivedCategory.Plus.homologyFunctorObjQIso
        (V.mapCochainComplexPlus.obj K') a).inv) ≫
      (H a).map (DerivedCategory.Plus.Q.map (V.mapCochainComplexPlus.map f'))
  rw [Category.assoc, Category.assoc, Category.assoc]
  rw [← G.map_comp_assoc,
    DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality,
    G.map_comp, Category.assoc]
  have hnG := (G.mapHomologicalComplexHomologyIso (.up ℤ) a).inv.naturality
    ((S.mapHomologicalComplex (.up ℤ)).map f)
  change G.map (HomologicalComplex.homologyMap
      ((S.mapHomologicalComplex (.up ℤ)).map f) a) ≫ _ = _ at hnG
  erw [reassoc_of% hnG]
  erw [← Functor.map_comp_assoc,
    (NatIso.mapHomologicalComplex theta.symm (.up ℤ)).hom.naturality f,
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) a).map_comp]
  simp only [Category.assoc]
  have hq := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality
    (V.mapCochainComplexPlus.map f') a
  have hq' : HomologicalComplex.homologyMap
      (V.mapCochainComplexPlus.map f').hom a ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso
          (V.mapCochainComplexPlus.obj L') a).inv =
      (DerivedCategory.Plus.homologyFunctorObjQIso
        (V.mapCochainComplexPlus.obj K') a).inv ≫
        (H a).map (DerivedCategory.Plus.Q.map (V.mapCochainComplexPlus.map f')) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hq, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  erw [hq']

set_option backward.isDefEq.respectTransparency false in
private theorem normalizationBaseIso_app
    {D : Type (u + 2)} [Category.{u + 1} D] [Abelian D]
    [HasDerivedCategory.{u + 1} D]
    (A : Type (u + 1)) [CommRing A]
    (S : D ⥤ ModuleCat.{u + 1} A) [S.Additive]
    (V : D ⥤ AddCommGrpCat.{u + 1}) [V.Additive]
    (theta : V ≅ S ⋙ forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
    (I : CochainComplex.Plus (D)) (a : ℤ) :
    (normalizationBaseIso A S V theta a).app
        ((HomotopyCategory.Plus.quotient _).obj I) =
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).mapIso
          (DerivedCategory.Plus.homologyFunctorObjQIso
            (S.mapCochainComplexPlus.obj I) a) ≪≫
        (((forget₂ (ModuleCat.{u + 1} A)
          AddCommGrpCat.{u + 1}).mapHomologicalComplexHomologyIso (.up ℤ) a).app
            ((S.mapHomologicalComplex (.up ℤ)).obj I.obj)).symm ≪≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) a).mapIso
          ((NatIso.mapHomologicalComplex theta.symm (.up ℤ)).app I.obj) ≪≫
        (DerivedCategory.Plus.homologyFunctorObjQIso
          (V.mapCochainComplexPlus.obj I) a).symm := by
  unfold normalizationBaseIso normalizationBaseComponent
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizationBaseIso_cycle
    {D : Type (u + 2)} [Category.{u + 1} D] [Abelian D]
    [HasDerivedCategory.{u + 1} D] (A : Type (u + 1)) [CommRing A]
    (S : D ⥤ ModuleCat.{u + 1} A) [S.Additive]
    (V : D ⥤ AddCommGrpCat.{u + 1}) [V.Additive]
    (theta : V ≅ S ⋙ forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
    (I : CochainComplex.Plus D) (a : ℤ)
    (x : ((S.mapHomologicalComplex (.up ℤ)).obj I.obj).cycles a)
    (f : V.obj (I.obj.X a))
    (hf : (V.map (I.obj.d a (a + 1))) f = 0)
    (hftheta : theta.hom.app (I.obj.X a) f =
      ((S.mapHomologicalComplex (.up ℤ)).obj I.obj).iCycles a x) :
    let G : ModuleCat.{u + 1} A ⥤ AddCommGrpCat.{u + 1} := forget₂ _ _
    let SI := (S.mapHomologicalComplex (.up ℤ)).obj I.obj
    let VI := (V.mapHomologicalComplex (.up ℤ)).obj I.obj
    let y : VI.cycles a := (VI.sc a).abCyclesIso.inv ⟨f, by
      change V.map (I.obj.d a ((ComplexShape.up ℤ).next a)) f = 0
      rw [CochainComplex.next]
      exact hf⟩
    (normalizationBaseIso A S V theta a).hom.app ((HomotopyCategory.Plus.quotient _).obj I)
        (G.map (DerivedCategory.Plus.homologyFunctorObjQIso
          (S.mapCochainComplexPlus.obj I) a).inv (SI.homologyπ a x)) =
        (DerivedCategory.Plus.homologyFunctorObjQIso
          (V.mapCochainComplexPlus.obj I) a).inv (VI.homologyπ a y) := by
  classical
  dsimp only
  let G : ModuleCat.{u + 1} A ⥤ AddCommGrpCat.{u + 1} := forget₂ _ _
  let : PreservesColimitsOfSize.{u + 1, u + 1} G :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} A
  let : PreservesFiniteColimits G :=
    PreservesColimitsOfSize.preservesFiniteColimits.{u + 1, u + 1} G
  let SI := (S.mapHomologicalComplex (.up ℤ)).obj I.obj
  let VI := (V.mapHomologicalComplex (.up ℤ)).obj I.obj
  let y : VI.cycles a := (VI.sc a).abCyclesIso.inv ⟨f, by
    change V.map (I.obj.d a ((ComplexShape.up ℤ).next a)) f = 0
    rw [CochainComplex.next]
    exact hf⟩
  change ((normalizationBaseIso A S V theta a).app
    ((HomotopyCategory.Plus.quotient _).obj I)).hom _ = _
  rw [normalizationBaseIso_app]
  simp only [Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, AddCommGrpCat.comp_apply]
  have hcancel : G.map
      (DerivedCategory.Plus.homologyFunctorObjQIso
        (S.mapCochainComplexPlus.obj I) a).hom
      (G.map (DerivedCategory.Plus.homologyFunctorObjQIso
        (S.mapCochainComplexPlus.obj I) a).inv (SI.homologyπ a x)) =
      SI.homologyπ a x :=
    Iso.inv_hom_id_apply (G.mapIso (DerivedCategory.Plus.homologyFunctorObjQIso
      (S.mapCochainComplexPlus.obj I) a)) _
  erw [hcancel]
  apply congrArg (DerivedCategory.Plus.homologyFunctorObjQIso
    (V.mapCochainComplexPlus.obj I) a).inv
  let GI := (G.mapHomologicalComplex (.up ℤ)).obj SI
  let x' : GI.cycles a := ((SI.sc a).mapCyclesIso G).inv x
  have hx' : GI.iCycles a x' = SI.iCycles a x := by
    change (((SI.sc a).mapCyclesIso G).inv ≫ GI.iCycles a) x = _
    exact congrArg (fun g ↦ g x) ((SI.sc a).mapCyclesIso_inv_iCycles G)
  have hforget : (G.mapHomologicalComplexHomologyIso (.up ℤ) a).inv.app SI
      (SI.homologyπ a x) = GI.homologyπ a x' := by
    have h := (SI.sc a).homologyπ_comp_mapHomologyIso_hom G
    have hx := congrArg (fun g ↦ g x') h
    change _ = _ at hx
    let e := Iso.addCommGroupIsoToAddEquiv
      ((G.mapHomologicalComplexHomologyIso (.up ℤ) a).app SI)
    apply e.injective
    change (G.mapHomologicalComplexHomologyIso (.up ℤ) a).hom.app SI
      ((G.mapHomologicalComplexHomologyIso (.up ℤ) a).inv.app SI
        (SI.homologyπ a x)) =
      (G.mapHomologicalComplexHomologyIso (.up ℤ) a).hom.app SI (GI.homologyπ a x')
    erw [Iso.inv_hom_id_apply ((G.mapHomologicalComplexHomologyIso (.up ℤ) a).app SI)]
    have hμ : (G.mapHomologicalComplexHomologyIso (.up ℤ) a).hom.app SI =
        ((SI.sc a).mapHomologyIso G).hom := by
      exact Functor.mapHomologicalComplexHomologyIso_hom_app_eq (.up ℤ) a G SI
    rw [hμ]
    simpa only [AddCommGrpCat.comp_apply, x', Iso.inv_hom_id_apply] using! hx.symm
  erw [hforget]
  erw [← AddCommGrpCat.comp_apply, HomologicalComplex.homologyπ_naturality,
    AddCommGrpCat.comp_apply]
  apply congrArg (VI.homologyπ a)
  apply (AddCommGrpCat.mono_iff_injective (VI.iCycles a)).mp inferInstance
  rw [← AddCommGrpCat.comp_apply, HomologicalComplex.cyclesMap_i,
    AddCommGrpCat.comp_apply]
  change theta.inv.app (I.obj.X a) (GI.iCycles a x') = VI.iCycles a y
  rw [hx']
  have ht : theta.inv.app (I.obj.X a) (SI.iCycles a x) = f := by
    rw [← hftheta]
    exact (theta.app (I.obj.X a)).addCommGroupIsoToAddEquiv.symm_apply_apply f
  rw [ht]
  exact (ShortComplex.abCyclesIso_inv_apply_iCycles (VI.sc a) ⟨f, by
    change V.map (I.obj.d a ((ComplexShape.up ℤ).next a)) f = 0
    rw [CochainComplex.next]
    exact hf⟩).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizationRHom
    {D : Type (u + 2)} [Category.{u + 1} D] [Abelian D]
    [EnoughInjectives D] [HasDerivedCategory.{u + 1} D] (B : D) :
    ∃ psi : ∀ (F : DerivedCategory.Plus D) (a : ℤ),
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} a).obj
          ((preadditiveCoyoneda.obj (op B)).rightDerivedFunctorPlus.obj F) ≃+
          ((DerivedCategory.singleFunctor D 0).obj B ⟶ F.obj⟦a⟧),
      (∀ (F G : DerivedCategory.Plus D) (v : F ⟶ G) (a : ℤ) (x),
        psi G a ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} a).map
          ((preadditiveCoyoneda.obj (op B)).rightDerivedFunctorPlus.map v) x) =
          psi F a x ≫ (DerivedCategory.Plus.ι.map v)⟦a⟧') ∧
      (∀ (I : CochainComplex.Plus D) (hi : ∀ n : ℤ, Injective (I.obj.X n))
          (a : ℤ) (f : B ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0),
        let V := preadditiveCoyoneda.obj (op B)
        let VI := (V.mapHomologicalComplex (.up ℤ)).obj I.obj
        let y : VI.cycles a := (VI.sc a).abCyclesIso.inv ⟨f, by
          change f ≫ I.obj.d a ((ComplexShape.up ℤ).next a) = 0
          rw [CochainComplex.next]
          exact hf⟩
        psi (DerivedCategory.Plus.Q.obj I) a
          ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} a).map
            (V.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient _).obj I))
            ((DerivedCategory.Plus.homologyFunctorObjQIso
              (V.mapCochainComplexPlus.obj I) a).inv (VI.homologyπ a y))) =
          ShiftedHom.map (Cocycle.equivHomShift.symm
            (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
            ((DerivedCategory.quotientCompQhIso D).hom.app I.obj)⟦a⟧') := by
  classical
  obtain ⟨psi, hnat, hroof⟩ := Functor.exists_rhom_hom_derived_roof B
  refine ⟨psi, hnat, ?_⟩
  intro I hi a f hf
  let := hi
  dsimp only
  obtain ⟨n, hn⟩ := I.2
  let := hn
  let r : CochainComplex.KInjectiveResolutionChoice I.obj :=
    { complex := I.obj
      map := 𝟙 I.obj
      quasiIso := inferInstance
      isKInjective := CochainComplex.isKInjective_of_injective I.obj n }
  have hr := hroof I r I.2 hi a f hf
  have : IsIso (DerivedCategory.Q.map (𝟙 I.obj)) := by
    rw [DerivedCategory.Q.map_id]
    infer_instance
  have hei : (DerivedCategory.Plus.ι (C := D)).preimageIso
      (X := DerivedCategory.Plus.Q.obj I) (Y := DerivedCategory.Plus.Q.obj I)
      ((DerivedCategory.Plus.QCompιIso D).app I ≪≫
        asIso (DerivedCategory.Q.map (𝟙 I.obj)) ≪≫
        (DerivedCategory.Plus.QCompιIso D).symm.app I) = Iso.refl _ := by
    apply Iso.ext
    apply DerivedCategory.Plus.ι.map_injective
    change DerivedCategory.Plus.ι.map (DerivedCategory.Plus.ι.preimage _) = 𝟙 _
    rw [Functor.map_preimage]
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, asIso_hom]
    simp [DerivedCategory.Plus.QCompιIso_hom_app,
      DerivedCategory.Plus.QCompιIso_inv_app]; rfl
  dsimp only [r] at hr
  rw [hei] at hr
  simp only [Iso.refl_inv] at hr
  erw [(preadditiveCoyoneda.obj (op B)).rightDerivedFunctorPlus.map_id,
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} a).map_id,
    AddCommGrpCat.id_apply] at hr
  have hid : inv (DerivedCategory.Q.map (𝟙 I.obj)) = 𝟙 _ := by
    apply (cancel_mono (DerivedCategory.Q.map (𝟙 I.obj))).mp
    erw [IsIso.inv_hom_id, Category.id_comp, DerivedCategory.Q.map_id]
  erw [hid, (shiftFunctor (DerivedCategory D) a).map_id, Category.id_comp] at hr
  have hq : (DerivedCategory.quotientCompQhIso D).hom.app I.obj = 𝟙 _ :=
    CategoryTheory.Quotient.lift.isLift_hom _ _ _ I.obj
  rw [hq]
  erw [(shiftFunctor (DerivedCategory D) a).map_id]
  have hunit : (preadditiveCoyoneda.obj (op B)).rightDerivedFunctorPlusUnit.app I =
      (preadditiveCoyoneda.obj (op B)).rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient _).obj I) := by
    have hs : (DerivedCategory.Plus.quotientCompQhIso AddCommGrpCat.{u + 1}).inv.app
        ((preadditiveCoyoneda.obj (op B)).mapCochainComplexPlus.obj I) = 𝟙 _ := by
      apply DerivedCategory.Plus.ι.map_injective
      exact CategoryTheory.Quotient.lift.isLift_inv _ _ _ _
    have ht : (DerivedCategory.Plus.quotientCompQhIso D).hom.app I = 𝟙 _ := by
      apply DerivedCategory.Plus.ι.map_injective
      exact CategoryTheory.Quotient.lift.isLift_hom _ _ _ _
    rw [Functor.rightDerivedFunctorPlusUnit_app, hs, ht]
    simp only [Functor.quotientCompMapHomotopyCategoryPlusIso, Iso.refl_inv,
      NatTrans.id_app]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.id_comp, Category.comp_id]
  rw [hunit] at hr
  simpa only [Functor.rightDerivedComplexWithResolution,
      Functor.mapCochainComplexPlus, DerivedCategory.Plus.QCompιIso_inv_app,
      CategoryTheory.Functor.map_id] using! hr

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizationDerivedComparison
    {D : Type (u + 2)} [Category.{u + 1} D] [Abelian D]
    [EnoughInjectives D] [HasDerivedCategory.{u + 1} D]
    (A : Type (u + 1)) [CommRing A]
    (S : D ⥤ ModuleCat.{u + 1} A) [S.Additive] (B : D)
    (theta : preadditiveCoyoneda.obj (op B) ≅
      S ⋙ forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) :
    let G : ModuleCat.{u + 1} A ⥤ AddCommGrpCat.{u + 1} := forget₂ _ _
    let HM (a : ℤ) := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a ⋙ G
    let RS (a : ℤ) := S.rightDerivedFunctorPlus ⋙ HM a
    let αS (a : ℤ) := Functor.whiskerRight S.rightDerivedFunctorPlusUnith (HM a) ≫
      (Functor.associator _ _ _).hom
    ∃ chi : ∀ (F : DerivedCategory.Plus D) (a : ℤ), (RS a).obj F ≃+
        ((DerivedCategory.singleFunctor D 0).obj B ⟶ F.obj⟦a⟧),
      (∀ (F F' : DerivedCategory.Plus D) (v : F ⟶ F') (a : ℤ) (x),
        chi F' a ((RS a).map v x) = chi F a x ≫ (DerivedCategory.Plus.ι.map v)⟦a⟧') ∧
      (∀ (I : CochainComplex.Plus D) (hi : ∀ n : ℤ, Injective (I.obj.X n))
          (F : DerivedCategory.Plus D) (eI : F ≅ DerivedCategory.Plus.Q.obj I) (a : ℤ)
          (x : ((S.mapHomologicalComplex (.up ℤ)).obj I.obj).cycles a),
        ∃! f : B ⟶ I.obj.X a,
          theta.hom.app (I.obj.X a) f =
            ((S.mapHomologicalComplex (.up ℤ)).obj I.obj).iCycles a x ∧
          ∃ hf : f ≫ I.obj.d a (a + 1) = 0,
            chi F a
              ((RS a).map eI.inv ((αS a).app ((HomotopyCategory.Plus.quotient _).obj I)
                (G.map (DerivedCategory.Plus.homologyFunctorObjQIso
                  (S.mapCochainComplexPlus.obj I) a).inv
                    (((S.mapHomologicalComplex (.up ℤ)).obj I.obj).homologyπ a x)))) =
              supportedHomLocalizedCocycle I.obj a f hf ≫
                (DerivedCategory.Plus.ι.map eI.inv)⟦a⟧') := by
  classical
  let G : ModuleCat.{u + 1} A ⥤ AddCommGrpCat.{u + 1} := forget₂ _ _
  let : PreservesColimitsOfSize.{u + 1, u + 1} G :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} A
  let : PreservesFiniteColimits G :=
    PreservesColimitsOfSize.preservesFiniteColimits.{u + 1, u + 1} G
  let V := preadditiveCoyoneda.obj (op B)
  let H (a : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} a
  let HM (a : ℤ) := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a ⋙ G
  let RS (a : ℤ) := S.rightDerivedFunctorPlus ⋙ HM a
  let RV (a : ℤ) := V.rightDerivedFunctorPlus ⋙ H a
  let αS (a : ℤ) := Functor.whiskerRight S.rightDerivedFunctorPlusUnith (HM a) ≫
    (Functor.associator _ _ _).hom
  let αV (a : ℤ) := Functor.whiskerRight V.rightDerivedFunctorPlusUnith (H a) ≫
    (Functor.associator _ _ _).hom
  let baseIso (a : ℤ) := normalizationBaseIso A S V theta a
  let eH (a : ℤ) : RS a ≅ RV a :=
    Functor.rightDerivedNatIso (RS a) (RV a) (αS a) (αV a)
      (HomotopyCategory.Plus.quasiIso _) (baseIso a)
  obtain ⟨psi, hnat, hroof⟩ := normalizationRHom B
  let chi : ∀ (F : DerivedCategory.Plus D) (a : ℤ), (RS a).obj F ≃+
      ((DerivedCategory.singleFunctor D 0).obj B ⟶ F.obj⟦a⟧) := fun F a ↦
    ((eH a).app F).addCommGroupIsoToAddEquiv.trans (psi F a)
  have hchi : ∀ (F F' : DerivedCategory.Plus D) (v : F ⟶ F') (a : ℤ) (x),
      chi F' a ((RS a).map v x) = chi F a x ≫ (DerivedCategory.Plus.ι.map v)⟦a⟧' := by
    intro F F' f a x
    change psi F' a ((eH a).hom.app F'
      ((RS a).map f x)) = _
    have h := congrArg (fun g ↦ g x) ((eH a).hom.naturality f)
    change _ = _ at h
    change (eH a).hom.app F' ((RS a).map f x) =
      (RV a).map f ((eH a).hom.app F x) at h
    exact (congrArg (psi F' a) h).trans (hnat F F' f a _)
  refine ⟨chi, hchi, ?_⟩
  intro I hi F eI a x
  let SI := (S.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj
  let f : B ⟶ I.obj.X a := (theta.app (I.obj.X a)).addCommGroupIsoToAddEquiv.symm
    (SI.iCycles a x)
  have hftheta : theta.hom.app (I.obj.X a) f = SI.iCycles a x := by
    exact (theta.app (I.obj.X a)).addCommGroupIsoToAddEquiv.apply_symm_apply _
  have hf : f ≫ I.obj.d a (a + 1) = 0 := by
    apply (theta.app (I.obj.X (a + 1))).addCommGroupIsoToAddEquiv.injective
    have h := congrArg (fun g ↦ g f) (theta.hom.naturality (I.obj.d a (a + 1)))
    change theta.hom.app _ (f ≫ I.obj.d a (a + 1)) = S.map _ _ at h
    change theta.hom.app _ (f ≫ I.obj.d a (a + 1)) = theta.hom.app _ 0
    erw [h, hftheta]
    have hx := congrArg (fun g ↦ g x) (SI.iCycles_d a (a + 1))
    rw [map_zero]
    change SI.d a (a + 1) (SI.iCycles a x) = 0
    simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using hx
  refine ⟨f, ⟨hftheta, hf, ?_⟩, ?_⟩
  · let VI := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj
    let y : VI.cycles a := (VI.sc a).abCyclesIso.inv ⟨f, by
      change f ≫ I.obj.d a ((ComplexShape.up ℤ).next a) = 0
      rw [CochainComplex.next]
      exact hf⟩
    have hclass := normalizationBaseIso_cycle A S V theta I a x f (by exact hf) hftheta
    have hfac := Functor.rightDerivedNatTrans_app (RS a) (RV a) (αS a) (αV a)
      (HomotopyCategory.Plus.quasiIso _) (baseIso a).hom
      ((HomotopyCategory.Plus.quotient _).obj I)
    have hcompat : (eH a).hom.app F
        ((RS a).map eI.inv ((αS a).app ((HomotopyCategory.Plus.quotient _).obj I)
          (G.map (DerivedCategory.Plus.homologyFunctorObjQIso
            (S.mapCochainComplexPlus.obj I) a).inv (SI.homologyπ a x)))) =
        (H a).map (V.rightDerivedFunctorPlus.map eI.inv)
          ((H a).map (V.rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient _).obj I))
            ((DerivedCategory.Plus.homologyFunctorObjQIso
              (V.mapCochainComplexPlus.obj I) a).inv (VI.homologyπ a y))) := by
      have hn := (eH a).hom.naturality eI.inv
      have hfacx := congrArg (fun g ↦ g
        (G.map (DerivedCategory.Plus.homologyFunctorObjQIso
          (S.mapCochainComplexPlus.obj I) a).inv (SI.homologyπ a x))) hfac
      change _ = _ at hfacx
      change ((RS a).map eI.inv ≫ (eH a).hom.app _) _ = _
      rw [hn]
      change (RV a).map eI.inv ((eH a).hom.app _ _) = _
      apply congrArg ((RV a).map eI.inv)
      change (eH a).hom.app (DerivedCategory.Plus.Q.obj I)
        ((αS a).app ((HomotopyCategory.Plus.quotient _).obj I)
          (G.map (DerivedCategory.Plus.homologyFunctorObjQIso
            (S.mapCochainComplexPlus.obj I) a).inv (SI.homologyπ a x))) = _ at hfacx
      exact hfacx.trans (congrArg
        ((αV a).app ((HomotopyCategory.Plus.quotient _).obj I)) hclass)
    change psi _ a ((eH a).hom.app _ _) = _
    rw [hcompat, hnat]
    have hr' := hroof I hi a f hf
    rw [hr', supportedHomLocalizedCocycle_eq]
    have hq : (DerivedCategory.quotientCompQhIso
        D).hom.app I.obj = 𝟙 _ :=
      CategoryTheory.Quotient.lift.isLift_hom _ _ _ I.obj
    rw [hq]
    erw [(shiftFunctor (DerivedCategory D) a).map_id, Category.comp_id]
  · intro f' hf'
    apply (theta.app (I.obj.X a)).addCommGroupIsoToAddEquiv.injective
    exact hf'.1.trans hftheta.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizationChi
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    [HasDerivedCategory.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    {T W : C} (j : W ⟶ T) (B : Sheaf J (ModuleCat.{u + 1} A))
    (theta : SupportedHomEvaluationIso J A j B) :
    ∃ chi : SupportedHomChi J A j B,
      SupportedHomChiNatural J A j B chi ∧ SupportedHomChiCocycle J A j B theta chi := by
  obtain ⟨chi, hn, hc⟩ := normalizationDerivedComparison A
    (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) B theta
  refine ⟨chi, hn, ?_⟩
  intro K I hi e he a x
  obtain ⟨f, ⟨hfθ, hf, hr⟩, hu⟩ := hc I hi (DerivedCategory.Plus.Q.obj K)
    (supportedHomResolutionIso J A K I e) a x
  refine ⟨f, ⟨hfθ, hf, ?_⟩, ?_⟩
  · have hq : (DerivedCategory.Plus.QCompιIso
        (Sheaf J (ModuleCat.{u + 1} A))).inv.app I = 𝟙 _ := by rfl
    rw [hq]
    erw [(shiftFunctor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) a).map_id,
      Category.id_comp]
    have hs : (DerivedCategory.Plus.quotientCompQhIso (ModuleCat.{u + 1} A)).inv.app
        ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj
          I) = 𝟙 _ := by
      apply DerivedCategory.Plus.ι.map_injective
      exact CategoryTheory.Quotient.lift.isLift_inv _ _ _ _
    have ht : (DerivedCategory.Plus.quotientCompQhIso
        (Sheaf J (ModuleCat.{u + 1} A))).hom.app I = 𝟙 _ := by
      apply DerivedCategory.Plus.ι.map_injective
      exact CategoryTheory.Quotient.lift.isLift_hom _ _ _ _
    simp only [Sheaf.supportSequenceModelIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, asIso_hom, Iso.app_hom, Iso.app_inv, hs, ht,
      Functor.quotientCompMapHomotopyCategoryPlusIso, Iso.refl_inv, NatTrans.id_app,
      Category.id_comp]
    repeat first
      | erw [CategoryTheory.Functor.map_id]
      | erw [Category.id_comp]
      | erw [Category.comp_id]
    exact hr
  · intro f' hf'
    apply (theta.app (I.obj.X a)).addCommGroupIsoToAddEquiv.injective
    exact hf'.1.trans hfθ.symm

private theorem normalizationConeAgreement
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    [HasDerivedCategory.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    {T W : C} (hT : IsTerminal T) (j : W ⟶ T) [Mono j]
    (B : Sheaf J (ModuleCat.{u + 1} A))
    (rho : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B)
    (N : SupportedHomCocycleNormalization J A hT j B rho) : N.ConeAgreement := by
  intro I hi
  let a := ((supportedHomAbelianInclusion J A j).mapHomologicalComplex
    (ComplexShape.up ℤ)).app I.obj
  let r := ((supportedHomAbelianRestriction J A j).mapHomologicalComplex
    (ComplexShape.up ℤ)).app I.obj
  have hz : a ≫ r = 0 := by
    ext n : 1
    change (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat).map
      (kernel.ι ((I.obj.X n).obj.map j.op)) ≫
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat).map
          ((I.obj.X n).obj.map j.op) = 0
    rw [← Functor.map_comp, kernel.condition, Functor.map_zero]
  have hs : (ShortComplex.mk a r hz).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    have : Epi ((I.obj.X n).obj.map j.op) := supportModule_restriction_epi J A _ j
    let S := ShortComplex.mk (kernel.ι ((I.obj.X n).obj.map j.op))
      ((I.obj.X n).obj.map j.op) (kernel.condition _)
    have hS : S.ShortExact :=
      { exact := ShortComplex.kernelSequence_exact _
        mono_f := inferInstance
        epi_g := inferInstance }
    exact hS.map (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat)
  have : HasDerivedCategory AddCommGrpCat.{u + 1} :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  have hq := CochainComplex.closedConeLift_quasiIso (ShortComplex.mk a r hz) hs
  refine ⟨hz, hq, ?_⟩
  have := hq
  infer_instance

private theorem normalizationAssemble
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    [HasDerivedCategory.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    {T W : C} (hT : IsTerminal T) (j : W ⟶ T) (B : Sheaf J (ModuleCat.{u + 1} A))
    (rho : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B)
    (theta : SupportedHomEvaluationIso J A j B)
    (he : SupportedHomEvaluation J A hT j B rho theta) :
    Nonempty (SupportedHomCocycleNormalization J A hT j B rho) := by
  obtain ⟨chi, hn, hc⟩ := normalizationChi J A j B theta
  exact ⟨⟨theta, he, chi, hn, hc⟩⟩

/-- Evaluation at one and the injective-resolution roof normalize supported Hom in
both topologies. On the etale site the comparison to the shifted restriction cone is
inclusion of the evaluated support kernel in the shifted source summand.

Source: Milne, Lectures on Etale Cohomology, Section 9, Example 9.5 and the Ext proof
of Theorem 9.4, pp. 66--67; blueprint lemma-cycle-class-cartier-divisor, Hom triangle proof
(blueprint: lem-pur-supported-hom-cocycle-normalization).

Proof, following the ten recorded DAG steps:
1. Use small representatives in the coefficient universe. Ordinary ModuleCat-valued
   sheaves are Grothendieck abelian and have enough injectives by the existing sheaf
   instances. Derive in module sheaves, without assuming that forgetting scalar
   action preserves injectives.
2. Evaluation g ↦ g(1) identifies Hom(A_X,M) with M(X). Its inverse sends a section m
   to the map b ↦ b m|_V on each site object V. Semilinearity proves restriction
   compatibility and both inverse identities. The same construction applies over U.
3. The open adjunction identifies the adjunct of g composed with its counit with the
   restriction of g. Evaluation therefore gives precisely restriction of g(1), with
   no scalar factor or sign, as expressed by SupportedHomOpenEvaluation.
4. Use lem-weil-pbc-open-closed-short-exact and the canonical constant pullback on
   the etale site, or lem-pur-proetale-supported-constant-presentation on the pro-etale
   site. The actual constant restriction rho is the cokernel of the open counit.
   Each supported section thus gives a unique factorization f through rho.
   Uniqueness proves additivity and naturality, and fixes theta by evaluation.
5. Apply theta inverse termwise. Naturality for each differential makes this an
   isomorphism of complexes. Supported cocycles go to Hom cocycles; supported
   boundaries go to Hom boundaries.
6. Derive theta inverse using lem-weil-pbc-right-derived-plus-injective and its
   universal property. The inverse derives in the same way; uniqueness makes their
   composites identities. Naturality of the derived units identifies the comparison
   on any specified resolution with the actual unit followed by inverse R(Qe).
7. A bounded-below complex of injectives is K-injective. Apply
   lem-sc-p1-rhom-hom-derived-roof with M=i_*A_Z to obtain exactly the localized
   cocycle map followed by inverse shifted Qe. No sign enters its sole component.
8. Naturality of both comparisons gives naturality of chi. The construction is on
   cohomology before a resolution is chosen; the formula holds for every e and every
   cocycle. Changing a cocycle by a boundary therefore gives the same value, and the
   canonical derived-unit transports compare any two resolutions, also in negative degrees.
9. Restriction of an injective module sheaf along a monomorphism of site objects is
   epic. Sheafification is exact, so its right adjoint preserves injectives. Extend
   a map from the free module presheaf on the smaller representable to the larger
   one and evaluate at the identity. This proves degreewise short exactness of the
   support kernel, total sections and open sections. Forgetting coefficients is exact.
10. Apply closedConeLift_quasiIso from lemma-cycle-class-cartier-divisor to this short exact
   sequence. The canonical support inclusion into the shifted restriction cone is
   a quasi-isomorphism, as is its composite with the termwise evaluation isomorphism.
   This proves exactly ConeAgreement. No quasi-compactness, constructibility,
   finite-Tor or purity hypothesis is used. -/
theorem supportedHom_cocycle_normalization (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ e : Etale.supportedHomNormalization P i,
      Nonempty (ProEtale.supportedHomNormalization P i) ∧ e.ConeAgreement ∧
      Etale.SupportedHomOpenEvaluation P.Coefficient i.openComplement.ι ∧
      ProEtale.SupportedHomOpenEvaluation P.Ring i.openComplement.ι := by
  obtain ⟨thetaE, he⟩ := Etale.normalizationTheta P i
  obtain ⟨e⟩ := normalizationAssemble X.smallEtaleTopology P.Coefficient
    (MorphismProperty.Over.mkIdTerminal _ _) (Etale.supportRestrictionArrow i) _ _ thetaE he
  obtain ⟨thetaP, hp⟩ := ProEtale.normalizationTheta P i
  have hP := normalizationAssemble (Scheme.ProEt.topology X) P.Coefficient
    (MorphismProperty.Over.mkIdTerminal _ _) (ProEtale.supportRestrictionArrow i) _ _ thetaP hp
  have : Mono (Etale.supportRestrictionArrow i) :=
    (MorphismProperty.Over.forget @Etale ⊤ X ⋙ Over.forget X).mono_of_mono_map
      (inferInstanceAs (Mono i.openComplement.ι))
  have hc := normalizationConeAgreement _ _ _ _ _ _ e
  exact ⟨e, hP, hc, (Etale.normalizationOpenDataAt _ i).2,
    (ProEtale.normalizationOpenDataAt _ i).2⟩

end AlgebraicGeometry
