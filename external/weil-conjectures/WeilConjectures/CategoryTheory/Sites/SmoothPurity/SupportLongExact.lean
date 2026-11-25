/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.CategoryTheory.Derived.DerivedInjectiveBoundary
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction

/-!
# The long exact sequence of cohomology with support

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4;
Stacks Project, Tags 093X, 03F3, 0117, 070I
(blueprint: thm-pur-with-support-exactness).
-/

@[expose] public section

set_option autoImplicit false

universe c v a w u d e

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type a) [Category.{w} A] [Abelian A]
variable {V W : C} (j : W ⟶ V)

/-- Inclusion of the kernel of restriction into sections on `V`.
Source: Milne, Section 9, definition before Theorem 9.4
(blueprint: thm-pur-with-support-exactness). -/
noncomputable def supportedSectionsInclusion :
    supportedSectionsFunctor J A j ⟶ (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V)) where
  app F := kernel.ι (F.obj.map j.op)
  naturality f := by simp [supportedSectionsFunctor]

variable [HasSheafify J A]
variable [EnoughInjectives (Sheaf J A)] [HasDerivedCategory (Sheaf J A)]
variable [HasDerivedCategory A]

/-- Derived evaluation on an object of a site, followed by integer-indexed cohomology.
For a terminal object this is global hypercohomology; for the open object it is
hypercohomology of the localized site. Source: Stacks, Tag 03F3
(blueprint: thm-pur-with-support-exactness). -/
noncomputable abbrev sectionHypercohomologyFunctor (V : C) (q : ℤ) :
    DerivedCategory.Plus (Sheaf J A) ⥤ A :=
  (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V)).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor A q

/-- Derived supported sections followed by cohomology: this specializes exactly to
`Etale.supportHypercohomology` and `ProEtale.supportHypercohomology`.
Source: the support definition and Milne, Section 9, Theorem 9.4
(blueprint: thm-pur-with-support-exactness). -/
noncomputable abbrev supportHypercohomologyFunctor (q : ℤ) :
    DerivedCategory.Plus (Sheaf J A) ⥤ A :=
  (supportedSectionsFunctor J A j).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor A q

/-- The canonical first arrow in the support sequence, obtained by deriving kernel inclusion.
Source: Milne, Section 9, Theorem 9.4 (blueprint: thm-pur-with-support-exactness). -/
noncomputable def supportHypercohomologyInclusion (q : ℤ) :
    supportHypercohomologyFunctor J A j q ⟶ sectionHypercohomologyFunctor J A V q :=
  Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatTrans
    (supportedSectionsInclusion J A j)) (DerivedCategory.Plus.homologyFunctor A q)

/-- The canonical second arrow in the support sequence, obtained by deriving restriction.
Source: Milne, Section 9, Theorem 9.4 (blueprint: thm-pur-with-support-exactness). -/
noncomputable def sectionHypercohomologyRestriction (q : ℤ) :
    sectionHypercohomologyFunctor J A V q ⟶ sectionHypercohomologyFunctor J A W q :=
  Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatTrans
    (F := sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V))
    (G := sheafToPresheaf J A ⋙ (evaluation _ _).obj (op W))
    ((sheafSections J A).map j.op)) (DerivedCategory.Plus.homologyFunctor A q)

/-- The canonical cohomology comparison from a bounded-below injective representative,
including its specified identification with the derived object. Source: Stacks, Tags 05TI,
05TH and 070I (blueprint: thm-pur-with-support-exactness). -/
noncomputable def supportSequenceModelIso (E : Sheaf J A ⥤ A) [E.Additive]
    (I : CochainComplex.Plus (Sheaf J A)) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : DerivedCategory.Plus (Sheaf J A)) (e : DerivedCategory.Plus.Q.obj I ≅ K)
    (q : ℤ) :
    ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).obj
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj)) ≅
      (E.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q).obj K :=
  (DerivedCategory.Plus.homologyFunctorObjQIso
    (E.mapCochainComplexPlus.obj I) q).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor A q).mapIso
      (((DerivedCategory.Plus.quotientCompQhIso A).app (E.mapCochainComplexPlus.obj I)).symm ≪≫
        DerivedCategory.Plus.Qh.mapIso (E.quotientCompMapHomotopyCategoryPlusIso.app I).symm ≪≫
        asIso (E.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient _).obj I)) ≪≫
        E.rightDerivedFunctorPlus.mapIso ((DerivedCategory.Plus.quotientCompQhIso _).app I)) ≪≫
    (E.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q).mapIso e

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type a) [Category.{w} A] [Abelian A] [HasSheafify J A]
variable [EnoughInjectives (Sheaf J A)] [HasDerivedCategory (Sheaf J A)]
variable [HasDerivedCategory A] {V W : C} (j : W ⟶ V)
variable (P : ObjectProperty (DerivedCategory.Plus (Sheaf J A)))

/-- A family of boundary maps natural in the permitted derived coefficients.
Source: Milne, Section 9, Theorem 9.4 (blueprint: thm-pur-with-support-exactness). -/
abbrev SupportSequenceBoundary :=
  ∀ q : ℤ, P.ι ⋙ sectionHypercohomologyFunctor J A W q ⟶
    P.ι ⋙ supportHypercohomologyFunctor J A j (q + 1)

/-- Exactness at all three places, in all integer degrees, of the displayed sequence.
The other two maps are the derived kernel inclusion and restriction, not existential maps.
Source: Milne, Section 9, Theorem 9.4 (blueprint: thm-pur-with-support-exactness). -/
def SupportSequenceExact (δ : SupportSequenceBoundary J A j P) : Prop :=
  ∀ (K : P.FullSubcategory) (q : ℤ),
    ∃ (w₁ : (supportHypercohomologyInclusion J A j q).app K.obj ≫
        (sectionHypercohomologyRestriction J A j q).app K.obj = 0)
      (w₂ : (sectionHypercohomologyRestriction J A j q).app K.obj ≫ (δ q).app K = 0)
      (w₃ : (δ q).app K ≫ (supportHypercohomologyInclusion J A j (q + 1)).app K.obj = 0),
      (ShortComplex.mk _ _ w₁).Exact ∧ (ShortComplex.mk _ _ w₂).Exact ∧
        (ShortComplex.mk _ _ w₃).Exact

/-- The boundary on a specified injective representative, transported by the canonical
right-derived-functor unit. Source: Stacks, Tags 05TI, 05TH, 0117
(blueprint: thm-pur-with-support-exactness). -/
noncomputable def supportSequenceModelBoundary (δ : SupportSequenceBoundary J A j P)
    (I : CochainComplex.Plus (Sheaf J A)) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : P.FullSubcategory) (e : DerivedCategory.Plus.Q.obj I ≅ K.obj) (q : ℤ) :
    ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).obj
      (((sheafToPresheaf J A ⋙ (evaluation _ _).obj (op W)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.obj)) ⟶
    ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) (q + 1)).obj
      (((supportedSectionsFunctor J A j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.obj)) :=
  (supportSequenceModelIso J A
    (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op W)) I K.obj e q).hom ≫
    (δ q).app K ≫
    (supportSequenceModelIso J A (supportedSectionsFunctor J A j) I K.obj e (q + 1)).inv

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

variable {C D : Type c} [Category.{v} C] [Category.{v} D]
variable (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
variable (A : Type a) [Category.{w} A] [Abelian A]
variable (B : C ⥤ D) [hB : B.IsContinuous J J']

variable [HasSheafify J A] [HasSheafify J' A]
variable [EnoughInjectives (Sheaf J A)] [EnoughInjectives (Sheaf J' A)]
variable [HasDerivedCategory (Sheaf J A)] [HasDerivedCategory (Sheaf J' A)]
variable [HasDerivedCategory A] {V W : C} (j : W ⟶ V) {V' W' : D} (j' : W' ⟶ V')
variable (P : ObjectProperty (DerivedCategory.Plus (Sheaf J A)))
variable (P' : ObjectProperty (DerivedCategory.Plus (Sheaf J' A)))

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type a) [Category.{w} A] [Abelian A] [HasSheafify J A]
variable [EnoughInjectives (Sheaf J A)] [HasDerivedCategory.{d} (Sheaf J A)]
variable [HasDerivedCategory.{e} A] {V W : C} (j : W ⟶ V)

end CategoryTheory.Sheaf

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem supportModule_restriction_epi
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type (max u v)) [Ring R] [HasSheafify J (ModuleCat.{max u v} R)]
    (I : Sheaf J (ModuleCat.{max u v} R)) [Injective I]
    {W V : C} (j : W ⟶ V) [Mono j] : Epi (I.obj.map j.op) := by
  have : Injective I.obj := Injective.injective_of_adjoint (sheafificationAdjunction J _) I
  let a : (uliftYoneda.{u}.obj W ⋙ ModuleCat.free R) ⟶
      (uliftYoneda.{u}.obj V ⋙ ModuleCat.free R) :=
    Functor.whiskerRight (uliftYoneda.{u}.map j) (ModuleCat.free R)
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
  let b : (uliftYoneda.{u}.obj W ⋙ ModuleCat.free R) ⟶ I.obj :=
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

end CategoryTheory

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry

end AlgebraicGeometry
