/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSequenceGlobalSections
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.SequenceProjection.SequencePushforwardLimitProjections
import WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Derived sections and total inverse limit of strict coefficient systems

Source: Stacks Project, Cohomology on Sites, Tags 0941 and 0D6E; Injectives, Tag 079P
(blueprint: lem-coef-sequence-sections-limit-comparison).

The direct image of the specified ringed sequence projection is inverse limit after
termwise restriction. Its cone and the abelian inverse-limit cone are normalized on
complexes. The unit equation specifies the comparison, in addition to its finite projections.
Index `n : ℕ` denotes positive level `n+1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

section Generic

universe a av b bv c cv da db dc sep
variable {E : Type a} [Category.{av} E] [Abelian E] [HasDerivedCategory.{da} E]
  {F : Type b} [Category.{bv} F] [Abelian F] [HasDerivedCategory.{db} F]
  {H : Type c} [Category.{cv} H] [Abelian H] [HasDerivedCategory.{dc} H]

omit [HasDerivedCategory E] in
private theorem sectionsDerives (T : E ⥤ F) [T.Additive] :
    (CochainComplex.KInjectives.localizerMorphism E).Derives
      (T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have : X.obj.IsKInjective := X.property
  have : Y.obj.IsKInjective := Y.property
  have : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp
    (inferInstance : QuasiIso f.hom)
  have : QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    rw [← he]
    exact (T.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map f.hom))
  infer_instance

private def sectionsCompositeUnit (T : E ⥤ F) (S : F ⥤ H) [T.Additive] [S.Additive]
    (R : SequenceSectionsDerivedPair T) (P : SequenceSectionsDerivedPair S) :
    (T ⋙ S).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (R.functor ⋙ P.functor) where
  app X := P.unit.app ((T.mapHomologicalComplex (.up ℤ)).obj X) ≫
    P.functor.map (R.unit.app X)
  naturality X Y f := by
    change DerivedCategory.Q.map ((S.mapHomologicalComplex (.up ℤ)).map
        ((T.mapHomologicalComplex (.up ℤ)).map f)) ≫ _ = _
    have hn := P.unit.naturality ((T.mapHomologicalComplex (.up ℤ)).map f)
    have hm := R.unit.naturality f
    dsimp only [Functor.comp_map] at hn hm
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    rw [← P.functor.map_comp, hm, P.functor.map_comp]
    rfl

private theorem sectionsCompositeDerived [Abelian.HasKInjectiveResolutions E]
    (T : E ⥤ F) (S : F ⥤ H) [T.Additive] [S.Additive]
    (R : SequenceSectionsDerivedPair T) (P : SequenceSectionsDerivedPair S)
    (h : ∀ I : CochainComplex E ℤ, I.IsKInjective →
      IsIso (P.unit.app ((T.mapHomologicalComplex (.up ℤ)).obj I))) :
    (R.functor ⋙ P.functor).IsRightDerivedFunctor
      (sectionsCompositeUnit T S R P) (HomologicalComplex.quasiIso E (.up ℤ)) := by
  apply (sectionsDerives (T ⋙ S)).isRightDerivedFunctor_of_isIso
  intro I
  have := R.computes I.obj I.property
  have := h I.obj I.property
  change IsIso (P.unit.app _ ≫ P.functor.map (R.unit.app I.obj))
  infer_instance

private def sectionsExactCompositeUnit (T : E ⥤ F) (S : F ⥤ H)
    [T.Additive] [S.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (P : SequenceSectionsDerivedPair S) :
    (T ⋙ S).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (T.mapDerivedCategory ⋙ P.functor) where
  app X := P.unit.app ((T.mapHomologicalComplex (.up ℤ)).obj X) ≫
    P.functor.map (T.mapDerivedCategoryFactors.inv.app X)
  naturality X Y f := by
    have hn := P.unit.naturality ((T.mapHomologicalComplex (.up ℤ)).map f)
    have hm := T.mapDerivedCategoryFactors.inv.naturality f
    dsimp only [Functor.comp_map] at hn hm
    change DerivedCategory.Q.map ((S.mapHomologicalComplex (.up ℤ)).map
        ((T.mapHomologicalComplex (.up ℤ)).map f)) ≫ _ = _
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    rw [← P.functor.map_comp, hm, P.functor.map_comp]
    rfl

private def sectionsExactComposite [Abelian.HasKInjectiveResolutions E]
    (T : E ⥤ F) (S : F ⥤ H)
    [T.Additive] [S.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (P : SequenceSectionsDerivedPair S)
    (h : ∀ I : CochainComplex E ℤ, I.IsKInjective →
      IsIso (P.unit.app ((T.mapHomologicalComplex (.up ℤ)).obj I))) :
    SequenceSectionsDerivedPair (T ⋙ S) := by
  have hi (I : CochainComplex E ℤ) (hI : I.IsKInjective) :
      IsIso ((sectionsExactCompositeUnit T S P).app I) := by
    have := h I hI
    change IsIso (P.unit.app _ ≫ P.functor.map (T.mapDerivedCategoryFactors.inv.app I))
    infer_instance
  have hd : (T.mapDerivedCategory ⋙ P.functor).IsRightDerivedFunctor
      (sectionsExactCompositeUnit T S P) (HomologicalComplex.quasiIso E (.up ℤ)) := by
    apply (sectionsDerives (T ⋙ S)).isRightDerivedFunctor_of_isIso
    intro I
    exact hi I.obj I.property
  exact ⟨_, _, hd, hi⟩

private theorem sectionsProjections [HasLimitsOfShape ℕᵒᵖ E]
    [HasDerivedCategory (ℕᵒᵖ ⥤ E)]
    [(lim : (ℕᵒᵖ ⥤ E) ⥤ E).Additive]
    (L : SequenceSectionsDerivedPair (lim : (ℕᵒᵖ ⥤ E) ⥤ E)) :
    ∃ p : ∀ n : ℕ, L.functor ⟶
        ((CategoryTheory.evaluation ℕᵒᵖ E).obj (op n)).mapDerivedCategory,
      ∀ (X : CochainComplex (ℕᵒᵖ ⥤ E) ℤ) (n : ℕ),
        L.unit.app X ≫ (p n).app (DerivedCategory.Q.obj X) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ E).obj (op n)).mapDerivedCategoryFactors.hom.app X =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X) := by
  have := L.universal
  let β (n : ℕ) := Functor.whiskerRight
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)) DerivedCategory.Q ≫
      ((CategoryTheory.evaluation ℕᵒᵖ E).obj (op n)).mapDerivedCategoryFactors.inv
  let p (n : ℕ) := L.functor.rightDerivedDesc L.unit
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ E) (.up ℤ)) _ (β n)
  refine ⟨p, ?_⟩
  intro X n
  rw [← Category.assoc, Functor.rightDerived_fac_app]
  simp [β]

private theorem sectionsNatTransExt [Abelian.HasKInjectiveResolutions E]
    {R S : DerivedCategory E ⥤ DerivedCategory F} (a b : R ⟶ S)
    (h : ∀ I : CochainComplex E ℤ, I.IsKInjective →
      a.app (DerivedCategory.Q.obj I) = b.app (DerivedCategory.Q.obj I)) : a = b := by
  apply NatTrans.ext
  funext X
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective X
  apply (cancel_mono (S.map e.hom)).mp
  rw [← a.naturality, ← b.naturality, h I hI]

omit [HasDerivedCategory E] in
private theorem sectionsTowerGrothendieck
    [IsGrothendieckAbelian.{sep} E] : IsGrothendieckAbelian.{sep} (ℕᵒᵖ ⥤ E) := by
  let G := separator E
  have hG := isSeparator_separator E
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun n : ℕᵒᵖ ↦ (evaluationLeftAdjoint E n).obj G) := by
    intro M N f g hfg
    apply NatTrans.ext
    funext n
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight E n
    apply (adj.homEquiv G N).symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ n) ((adj.homEquiv G M).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  have : HasSeparator (ℕᵒᵖ ⥤ E) := ⟨_, hS.isSeparator_coproduct⟩
  have : HasFilteredColimitsOfSize.{sep, sep} (ℕᵒᵖ ⥤ E) := ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{sep, sep} (ℕᵒᵖ ⥤ E) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun M N ↦ small_of_injective
    (f := fun f : M ⟶ N ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

private theorem sectionsSplitRoos
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [∀ (p : ℤ) (n : ℕ),
      IsSplitEpi ((I.X p).map (homOfLE (Nat.le_succ n)).op)] :
    let L := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)
    let p : L.obj I ⟶ ∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n)) :=
      Pi.lift (fun n : ℕ ↦ (NatTrans.mapHomologicalComplex
        (lim.π (op n)) (ComplexShape.up ℤ)).app I)
    let t := towerTransitionEndomorphism
      (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op)
    ∃ h : p ≫ t = 0, (ShortComplex.mk p t h).ShortExact := by
  intro L p t
  let c : Cone I.asFunctor :=
    { pt := L.obj I
      π := { app := fun n ↦ (NatTrans.mapHomologicalComplex
                (lim.π n) (ComplexShape.up ℤ)).app I
             naturality := by
               intro n m f
               ext r
               change 𝟙 _ ≫ limit.π (I.X r) m =
                 limit.π (I.X r) n ≫ (I.X r).map f
               rw [Category.id_comp]
               exact (limit.w _ _).symm } }
  have hc : IsLimit c := by
    apply HomologicalComplex.isLimitOfEval
    intro r
    exact limit.isLimit (I.X r)
  let K := fun n : ℕ ↦ I.asFunctor.obj (op n)
  let P : Fan K := limit.cone (Discrete.functor K)
  have ht (n) : t ≫ P.proj n = P.proj n - P.proj (n + 1) ≫
      I.asFunctor.map (homOfLE (Nat.le_succ n)).op := by
    change t ≫ Pi.π K n = Pi.π K n - Pi.π K (n + 1) ≫ _
    simp [t, K, towerTransitionEndomorphism, towerProductShift]
  obtain ⟨h, ⟨hk⟩⟩ := CategoryTheory.tower_kernel I.asFunctor c hc P
    (limit.isLimit _) p t (fun n ↦ Pi.lift_comp_π _ n) ht
  refine ⟨h, HomologicalComplex.shortExact_of_degreewise_shortExact _ ?_⟩
  intro r
  let ev := HomologicalComplex.eval A (ComplexShape.up ℤ) r
  have hkr := KernelFork.mapIsLimit _ hk ev
  have hPr : IsLimit (Fan.mk (P.pt.X r) (fun n ↦ (P.proj n).f r)) :=
    (Fan.isLimitMapConeEquiv ev K P) (isLimitOfPreserves ev (limit.isLimit _))
  have htr : IsSplitEpi (t.f r) := CategoryTheory.fan_shift_splitEpi
    (fun n : ℕ ↦ (I.X r).obj (op n)) _ hPr
    (fun n : ℕ ↦ (I.X r).map (homOfLE (Nat.le_succ n)).op) (t.f r)
    (fun n ↦ congrArg (fun f ↦ f.f r) (ht n))
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hkr)
    (mono_of_isLimit_fork hkr) htr.epi

private theorem sectionsRoosComparisonQuasiIso
    (I : CochainComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ℤ)
    [∀ (p : ℤ) (n : ℕ), IsSplitEpi ((I.X p).map (homOfLE (Nat.le_succ n)).op)] :
    QuasiIso (ExactProductsRoos.comparison.app I) := by
  obtain ⟨h, hs⟩ := sectionsSplitRoos I
  let S := ShortComplex.mk (ExactProductsRoos.inclusion.app I)
    (-ExactProductsRoos.difference.app I)
    (by rw [Preadditive.comp_neg, ExactProductsRoos.inclusion_difference, neg_zero])
  have hS : S.ShortExact := by
    apply ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk _ _ h) _ hs
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      { hom := -𝟙 _
        inv := -𝟙 _
        hom_inv_id := by simp
        inv_hom_id := by simp } (by simp [S]) (by
          change 𝟙 _ ≫ (-ExactProductsRoos.difference.app I) = _ ≫ (-𝟙 _)
          simp)
  exact AlgebraicGeometry.ProEtale.cocone_lift_quasiIso S hS
    (ExactProductsRoos.comparison_condition I)

omit [HasDerivedCategory E] in
private theorem sectionsTowerImageAcyclic
    [IsGrothendieckAbelian.{sep} E]
    (T : E ⥤ AddCommGrpCat.{w}) [T.Additive]
    [(lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).Additive]
    (L : SequenceSectionsDerivedPair
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}))
    (I : CochainComplex (ℕᵒᵖ ⥤ E) ℤ) (hI : I.IsKInjective) :
    IsIso (L.unit.app
      ((((Functor.whiskeringRight ℕᵒᵖ E AddCommGrpCat.{w}).obj T).mapHomologicalComplex
        (.up ℤ)).obj I)) := by
  have : IsGrothendieckAbelian.{sep} (ℕᵒᵖ ⥤ E) := sectionsTowerGrothendieck
  have : IsGrothendieckAbelian.{w} (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) :=
    sectionsTowerGrothendieck
  have := hI
  let W := (Functor.whiskeringRight ℕᵒᵖ E AddCommGrpCat.{w}).obj T
  let J := (CochainComplex.kInjectiveResolutionFunctor.{sep} (ℕᵒᵖ ⥤ E)).obj I
  let q : I ⟶ J := (CochainComplex.toKInjectiveResolution.{sep} (ℕᵒᵖ ⥤ E)).app I
  have : QuasiIso q :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ I).2
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff q).mp inferInstance
  have hWq : QuasiIso ((W.mapHomologicalComplex (.up ℤ)).map q) := by
    rw [← he]
    exact (W.mapHomotopyEquiv e).quasiIso_hom
  have hLq : QuasiIso
      ((lim.mapHomologicalComplex (.up ℤ)).map ((W.mapHomologicalComplex (.up ℤ)).map q)) := by
    rw [← he]
    exact (lim.mapHomotopyEquiv (W.mapHomotopyEquiv e)).quasiIso_hom
  have (p : ℤ) (n : ℕ) : IsSplitEpi
      ((((W.mapHomologicalComplex (.up ℤ)).obj J).X p).map
        (homOfLE (Nat.le_succ n)).op) := by
    have := CategoryTheory.injective_tower_transition_split (J.X p) n
    change IsSplitEpi (T.map ((J.X p).map (homOfLE (Nat.le_succ n)).op))
    infer_instance
  have : QuasiIso (ExactProductsRoos.comparison.app
      ((W.mapHomologicalComplex (.up ℤ)).obj J)) := sectionsRoosComparisonQuasiIso _
  obtain ⟨a, ha⟩ := ExactProductsRoos.comparisonIso L.functor L.unit L.computes
  have hη : IsIso (L.unit.app ((W.mapHomologicalComplex (.up ℤ)).obj J)) := by
    have heq := congrArg (fun η ↦ η.app ((W.mapHomologicalComplex (.up ℤ)).obj J)) ha
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at heq
    rw [← heq]
    infer_instance
  have hn := L.unit.naturality ((W.mapHomologicalComplex (.up ℤ)).map q)
  have : IsIso (L.unit.app ((W.mapHomologicalComplex (.up ℤ)).obj I) ≫
      L.functor.map (DerivedCategory.Q.map ((W.mapHomologicalComplex (.up ℤ)).map q))) := by
    change _ = L.unit.app ((W.mapHomologicalComplex (.up ℤ)).obj I) ≫
      L.functor.map (DerivedCategory.Q.map ((W.mapHomologicalComplex (.up ℤ)).map q)) at hn
    rw [← hn]
    change IsIso (DerivedCategory.Q.map
      ((lim.mapHomologicalComplex (.up ℤ)).map
        ((W.mapHomologicalComplex (.up ℤ)).map q)) ≫
      L.unit.app ((W.mapHomologicalComplex (.up ℤ)).obj J))
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (L.functor.map (DerivedCategory.Q.map ((W.mapHomologicalComplex (.up ℤ)).map q)))

end Generic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- Abelian inverse limit is additive.
Source: Stacks 0941 (blueprint: lem-coef-sequence-sections-limit-comparison). -/
instance sequenceAbLimitAdditive :
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).Additive :=
  Functor.additive_of_preserves_binary_products _

end SheafOfModules
