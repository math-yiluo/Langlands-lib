/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemOrdinaryImages
import WeilConjectures.CategoryTheory.Scalar.ScalarAdjunctionDescent
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedExtension
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedAbove
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedBelow
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedTransition
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientTensorDerivedUnit
import all WeilConjectures.CategoryTheory.Exact.ExactDerivedAdjunctionBounds
import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Core data for bounded-below site comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

private theorem exceptionalEvaluationLimits
    (O : Type (u + 1)) [CommRing O] (ell : O) (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits
      (coefficientEvaluation (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n) :=
  (coefficientEvaluation_exact.{u + 1, u, u + 1} n).1

private theorem exceptionalEvaluationColimits
    (O : Type (u + 1)) [CommRing O] (ell : O) (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits
      (coefficientEvaluation (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n) :=
  (coefficientEvaluation_exact.{u + 1, u, u + 1} n).2

attribute [local instance] exceptionalEvaluationLimits exceptionalEvaluationColimits

private def exceptionalEvaluationDerivedIso
    (O : Type (u + 1)) [CommRing O] (ell : O)
    (T : Scheme.{u})
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology T) (O := O) (ell := ell)) (n : ℕ) :
    P.evaluation n ≅ (coefficientEvaluation (J := Scheme.ProEt.topology T)
      (O := O) (ell := ell) n).mapDerivedCategory := by
  letI := (coefficientEvaluation_exact (J := Scheme.ProEt.topology T)
    (O := O) (ell := ell) n).1
  letI := (coefficientEvaluation_exact (J := Scheme.ProEt.topology T)
    (O := O) (ell := ell) n).2
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (CoefficientSystem (J := Scheme.ProEt.topology T) O ell) (.up ℤ))
    (DerivedCategory.Q ⋙ P.evaluation n)
    (DerivedCategory.Q ⋙ (coefficientEvaluation (J := Scheme.ProEt.topology T)
      (O := O) (ell := ell) n).mapDerivedCategory)
    (P.evaluation n)
    (coefficientEvaluation (J := Scheme.ProEt.topology T) (O := O)
      (ell := ell) n).mapDerivedCategory
    (P.evaluationFactors n ≪≫
      (coefficientEvaluation (J := Scheme.ProEt.topology T) (O := O)
        (ell := ell) n).mapDerivedCategoryFactors.symm)

/-- The finite inverse image preserves lower bounds.
Source: Zheng Lemma 4.10; Stacks 09B1.
(blueprint: lem-sf-exceptional-site-origin-comparison-level-bound). -/
theorem exceptionalSiteOriginComparison_level_inverse_bound
    (O : Type (u + 1)) [CommRing O] (ell : O)
    (T : Scheme.{u}) (PE : StrictEtaleEvaluation T O ell)
    (C : ExceptionalSystemSiteComparison O ell T PE)
    (n : ℕ) (N : DerivedCategory (strictEtaleLevel T O ell n)) (a : ℤ)
    (hN : N.IsGE a) : ((C.image.level n).inverse.obj N).IsGE a := by
  letI : PreservesFiniteLimits (C.ordinary.lift n).modules :=
    C.ordinary.inverseExact n |>.1
  letI : PreservesFiniteColimits (C.ordinary.lift n).modules :=
    C.ordinary.inverseExact n |>.2
  have hF : ((C.ordinary.lift n).modules.mapDerivedCategory.obj N).IsGE a :=
    (C.ordinary.lift n).modules.isGE_mapDerivedCategory_obj N a
  have he : (C.image.level n).inverse.obj N ≅
      (C.ordinary.lift n).modules.mapDerivedCategory.obj N := by
    exact Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso
        (strictEtaleLevel T O ell n) (.up ℤ))
      (DerivedCategory.Q ⋙ (C.image.level n).inverse)
      (DerivedCategory.Q ⋙ (C.ordinary.lift n).modules.mapDerivedCategory)
      (C.image.level n).inverse
      (C.ordinary.lift n).modules.mapDerivedCategory
      ((C.image.level n).inverseFactors ≪≫
        (C.ordinary.lift n).modules.mapDerivedCategoryFactors.symm) |>.app N
  exact DerivedCategory.TStructure.t.isGE_of_iso he.symm a

-- Assemble all coherence fields at the concrete pro-etale site sizes.
private theorem exceptionalProEvaluation_exists (W : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) : Nonempty (ExceptionalProEvaluation W O ell) := by
  classical
  let J := Scheme.ProEt.topology W
  obtain ⟨ordinary⟩ := coefficientOrdinaryEvaluationExtension (J := J) (O := O) (ell := ell)
  let := ordinary.extensionAdditive
  let scalar {m n : ℕ} (h : n ≤ m) :=
    (coefficientScalarDerivedAdjunction (J := J) (O := O) (ell := ell) h).some
  obtain ⟨core⟩ := coefficientEvaluationDerivedCore ordinary
  choose transition ht using (fun (m n : ℕ) (h : n ≤ m) ↦
    coefficientEvaluationDerivedTransition ordinary (fun {_ _} h ↦ scalar h) core h)
  choose below hb using (fun (n q : ℕ) (h : q ≤ n) ↦
    coefficientEvaluationDerivedBelow ordinary (fun {_ _} h ↦ scalar h) core h)
  obtain ⟨strict⟩ := coefficientEvaluationOrdinaryCoherence ordinary
  choose unit hu using (fun n ↦ coefficientTensorDerivedUnit
    (fun {_ _} h ↦ scalar h) n (strict.tensorUnit n))
  have unit_rep (n : ℕ) P : (unit n).hom.app (DerivedCategory.Q.obj P) =
      (scalar (Nat.le_refl n)).counit.app P ≫
        DerivedCategory.Q.map (strict.tensorUnitComplex n P).hom := by
    rw [hu n P]
    congr 1
    apply congrArg
    apply HomologicalComplex.hom_f_injective
    funext i
    change (strict.tensorUnit n).hom.app (P.X i) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact (strict.tensorUnitComplex_f n P i).symm
  obtain ⟨derived⟩ := coefficientEvaluationDerivedCoherence ordinary
    (fun {_ _} h ↦ scalar h) core (fun {_ _} h ↦ transition _ _ h) strict unit unit_rep
    (fun h K ↦ ht _ _ h K)
  exact ⟨{
    strictTransition := ordinary.strictTransition
    transitionsNormalized := ordinary.transitionsNormalized
    scalar := fun h ↦ scalar h
    extension := ordinary.extension
    extensionAdditive := ordinary.extensionAdditive
    adj := ordinary.adj
    below := ordinary.below
    above := ordinary.above
    hom_formula := ordinary.hom_formula
    evaluation := core.evaluation
    evaluationFactors := core.evaluationFactors
    derivedExtension := core.derivedExtension
    counit := core.counit
    isDerived := core.isDerived
    computes := fun n P hP _ ↦ core.computes n P hP
    derivedAdj := core.derivedAdj
    transpose := core.transpose
    derivedBelow := fun h ↦ below _ _ h
    derivedAbove := coefficientEvaluationDerivedAbove ordinary core
    transition := fun h ↦ transition _ _ h
    transition_rep := fun h K ↦ ht _ _ h K
    sigma := fun h ↦ coefficientEvaluationSigma (fun {_ _} h ↦ scalar h) core
      (fun {_ _} h ↦ transition _ _ h) h
    mate := fun h ↦ CategoryTheory.Adjunction.compositeMate_homEquiv
      (core.derivedAdj _) (core.derivedAdj _) (scalar h).derivedAdj (transition _ _ h)
    tensorUnit := strict.tensorUnit
    tensorUnit_normalized := strict.tensorUnit_normalized
    tensorAssoc := strict.tensorAssoc
    tensorAssoc_normalized := strict.tensorAssoc_normalized
    strictSigma := strict.strictSigma
    strictSigma_below := strict.strictSigma_below
    strictSigma_above := strict.strictSigma_above
    strictSigmaComplex := strict.strictSigmaComplex
    strictSigmaComplex_f := strict.strictSigmaComplex_f
    sigma_rep := derived.sigma_rep
    tensorUnitComplex := strict.tensorUnitComplex
    tensorUnitComplex_f := strict.tensorUnitComplex_f
    tensorAssocComplex := strict.tensorAssocComplex
    tensorAssocComplex_f := strict.tensorAssocComplex_f
    derivedUnit := unit
    derivedUnit_rep := fun n P _ ↦ unit_rep n P
    derivedAssoc := derived.derivedAssoc
    derivedAssoc_rep := derived.derivedAssoc_rep
    sigma_id := derived.sigma_id
    sigma_comp := derived.sigma_comp
    belowComplex := fun h P ↦
      (NatIso.mapHomologicalComplex (ordinary.below h) (.up ℤ)).app P
    belowComplex_f := fun _ _ _ ↦ rfl
    derivedBelow_rep := fun h P ↦ hb _ _ h P }⟩

private def scalarRestrictionCancel
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (α : R ⟶ S) (β : S ⟶ R)
    (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{u + 1} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private theorem scalarRestrictionEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (e : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} e.hom).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars.{u + 1} e.hom)
    (SheafOfModules.restrictScalars e.inv)
    (scalarRestrictionCancel e.inv e.hom e.inv_hom_id).symm
    (scalarRestrictionCancel e.hom e.inv e.hom_inv_id)).isEquivalence_functor

private theorem constantSection_apply
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type (u + 1))] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1})]
    (A : Type (u + 1)) [CommRing A] (a : A) (U : Cᵒᵖ)
    (z : ((constantSheaf J (Type (u + 1))).obj PUnit).obj.obj U) :
    ((((sheafificationAdjunction J (Type (u + 1))).homEquiv _
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj
        ((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of A)))).symm
      ((Functor.const Cᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{u + 2}) ↦ a)) ≫
        Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
          (CategoryTheory.forget CommRingCat.{u + 1}))).hom.app U z) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a := by
  let T := (Functor.const Cᵒᵖ).obj (PUnit.{u + 2} : Type (u + 1))
  have hT : Presheaf.IsSheaf J T := Sheaf.tensorUnit_isSheaf J
  have : IsIso (toSheafify J T) := isIso_toSheafify J hT
  obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((toSheafify J T).app U)).surjective z
  have h := ((sheafificationAdjunction J (Type (u + 1))).homEquiv _
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj
        ((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of A)))).apply_symm_apply
    ((Functor.const Cᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{u + 2}) ↦ a)) ≫
      Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
        (CategoryTheory.forget CommRingCat.{u + 1}))
  exact congrArg (fun f ↦ f.app U t) h

private theorem constantRingScalar
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasWeakSheafify J RingCat.{u + 1}] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    (A : Type (u + 1)) [CommRing A] (U : Cᵒᵖ) (a : A) :
    (((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
      (CommRingCat.of A)).hom.app U)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a := by
  have h := sheafComposeIso_hom_fac J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  change ((sheafifyComposeIso J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U)
      (((presheafToSheaf J RingCat.{u + 1}).map
        ((Functor.compConstIso Cᵒᵖ
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
            (CommRingCat.of A))).hom.app U
              ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a)) = _
  have hi : ((Functor.compConstIso Cᵒᵖ
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
        (CommRingCat.of A)) = 𝟙 _ := rfl
  rw [hi, CategoryTheory.Functor.map_id]
  exact congrArg (fun f ↦ f.app U a) h

private theorem exceptionalForget
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J RingCat.{u + 1}] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.WEqualsLocallyBijective RingCat.{u + 1}]
    [J.WEqualsLocallyBijective CommRingCat.{u + 1}] :
    J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  constructor
  intro P Q f hf
  change J.W (Functor.whiskerRight f (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  have hi : Presheaf.IsLocallyInjective J f := hf.isLocallyInjective
  have hs : Presheaf.IsLocallySurjective J f := hf.isLocallySurjective
  apply (J.W_iff_isLocallyBijective _).mpr
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J f x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem J f x⟩

private def exceptionalLevelRealization
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J RingCat.{u + 1}] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    (O : Type (u + 1)) [CommRing O] (ell : O) (n : ℕ) :
    coefficientLevelModules (J := J) O ell n ⥤
      Sheaf J (ModuleCat.{u + 1} (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))) :=
  SheafOfModules.restrictScalars
      ((constantCommuteCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)))).inv ⋙
    constantRingModuleRestriction J (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))

private theorem exceptionalLevelRealization_equivalence
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J RingCat.{u + 1}] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    (O : Type (u + 1)) [CommRing O] (ell : O) (n : ℕ) :
    (exceptionalLevelRealization J O ell n).IsEquivalence := by
  let A : Type (u + 1) := O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)
  obtain ⟨e, he, _⟩ := (constant_ring_module_sheaves J A).1
  have : (constantRingModuleRestriction J A).IsEquivalence := he ▸ e.isEquivalence_functor
  let c := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of A)
  have : (SheafOfModules.restrictScalars.{u + 1} c.inv).IsEquivalence :=
    scalarRestrictionEquivalence c.symm
  dsimp only [exceptionalLevelRealization]
  infer_instance

attribute [local instance] exceptionalForget exceptionalLevelRealization_equivalence

/-- The scalar action of a realized module is the action of the corresponding constant section. -/
private theorem exceptionalLevelRealization_smul
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J RingCat.{u + 1}] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    (O : Type (u + 1)) [CommRing O] (ell : O) (n : ℕ)
    (M : coefficientLevelModules (J := J) O ell n) (U : Cᵒᵖ)
    (c : O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)) (x : M.val.obj U) :
    (show M.val.obj U from
      c • (show ((exceptionalLevelRealization J O ell n).obj M).obj.obj U from x)) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))))).app U c • x := by
  change (((constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
      (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)))).hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj
          (RingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))))).app U c)) • x = _
  rw [constantRingScalar]

/-- A sectionwise linear isomorphism of underlying sheaves lifts uniquely to module sheaves. -/
private theorem exceptionalModuleSheafIso_existsUnique
    {C D : Type*} [Category C] [Category D] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] (F G : D ⥤ Sheaf J (ModuleCat.{u + 1} A))
    (β : F ⋙ sheafCompose J (CategoryTheory.forget (ModuleCat.{u + 1} A)) ≅
      G ⋙ sheafCompose J (CategoryTheory.forget (ModuleCat.{u + 1} A)))
    (hadd : ∀ M U (x y : (F.obj M).obj.obj U),
      (β.hom.app M).hom.app U (x + y) =
        (show (G.obj M).obj.obj U from (β.hom.app M).hom.app U x) +
          (show (G.obj M).obj.obj U from (β.hom.app M).hom.app U y))
    (hsmul : ∀ M U (c : A) (x : (F.obj M).obj.obj U),
      (β.hom.app M).hom.app U (c • x) =
        c • (show (G.obj M).obj.obj U from (β.hom.app M).hom.app U x)) :
    ∃! e : F ≅ G, ∀ M U (x : (F.obj M).obj.obj U),
      (e.hom.app M).hom.app U x = (β.hom.app M).hom.app U x := by
  let γ : F ⟶ G := {
    app := fun M ↦ { hom := {
      app := fun U ↦ ModuleCat.ofHom {
        toFun := fun x ↦ (β.hom.app M).hom.app U x
        map_add' := hadd M U
        map_smul' := hsmul M U }
      naturality := by
        intro U V f
        ext x
        exact congrArg (fun k ↦ k x) ((β.hom.app M).hom.naturality f) } }
    naturality := by
      intro M N f
      ext U x
      exact congrArg (fun k ↦ k.hom.app U x) (β.hom.naturality f) }
  have hγ (M) : IsIso (γ.app M) := by
    have hpoint (U) : IsIso ((γ.app M).hom.app U) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact ConcreteCategory.bijective_of_isIso ((β.hom.app M).hom.app U)
    have : IsIso ((sheafToPresheaf J _).map (γ.app M)) :=
      NatIso.isIso_of_isIso_app (γ.app M).hom
    exact isIso_of_reflects_iso (γ.app M) (sheafToPresheaf J _)
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  refine ⟨asIso γ, ?_, ?_⟩
  · intro M U x
    rfl
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    apply funext
    intro M
    ext U x
    exact he M U x

section
variable (O : Type (u + 1)) [CommRing O] (ell : O) (W : Scheme.{u})
  (S : CoefficientSystemOrdinaryImage (J := W.smallEtaleTopology)
    (K := Scheme.ProEt.topology W) O ell _ _ (Scheme.proEtaleSiteComparison W))

-- Lift the underlying right-adjoint comparison using the counit's linearity.
private theorem exceptionalSiteRight_existsUnique (n : ℕ) :
    ∃! e : S.right n ⋙ exceptionalLevelRealization W.smallEtaleTopology O ell n ≅
      exceptionalLevelRealization (Scheme.ProEt.topology W) O ell n ⋙
        ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))) W,
      ∀ (M : coefficientLevelModules (J := Scheme.ProEt.topology W)
        O ell n)
        (U : W.Etaleᵒᵖ) (x : ((S.right n).obj M).val.obj U),
        (e.hom.app M).hom.app U x =
          ((S.rightUnderlying n).hom.app M).hom.app U x := by
  -- Share these instances between the realization functors and their scalar-action formulas.
  have : HasWeakSheafify W.smallEtaleTopology RingCat.{u + 1} := inferInstance
  have : HasWeakSheafify (Scheme.ProEt.topology W) RingCat.{u + 1} := inferInstance
  have : W.smallEtaleTopology.PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := exceptionalForget _
  have : (Scheme.ProEt.topology W).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := exceptionalForget _
  let L : Sheaf W.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology W) (Type (u + 1)) :=
    Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt W)
      (Type (u + 1)) W.smallEtaleTopology (Scheme.ProEt.topology W)
  let adj := Scheme.proEtaleSiteComparison W
  let Q := coefficientUnderlying (J := W.smallEtaleTopology)
    O ell n
  let V := coefficientUnderlying (J := Scheme.ProEt.topology W)
    O ell n
  let I := S.lift n
  let R := S.right n
  let β := S.rightUnderlying n
  have hβ (M) : β.hom.app M = adj.homEquiv _ _
      (I.moduleUnderlying.inv.app (R.obj M) ≫
        V.map ((S.levelAdj n).counit.app M)) := by
    have hc : (S.levelAdj n).homEquiv (R.obj M) M
        ((S.levelAdj n).counit.app M) = 𝟙 _ := by
      rw [← Adjunction.homEquiv_symm_id]
      exact ((S.levelAdj n).homEquiv (R.obj M) M).apply_symm_apply _
    have h := S.levelTranspose n (R.obj M) M
      ((S.levelAdj n).counit.app M)
    change (S.levelAdj n).homEquiv (R.obj M) M
      ((S.levelAdj n).counit.app M) = 𝟙 _ at hc
    change Q.map ((S.levelAdj n).homEquiv (R.obj M) M
      ((S.levelAdj n).counit.app M)) ≫ β.hom.app M = _ at h
    simp only [hc, Q.map_id, Category.id_comp] at h
    exact h
  have hunit (M) (T : Sheaf W.smallEtaleTopology (Type (u + 1)))
      (a : T ⟶ Q.obj (R.obj M)) (U : W.Etaleᵒᵖ) (z : T.obj.obj U) :
      (β.hom.app M).hom.app U (a.hom.app U z) =
      ((S.levelAdj n).counit.app M).val.app ((Scheme.toProEt W).op.obj U)
        ((I.moduleUnderlying.inv.app (R.obj M)).hom.app ((Scheme.toProEt W).op.obj U)
          ((L.map a).hom.app ((Scheme.toProEt W).op.obj U)
            ((adj.unit.app T).hom.app U z))) := by
    simp only [hβ, Adjunction.homEquiv_unit]
    have h := congrArg (fun f ↦ f.hom.app U z) (adj.unit.naturality a)
    change (adj.unit.app (Q.obj (R.obj M))).hom.app U (a.hom.app U z) =
      (L.map a).hom.app ((Scheme.toProEt W).op.obj U)
        ((adj.unit.app T).hom.app U z) at h
    exact congrArg (fun x ↦
      ((S.levelAdj n).counit.app M).val.app ((Scheme.toProEt W).op.obj U)
        ((I.moduleUnderlying.inv.app (R.obj M)).hom.app
          ((Scheme.toProEt W).op.obj U) x)) h
  have hadd (M) (U : W.Etaleᵒᵖ) (x y : (R.obj M).val.obj U) :
      (β.hom.app M).hom.app U (x + y) =
        (show M.val.obj ((Scheme.toProEt W).op.obj U) from
          (β.hom.app M).hom.app U x) +
        (show M.val.obj ((Scheme.toProEt W).op.obj U) from
          (β.hom.app M).hom.app U y) := by
    let X := Q.obj (R.obj M)
    let T := (CategoryTheory.MonoidalCategory.tensorObj X X)
    let a : T ⟶ X := CartesianMonoidalCategory.fst X X
    let b : T ⟶ X := CartesianMonoidalCategory.snd X X
    let t : T ⟶ X := ⟨{
      app := fun Y ↦ ↾fun z ↦
        (show (R.obj M).val.obj Y from z.1) +
          (show (R.obj M).val.obj Y from z.2)
      naturality := by
        intro Y Z f
        ext z
        exact ((R.obj M).val.map f).hom.map_add z.1 z.2 |>.symm }⟩
    have h := I.moduleAdd (R.obj M) T a b t (fun _ _ ↦ rfl)
      ((Scheme.toProEt W).op.obj U) ((adj.unit.app T).hom.app U (x, y))
    have ha := hunit M T a U (x, y)
    have hb := hunit M T b U (x, y)
    have ht := hunit M T t U (x, y)
    change (β.hom.app M).hom.app U (x + y) = _ at ht
    change (β.hom.app M).hom.app U x = _ at ha
    change (β.hom.app M).hom.app U y = _ at hb
    simp only [ht, ha, hb]
    dsimp only [id] at h
    exact (congrArg (fun z ↦ ((S.levelAdj n).counit.app M).val.app
      ((Scheme.toProEt W).op.obj U) z) h).trans
        ((((S.levelAdj n).counit.app M).val.app
          ((Scheme.toProEt W).op.obj U)).hom.map_add _ _)
  have hsmul (M) (U : W.Etaleᵒᵖ) (q : (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)))
      (x : (R.obj M).val.obj U) :
      (β.hom.app M).hom.app U
        ((toSheafify W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj
          (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))))).app U q • x) =
      (toSheafify (Scheme.ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))))).app
          ((Scheme.toProEt W).op.obj U) q •
        (show M.val.obj ((Scheme.toProEt W).op.obj U) from
          (β.hom.app M).hom.app U x) := by
    let X := Q.obj (R.obj M)
    let P₁ := (constantSheaf W.smallEtaleTopology (Type (u + 1))).obj PUnit
    let T := CategoryTheory.MonoidalCategory.tensorObj P₁ X
    let a : T ⟶ _ := CartesianMonoidalCategory.fst P₁ X ≫
      coefficientConstantSection (J := W.smallEtaleTopology)
        O ell n q
    let b : T ⟶ X := CartesianMonoidalCategory.snd P₁ X
    let t : T ⟶ X := ⟨{
      app := fun Y ↦ ↾fun z ↦
        (show (coefficientQuotientSheaf (J := W.smallEtaleTopology)
          O ell n).obj.obj Y
            from a.hom.app Y z) • (show (R.obj M).val.obj Y from z.2)
      naturality := by
        intro Y Z f
        ext z
        have hn := congrArg (fun k ↦ k z) (a.hom.naturality f).symm
        change (coefficientQuotientSheaf (J := W.smallEtaleTopology)
          O ell n).obj.map f
            (a.hom.app Y z) = a.hom.app Z (T.obj.map f z) at hn
        symm
        change (R.obj M).val.map f
          ((show (coefficientQuotientSheaf (J := W.smallEtaleTopology)
            O ell n).obj.obj Y
              from a.hom.app Y z) • (show (R.obj M).val.obj Y from z.2)) =
          (show (coefficientQuotientSheaf (J := W.smallEtaleTopology)
            O ell n).obj.obj Z
              from a.hom.app Z (T.obj.map f z)) •
            (show (R.obj M).val.obj Z from (R.obj M).val.map f z.2)
        rw [(R.obj M).val.map_smul]
        exact congrArg (fun c : (coefficientQuotientSheaf
          (J := W.smallEtaleTopology) O
          ell n).obj.obj Z ↦
            c • (show (R.obj M).val.obj Z from (R.obj M).val.map f z.2)) hn }⟩
    let z : T.obj.obj U :=
      ((toSheafify W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj
        (PUnit.{u + 2} : Type (u + 1)))).app U PUnit.unit, x)
    have ha : a.hom.app U z =
        (toSheafify W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj
          (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))))).app U q :=
      constantSection_apply W.smallEtaleTopology _ q U z.1
    have h := I.moduleSMul (R.obj M) T a b t (fun _ _ ↦ rfl)
      ((Scheme.toProEt W).op.obj U) ((adj.unit.app T).hom.app U z)
    have hc : L.map a ≫ I.ringUnderlying.hom =
        L.map (CartesianMonoidalCategory.fst P₁ X) ≫ S.singleton.hom ≫
          coefficientConstantSection (J := Scheme.ProEt.topology W)
            O ell n q := by
      dsimp only [a]
      rw [L.map_comp, Category.assoc, S.constants]
    have hc' := congrArg (fun f ↦ f.hom.app ((Scheme.toProEt W).op.obj U)
      ((adj.unit.app T).hom.app U z)) hc
    have ht := hunit M T t U z
    have hb := hunit M T b U z
    change (β.hom.app M).hom.app U
      ((show (coefficientQuotientSheaf (J := W.smallEtaleTopology) O ell n).obj.obj U
        from a.hom.app U z) • x) = _ at ht
    change (β.hom.app M).hom.app U x = _ at hb
    simp only [ha] at ht
    simp only [ht, hb]
    dsimp only [id] at h
    refine (congrArg (fun z ↦ ((S.levelAdj n).counit.app M).val.app
      ((Scheme.toProEt W).op.obj U) z) h).trans ?_
    have hconst := constantSection_apply (Scheme.ProEt.topology W)
      (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)) q ((Scheme.toProEt W).op.obj U)
      ((S.singleton.hom).hom.app ((Scheme.toProEt W).op.obj U)
        ((L.map (CartesianMonoidalCategory.fst P₁ X)).hom.app
          ((Scheme.toProEt W).op.obj U) ((adj.unit.app T).hom.app U z)))
    change (I.ringUnderlying.hom).hom.app ((Scheme.toProEt W).op.obj U)
      ((L.map a).hom.app ((Scheme.toProEt W).op.obj U)
        ((adj.unit.app T).hom.app U z)) = _ at hc'
    have hs := hc'.trans hconst
    let f := ((S.levelAdj n).counit.app M).val.app ((Scheme.toProEt W).op.obj U)
    let y : (I.modules.obj (R.obj M)).val.obj ((Scheme.toProEt W).op.obj U) :=
      (I.moduleUnderlying.inv.app (R.obj M)).hom.app ((Scheme.toProEt W).op.obj U)
        ((L.map b).hom.app ((Scheme.toProEt W).op.obj U) ((adj.unit.app T).hom.app U z))
    exact (f.hom.map_smul _ y).trans
      (congrArg (fun c : (coefficientQuotientSheaf (J := Scheme.ProEt.topology W)
        O ell n).obj.obj ((Scheme.toProEt W).op.obj U) ↦ c • f y) hs)
  let F := R ⋙ exceptionalLevelRealization W.smallEtaleTopology O ell n
  let G := exceptionalLevelRealization (Scheme.ProEt.topology W) O ell n ⋙
    ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
      (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))) W
  refine exceptionalModuleSheafIso_existsUnique W.smallEtaleTopology
    (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)) F G β hadd ?_
  intro M U c x
  exact (congrArg (fun z ↦ (β.hom.app M).hom.app U z)
    (exceptionalLevelRealization_smul W.smallEtaleTopology O ell n (R.obj M) U c x)).trans
      ((hsmul M U c x).trans
        (exceptionalLevelRealization_smul (Scheme.ProEt.topology W) O ell n M
          ((Scheme.toProEt W).op.obj U) c ((β.hom.app M).hom.app U x)).symm)

private def exceptionalSiteInverse (n : ℕ) :
    (S.lift n).modules ⋙ exceptionalLevelRealization (Scheme.ProEt.topology W) O ell n ≅
      exceptionalLevelRealization W.smallEtaleTopology O ell n ⋙
        ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))) W := by
  let adj₁ := S.levelAdj n
  let adj₂ := ProEtale.comparisonAdjunction
    (ModuleCat.{u + 1} (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))) W
  let β := (exceptionalSiteRight_existsUnique O ell W S n).exists.choose
  let α := ((mateEquiv adj₁ adj₂).symm β.hom)
  have : IsIso α := isIso_inverseMate_of_equivalences adj₁ adj₂ β
  exact (asIso α).symm

-- Transport the two realization equivalences and their derived comparison square.
private theorem exceptionalLevel_full
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (n : ℕ)
    (FD : DerivedCategory (coefficientLevelModules (J := W.smallEtaleTopology) O ell n) ⥤
      DerivedCategory (coefficientLevelModules (J := Scheme.ProEt.topology W) O ell n))
    (fac : DerivedCategory.Q ⋙ FD ≅
      (S.lift n).modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (X Y : DerivedCategory (coefficientLevelModules (J := W.smallEtaleTopology) O ell n))
    (hX : ∃ a : ℤ, X.IsGE a) (hY : ∃ a : ℤ, Y.IsGE a) :
    Function.Bijective (FD.map : (X ⟶ Y) → _) := by
  let A : Type (u + 1) := O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  let F := (S.lift n).modules
  have : PreservesFiniteLimits F := (S.inverseExact n).1
  have : PreservesFiniteColimits F := (S.inverseExact n).2
  let EJ := exceptionalLevelRealization W.smallEtaleTopology O ell n
  let EK := exceptionalLevelRealization (Scheme.ProEt.topology W) O ell n
  have : EJ.Additive := Functor.additive_of_preserves_binary_products EJ
  have : EK.Additive := Functor.additive_of_preserves_binary_products EK
  let L := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) W
  let E := ProEtale.finiteCoefficientRealization W A
  let ffE := Functor.FullyFaithful.ofCompFaithful
    ((Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Plus.ι ⋙ E.mapDerivedCategory)).ofIso
        E.mapDerivedCategoryPlusCompatibility.symm)
  have : E.mapDerivedCategoryPlus.Faithful := ffE.faithful
  let ffL := Functor.FullyFaithful.ofCompFaithful
    (((ProEtale.siteComparison_boundedBelow W A).1.some).ofIso
      (Functor.mapDerivedCategoryPlusCompIso L E))
  let ffJ := Functor.FullyFaithful.ofCompFaithful
    ((Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Plus.ι ⋙ EJ.mapDerivedCategory)).ofIso
        EJ.mapDerivedCategoryPlusCompatibility.symm)
  let ffK := Functor.FullyFaithful.ofCompFaithful
    ((Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Plus.ι ⋙ EK.mapDerivedCategory)).ofIso
        EK.mapDerivedCategoryPlusCompatibility.symm)
  have : EK.mapDerivedCategoryPlus.Faithful := ffK.faithful
  let square := (Functor.mapDerivedCategoryPlusCompIso F EK).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (exceptionalSiteInverse O ell W S n) ≪≫
    Functor.mapDerivedCategoryPlusCompIso EJ L
  let ffF := Functor.FullyFaithful.ofCompFaithful ((ffJ.comp ffL).ofIso square.symm)
  let ff := ffF.comp (Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι)
  let ff' := ff.ofIso F.mapDerivedCategoryPlusCompatibility
  have hb : Function.Bijective
      (F.mapDerivedCategory.map : (X ⟶ Y) → _) := by
    let X' : DerivedCategory.Plus _ := ⟨X, hX⟩
    let Y' : DerivedCategory.Plus _ := ⟨Y, hY⟩
    constructor
    · intro f g hfg
      have hh : (ObjectProperty.homMk f : X' ⟶ Y') = ObjectProperty.homMk g :=
        (ff'.map_bijective X' Y').1 hfg
      exact congrArg (fun k : X' ⟶ Y' ↦ k.hom) hh
    · intro f
      obtain ⟨g, hg⟩ := (ff'.map_bijective X' Y').2 f
      exact ⟨g.hom, hg⟩
  let e := exactDerivedIso F FD fac
  have he (f : X ⟶ Y) :
      e.inv.app X ≫ FD.map f ≫ e.hom.app Y = F.mapDerivedCategory.map f := by
    rw [e.hom.naturality]
    simp
  constructor
  · intro f g hfg
    apply hb.1
    rw [← he f, ← he g, hfg]
  · intro f
    obtain ⟨g, hg⟩ := hb.2 (e.inv.app X ≫ f ≫ e.hom.app Y)
    refine ⟨g, ?_⟩
    apply (cancel_epi (e.inv.app X)).1
    apply (cancel_mono (e.hom.app Y)).1
    simpa only [Category.assoc] using (he g).trans hg

end

private theorem exceptional_inverse_scalar_transpose
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {CY : A ⥤ B} {RY : B ⥤ A} (ay : CY ⊣ RY)
    {CX : C ⥤ D} {RX : D ⥤ C} (ax : CX ⊣ RX)
    {Fm : A ⥤ C} {Gm : C ⥤ A} (am : Fm ⊣ Gm)
    {Fn : B ⥤ D} {Gn : D ⥤ B} (an : Fn ⊣ Gn)
    (γ : CY ⋙ Fn ≅ Fm ⋙ CX) (δ : RX ⋙ Gm ≅ Gn ⋙ RY)
    (hδ : ∀ (P : A) (Q : D) (f : Fn.obj (CY.obj P) ⟶ Q),
      ay.homEquiv P (Gn.obj Q) (an.homEquiv _ Q f) =
        am.homEquiv P (RX.obj Q)
          (ax.homEquiv (Fm.obj P) Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q)
    (β : RY ⋙ Fm ≅ Fn ⋙ RX)
    (hβ : ∀ Y, am.homEquiv _ _ (β.hom.app Y) =
      RY.map (an.unit.app Y) ≫ δ.inv.app (Fn.obj Y))
    (X : A) (Y : B) (f : CY.obj X ⟶ Y) :
    ax.homEquiv _ _ (γ.inv.app X ≫ Fn.map f) =
      Fm.map (ay.homEquiv _ _ f) ≫ β.hom.app Y := by
  apply (am.homEquiv X _).injective
  apply (cancel_mono (δ.hom.app (Fn.obj Y))).mp
  calc
    _ = ay.homEquiv _ _ (an.homEquiv _ _ (Fn.map f)) := (hδ X (Fn.obj Y) _).symm
    _ = ay.homEquiv _ _ f ≫ RY.map (an.unit.app Y) := by
      have hn : an.homEquiv _ _ (Fn.map f) = f ≫ an.unit.app Y := by
        rw [Adjunction.homEquiv_unit]
        exact (an.unit.naturality f).symm
      rw [hn, ay.homEquiv_naturality_right]
    _ = _ := by
      have hb : am.homEquiv (RY.obj Y) (RX.obj (Fn.obj Y)) (β.hom.app Y) =
          RY.map (an.unit.app Y) ≫ δ.inv.app (Fn.obj Y) := hβ Y
      rw [am.homEquiv_naturality_left, hb]
      simp only [Category.assoc, Iso.inv_hom_id_app]
      dsimp only [Functor.comp_obj]
      rw [Category.comp_id]

/-- Transport an adjoint transpose through isomorphisms of its source and target. -/
private theorem exceptional_transpose_conjugate
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X X' : C} {Y Y' : D} (eX : X ≅ X') (eY : Y ≅ Y')
    (f : X ⟶ G.obj Y) (g : F.obj X' ⟶ Y')
    (h : f ≫ G.map eY.hom = eX.hom ≫ adj.homEquiv _ _ g) :
    (adj.homEquiv X Y).symm f = F.map eX.hom ≫ g ≫ eY.inv := by
  apply (adj.homEquiv X Y).injective
  simp only [Equiv.apply_symm_apply, adj.homEquiv_naturality_left,
    adj.homEquiv_naturality_right]
  apply (cancel_mono (G.map eY.hom)).mp
  simpa only [Category.assoc, ← G.map_comp, eY.inv_hom_id, G.map_id,
    Category.comp_id] using h

-- Assemble the derived comparison and all evaluation and scalar-mate clauses.
/-- The site comparison core, before the final evaluation-origin projection.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 09B1.
(blueprint: lem-sf-exceptional-site-origin-comparison-core).

Construct the ordinary and derived comparison at the prescribed evaluation package,
then apply the finite comparison at each quotient level. The system unit and counit
are detected by the evaluations, and the scalar mate squares give normalization. This
statement records the construction and comparison properties; evaluation-origin
projection is handled separately by the preceding exactness lemma. -/
theorem exceptionalSiteOriginComparison_core
    (O : Type (u + 1)) [CommRing O] (ell : O)
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (T : Scheme.{u}) (PE : StrictEtaleEvaluation T O ell) :
    ∃ C : ExceptionalSystemSiteComparison O ell T PE,
      ExceptionalSystemSiteEquivalence C ∧
      (∀ n M, (∃ a : ℤ, M.IsGE a) →
        IsIso ((C.image.level n).adjunction.unit.app M)) ∧
      (∀ n M, C.levelOrigin n M →
        IsIso ((C.image.level n).adjunction.counit.app M)) ∧
      (∀ n M, (∃ a : ℤ, M.IsGE a) →
        C.levelOrigin n ((C.image.level n).inverse.obj M)) := by
  obtain ⟨PX⟩ := exceptionalProEvaluation_exists T O ell
  have := Scheme.preservesFiniteLimits_proEtaleSiteComparison T
  obtain ⟨S⟩ := coefficientSystemOrdinaryImage_exists O ell
    (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt T)
      (Type (u + 1)) T.smallEtaleTopology (Scheme.ProEt.topology T)) _
    (Scheme.proEtaleSiteComparison T)
  obtain ⟨U⟩ := coefficientSystemUnboundedComparison O ell
    (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt T)
      (Type (u + 1)) T.smallEtaleTopology (Scheme.ProEt.topology T)) _
    (Scheme.proEtaleSiteComparison T) S PE PX
  have hlim : PreservesFiniteLimits S.inverse := S.systemExact.1
  have hcolim : PreservesFiniteColimits S.inverse := S.systemExact.2
  have hlevelLim (n : ℕ) : PreservesFiniteLimits (S.lift n).modules :=
    (S.inverseExact n).1
  have hlevelColim (n : ℕ) : PreservesFiniteColimits (S.lift n).modules :=
    (S.inverseExact n).2
  have hevalLim (n : ℕ) : PreservesFiniteLimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact.{u + 1, u, u + 1} n).1
  have hevalColim (n : ℕ) : PreservesFiniteColimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact.{u + 1, u, u + 1} n).2
  have heval (n : ℕ) (M : DerivedCategory (CoefficientSystem
      (J := T.smallEtaleTopology) O ell)) (a : ℤ) [M.IsGE a] :
      ((PE.evaluation n).obj M).IsGE a :=
    exactDerived_isGE (coefficientEvaluation (J := T.smallEtaleTopology)
      (O := O) (ell := ell) n) (PE.evaluation n) (PE.evaluationFactors n) M a
  let I : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := T.smallEtaleTopology) (K := Scheme.ProEt.topology T)
      O ell _ _ (Scheme.proEtaleSiteComparison T) S PE PX := {
    construction := U
    detectsIso := coefficientEvaluation_detectsIso O ell PX
    boundedBelow := by
      rintro M ⟨a, ha⟩
      have : PreservesFiniteLimits S.inverse := S.systemExact.1
      have : PreservesFiniteColimits S.inverse := S.systemExact.2
      exact ⟨a, exactDerivedAdjunction_isGE S.inverse U.evaluation.system.inverse
        U.evaluation.system.inverseFactors U.evaluation.system.adjunction M a⟩
    origin := by
      intro hfull M hM horigin
      have hlevelLim (n : ℕ) : PreservesFiniteLimits (S.lift n).modules :=
        (S.inverseExact n).1
      have hlevelColim (n : ℕ) : PreservesFiniteColimits (S.lift n).modules :=
        (S.inverseExact n).2
      have hc (n : ℕ) : IsIso
          ((U.evaluation.level n).adjunction.counit.app ((PX.evaluation n).obj M)) := by
        obtain ⟨H, hH, ⟨e⟩⟩ := horigin n
        exact exactDerivedAdjunction_counit_isIso_of_origin (S.lift n).modules
          (U.evaluation.level n).inverse (U.evaluation.level n).inverseFactors
          (U.evaluation.level n).adjunction (hfull n) _ H hH e
      constructor
      · apply (coefficientEvaluation_detectsIso O ell PX _).2
        intro n
        rw [← U.evaluation.counit n M]
        infer_instance
      · intro hnorm m n h
        have hreflect : (U.evaluation.level n).inverse.ReflectsIsomorphisms :=
          exactDerived_reflectsIso_of_boundedBelow_faithful (S.lift n).modules
            (U.evaluation.level n).inverse (U.evaluation.level n).inverseFactors
            (fun A B hA hB ↦ (hfull n A B hA hB).1)
        have hnorm' := hnorm h
        exact isIso_scalar_transpose_of_mate (PE.scalar h).derivedAdj
          (PX.scalar h).derivedAdj (U.evaluation.level m).adjunction
          (U.evaluation.level n).adjunction (U.scalar.derivedTensor h)
          (U.scalar.restrictedDirect h) (U.scalar.restrictedDirect_mate h)
          ((U.evaluation.directEvaluation m).app M)
          ((U.evaluation.directEvaluation n).app M)
          ((PE.transition h).app (U.evaluation.system.direct.obj M))
          ((PX.transition h).app M) (U.scalar.directTransition h M) }
  let C : ExceptionalSystemSiteComparison O ell T PE := ⟨PX, S, I⟩
  have hfull (n : ℕ) := exceptionalLevel_full O ell T S n
    (I.level n).inverse (I.level n).inverseFactors
  have hlunit (n : ℕ) (M : DerivedCategory (strictEtaleLevel T O ell n))
      (hM : ∃ a : ℤ, M.IsGE a) : IsIso ((I.level n).adjunction.unit.app M) := by
    have hreflect : (I.level n).inverse.ReflectsIsomorphisms :=
      exactDerived_reflectsIso_of_boundedBelow_faithful (S.lift n).modules
        (I.level n).inverse (I.level n).inverseFactors
        (fun A B hA hB ↦ (hfull n A B hA hB).1)
    have hc : IsIso ((I.level n).adjunction.counit.app ((I.level n).inverse.obj M)) :=
      exactDerivedAdjunction_counit_isIso_of_origin (S.lift n).modules
        (I.level n).inverse (I.level n).inverseFactors (I.level n).adjunction
        (hfull n) _ M hM (Iso.refl _)
    have hi : IsIso ((I.level n).inverse.map ((I.level n).adjunction.unit.app M) ≫
        (I.level n).adjunction.counit.app ((I.level n).inverse.obj M)) := by
      rw [(I.level n).adjunction.left_triangle_components M]
      exact ⟨𝟙 _, by simp, by simp⟩
    have : IsIso ((I.level n).inverse.map ((I.level n).adjunction.unit.app M)) :=
      IsIso.of_isIso_comp_right
        ((I.level n).inverse.map ((I.level n).adjunction.unit.app M))
        ((I.level n).adjunction.counit.app ((I.level n).inverse.obj M))
    exact isIso_of_reflects_iso _ (I.level n).inverse
  refine ⟨C, ?_, hlunit, ?_, ?_⟩
  · refine {
      inverseBound := ?_
      directBound := ?_
      unit := ?_
      counit := ?_
      inverseOrigin := ?_
      inverseNormalized := ?_
      directNormalized := ?_ }
    · intro a M hM
      exact exactDerived_isGE S.inverse I.system.inverse I.system.inverseFactors M a
    · intro a M hM
      exact exactDerivedAdjunction_isGE S.inverse I.system.inverse
        I.system.inverseFactors I.system.adjunction M a
    · rintro M ⟨a, ha⟩
      apply (coefficientEvaluation_detectsIso O ell PE _).2
      intro n
      have := hlunit n ((PE.evaluation n).obj M) ⟨a, heval n M a⟩
      have hi : IsIso ((PE.evaluation n).map (I.system.adjunction.unit.app M) ≫
          (I.directEvaluation n).hom.app (I.system.inverse.obj M) ≫
          (I.level n).direct.map ((I.inverseEvaluation n).hom.app M)) := by
        rw [I.unit n M]
        infer_instance
      exact IsIso.of_isIso_comp_right
        ((PE.evaluation n).map (I.system.adjunction.unit.app M))
        ((I.directEvaluation n).hom.app (I.system.inverse.obj M) ≫
          (I.level n).direct.map ((I.inverseEvaluation n).hom.app M))
    · intro M hM
      exact (I.origin hfull M hM.1 hM.2).1
    · rintro M ⟨a, ha⟩
      refine ⟨⟨a, exactDerived_isGE S.inverse I.system.inverse
        I.system.inverseFactors M a⟩, ?_⟩
      intro n
      exact ⟨(PE.evaluation n).obj M, ⟨a, heval n M a⟩,
        ⟨((I.inverseEvaluation n).app M).symm⟩⟩
    · intro M hM hnorm m n h
      let em := (I.inverseEvaluation m).app M
      let en := (I.inverseEvaluation n).app M
      let z := ((PE.scalar h).derivedAdj.homEquiv _ _).symm ((PE.transition h).app M)
      have hz : IsIso z := hnorm h
      let g := (I.derivedTensor h).inv.app ((PE.evaluation m).obj M) ≫
        (I.level n).inverse.map z
      have hg : (PX.scalar h).derivedAdj.homEquiv _ _ g =
          (I.level m).inverse.map ((PE.transition h).app M) ≫
            (I.restrictedInverse h).hom.app ((PE.evaluation n).obj M) := by
        simpa only [z, Equiv.apply_symm_apply] using
          exceptional_inverse_scalar_transpose (PE.scalar h).derivedAdj
            (PX.scalar h).derivedAdj (I.level m).adjunction (I.level n).adjunction
            (I.derivedTensor h) (I.restrictedDirect h) (I.restrictedDirect_mate h)
            (I.restrictedInverse h) (I.restrictedInverse_mate h)
            ((PE.evaluation m).obj M) ((PE.evaluation n).obj M) z
      have he : ((PX.scalar h).derivedAdj.homEquiv _ _).symm
          ((PX.transition h).app (I.system.inverse.obj M)) =
          (PX.scalar h).derived.map em.hom ≫ g ≫ en.inv := by
        apply exceptional_transpose_conjugate (PX.scalar h).derivedAdj em en _ g
        dsimp only [Functor.comp_obj] at hg ⊢
        have ht := I.inverseTransition h M
        change (PX.transition h).app (I.system.inverse.obj M) ≫
            (PX.scalar h).restriction.map en.hom = em.hom ≫
            (I.level m).inverse.map ((PE.transition h).app M) ≫
            (I.restrictedInverse h).hom.app ((PE.evaluation n).obj M) at ht
        simpa only [hg, Category.assoc] using ht
      rw [he]
      dsimp only [g]
      infer_instance
    · intro M hM hnorm
      exact (I.origin hfull M hM.1 hM.2).2 hnorm
  · intro n M hM
    obtain ⟨N, hN, ⟨e⟩⟩ := hM.2
    exact exactDerivedAdjunction_counit_isIso_of_origin (S.lift n).modules
      (I.level n).inverse (I.level n).inverseFactors (I.level n).adjunction
      (hfull n) M N hN e
  · intro n M hM
    obtain ⟨a, ha⟩ := hM
    exact ⟨⟨a, exactDerived_isGE (S.lift n).modules (I.level n).inverse
      (I.level n).inverseFactors M a⟩, M, ⟨a, ha⟩, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry
