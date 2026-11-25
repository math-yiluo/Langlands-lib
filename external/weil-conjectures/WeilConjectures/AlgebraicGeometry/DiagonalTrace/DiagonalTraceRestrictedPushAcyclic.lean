/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceRestrictionRingedModels
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportScalarProofs
import all WeilConjectures.SmoothPurity.Supporting.NativeConstantRestrictionAcyclicity
import all WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Acyclicity after scalar restriction for direct image -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

attribute [local instance 200000] SheafOfModules.instAbelian
attribute [local instance 100000] WeilConjectures.NativeConstantModel.sequenceSmall
  WeilConjectures.NativeConstantModel.sequenceAbSheafify
  WeilConjectures.NativeConstantModel.sequenceAbLocallyBijective
  WeilConjectures.NativeConstantModel.geometricContinuous
  WeilConjectures.NativeConstantModel.siteSmall
  WeilConjectures.NativeConstantModel.siteAbSheafify
  WeilConjectures.NativeConstantModel.siteAbLocallyBijective

private theorem unit_isIso_of_resolution
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{u} A] [HasDerivedCategory.{u} B]
    [HasKInjectiveResolutions A] (G : A ⥤ B) [G.Additive]
    (R : DiagonalRightDerived G) (K : CochainComplex A ℤ)
    (h : ∀ (J : CochainComplex A ℤ), J.IsKInjective →
      ∀ (j : K ⟶ J), QuasiIso j →
        QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j)) :
    IsIso (R.η.app K) := by
  obtain ⟨J, hJ, j, _, hj⟩ := HasKInjectiveResolutions.exists_isKInjective K
  have : QuasiIso j := hj
  have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) := h J hJ j hj
  have : IsIso (R.η.app J) := R.computation J hJ
  have hn := R.η.naturality j
  dsimp only [Functor.comp_map] at hn
  have : IsIso (R.η.app K ≫ R.R.map (DerivedCategory.Q.map j)) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (R.R.map (DerivedCategory.Q.map j))

private def comparisonInverse
    {M C D : Type*} [Category M] [Category C] [Category D]
    (e : C ≌ D) (r : M ⥤ C) (H : M ⥤ D) (a : r ⋙ e.functor ≅ H) :
    (𝟭 M) ⋙ r ≅ H ⋙ e.inverse :=
  Functor.leftUnitor r ≪≫ Functor.isoWhiskerLeft r e.unitIso ≪≫
    (Functor.associator r e.functor e.inverse).symm ≪≫ Functor.isoWhiskerRight a e.inverse

open AlgebraicGeometry.ProEtale in
private def constantSectionsIso (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    SheafOfModules.restrictScalars
        ((constantCommuteCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of A)).inv ⋙
      constantRingModuleRestriction (Scheme.ProEt.topology X) A ≅
        scalarSectionsAt X A := by
  let J := Scheme.ProEt.topology X
  let U := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let i := (constantCommuteCompose J U).app (CommRingCat.of A)
  have hf : scalarUnit J A ≫ i.hom.hom =
      toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A)) := by
    dsimp only [i, Iso.app_hom]
    rw [constantCommuteCompose_hom_app_hom]
    unfold scalarUnit
    rw [← Category.assoc, sheafComposeIso_inv_fac]
    exact (toSheafify_naturality J
      (Functor.constComp X.ProEtᵒᵖ (CommRingCat.of A) U).hom).symm.trans (by rfl)
  have hi : toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A)) ≫
      i.inv.hom = scalarUnit J A := by
    rw [← hf, Category.assoc, ObjectProperty.isoHom_inv_id_hom]
    exact Category.comp_id _
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun V ↦ ?_) ?_)) ?_
  · refine ModuleCat.isoMk (Iso.refl _) (fun a ↦ ?_)
    ext x
    exact congrArg (fun b ↦ b • (show M.val.obj V from x))
      (ConcreteCategory.congr_hom (congr_app hi V) a).symm
  · intro V W f
    ext x
    rfl
  · intro M N f
    ext V x
    rfl

private theorem completed_resolution_quasiIso (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (I : CochainComplex (DiagonalCompleted l X) ℤ) [I.IsKInjective]
    (J : CochainComplex (DiagonalMod l X) ℤ) [J.IsKInjective]
    (j : ((diagonalCompletedRestriction l X).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    QuasiIso (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).mapHomologicalComplex
       (.up ℤ)).map j) := by
  let A := ULift.{u + 1} ℤ_[l]
  let RX := scalarRing (Scheme.ProEt.topology X) A
  let RS := scalarRing (Scheme.ProEt.topology S) A
  let a := Scheme.purTwistZlCompletionMap X l
  let b := Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A)
  let r := SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)
  let p := SheafOfModules.pushforward.{u + 1} (F := Scheme.proEtaleBaseChange f)
    (J := Scheme.ProEt.topology S) (K := Scheme.ProEt.topology X)
    (R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)
    (S := (sheafCompose (Scheme.ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RS)
    ((sheafCompose (Scheme.ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map b)
  let EX := scalarSectionsAt X A
  let ES := scalarSectionsAt S A
  have : EX.IsEquivalence := scalarSectionsAt_equiv X A
  have : ES.IsEquivalence := scalarSectionsAt_equiv S A
  have : EX.inv.Additive := EX.inv.additive_of_preserves_binary_products
  have : ES.inv.Additive := ES.inv.additive_of_preserves_binary_products
  have : EX.inv.PreservesHomology := inferInstance
  have : ES.inv.PreservesHomology := inferInstance
  have : EX.inv.PreservesKInjectiveComplexes := inferInstance
  have : ES.inv.ReflectsIsomorphisms := inferInstance
  have : r.Additive := by dsimp only [r]; infer_instance
  have : p.Additive :=
    WeilConjectures.CompactSupportCondensedRealization.scalarSitePushforward_additive _ _
  let H := diagonalCompletedRestriction l X
  let G := lowerStar (ModuleCat.{u + 1} A) f
  let α₀ : r ⋙ EX ≅ H :=
    (Functor.isoWhiskerLeft r (constantSectionsIso X A)).symm
  let α : (𝟭 _) ⋙ r ≅ H ⋙ EX.inv :=
    comparisonInverse EX.asEquivalence r H α₀
  have hb : scalarUnit (Scheme.ProEt.topology S) A ≫
      ((sheafCompose (Scheme.ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map b).hom =
        Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
          (scalarUnit (Scheme.ProEt.topology X) A) := by
    have h := Equiv.apply_symm_apply
      ((sheafificationAdjunction (Scheme.ProEt.topology S) CommRingCat.{u + 1}).homEquiv
        ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of A))
        ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj RX))
      (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
    exact congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) h
  let β₀ : p ⋙ ES ≅ EX ⋙ G :=
    scalarDirectImageIso (Scheme.ProEt.topology X) (Scheme.ProEt.topology S)
      (Scheme.proEtaleBaseChange f) A _ _ _ _ _ hb
  let β : EX.inv ⋙ p ≅ G ⋙ ES.inv := inverseSquare EX ES p G β₀
  apply Scheme.quasiIso_map_of_models (𝟭 _) EX.inv ES.inv r p H G α β ?_ I J j
  intro I hI J hJ j hj
  have : I.IsKInjective := hI
  have : J.IsKInjective := hJ
  have : QuasiIso j := hj
  have : RepresentablyFlat (Scheme.proEtaleBaseChange f) :=
    flat_of_preservesFiniteLimits _
  exact WeilConjectures.CompactSupportCondensedRealization.continuous_scalar_resolution
    (Scheme.ProEt.topology S) (Scheme.ProEt.topology X)
    (Scheme.proEtaleBaseChange f) (Scheme.purTwistZlCompletion X l) RX RS a b I J j

private theorem tower_resolution_quasiIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (f : X ⟶ S) (rX : Restriction l E X)
    (I : CochainComplex (Systems X (Arings l E X)) ℤ) [I.IsKInjective]
    (J : CochainComplex (DiagonalSystems l X) ℤ) [J.IsKInjective]
    (j : ((rX.F).mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j] :
    QuasiIso (((diagonalTraceSystemPush l f).mapHomologicalComplex (.up ℤ)).map j) := by
  obtain ⟨RX, RS, a, b, ex, es, ⟨α₀⟩, ⟨β⟩⟩ :=
    diagonalTrace_restriction_ringedModels l E f rX
  let FA := ex.inverse
  let FB := es.inverse
  have : FA.IsEquivalence := inferInstanceAs ex.inverse.IsEquivalence
  have : FB.IsEquivalence := inferInstanceAs es.inverse.IsEquivalence
  have : FA.Additive := FA.additive_of_preserves_binary_products
  have : FB.Additive := FB.additive_of_preserves_binary_products
  have : FA.PreservesHomology := inferInstance
  have : FB.PreservesHomology := inferInstance
  have : FA.PreservesKInjectiveComplexes := inferInstance
  have : FB.ReflectsIsomorphisms := inferInstance
  let r := SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology X))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)
  let p := SheafOfModules.pushforward.{u + 1}
    (F := ProEtale.VaryingRing.baseChange f)
    (J := WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology S))
    (K := WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology X))
    (R := (sheafCompose (WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology X))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)
    (S := (sheafCompose (WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology S))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RS)
    ((sheafCompose (WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology S))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map b)
  let H := rX.F
  let G := diagonalTraceSystemPush l f
  have : r.Additive := by dsimp only [r]; infer_instance
  have : p.Additive :=
    WeilConjectures.CompactSupportCondensedRealization.scalarSitePushforward_additive _ _
  let α : (𝟭 _) ⋙ r ≅ H ⋙ FA := comparisonInverse ex r H α₀
  apply Scheme.quasiIso_map_of_models (𝟭 _) FA FB r p H G α β ?_ I J j
  intro I hI J hJ j hj
  have : I.IsKInjective := hI
  have : J.IsKInjective := hJ
  have : QuasiIso j := hj
  have : RepresentablyFlat (ProEtale.VaryingRing.baseChange f) := by
    have : RepresentablyFlat (Scheme.proEtaleBaseChange f) :=
      flat_of_preservesFiniteLimits _
    constructor
    intro U
    exact IsCofiltered.of_equivalence
      (StructuredArrow.prodEquivalence U.1 U.2 (𝟭 ℕ) (Scheme.proEtaleBaseChange f)).symm
  exact WeilConjectures.CompactSupportCondensedRealization.continuous_scalar_resolution
    (WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology S))
    (WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology X))
    (ProEtale.VaryingRing.baseChange f) _ RX RS a b I J j

/-- Restricted K-injective complexes are acyclic for geometric direct image,
for the strict finite-coefficient systems and for completed coefficients.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
scalar/direct-image comparison; Stacks Tag 0D6E, composition of ringed-topos
right derived direct images.
(blueprint: lem-sfb-diagonal-trace-restricted-push-acyclic).

Proof: present the strict systems as module sheaves on the sequence site.
The section, transition and residue-action conditions on rX identify its functor
with ordinary restriction along the constant Z_l-to-coefficient-system ring map.
The completed restriction is already the analogous coefficient-ring restriction,
followed by the constant-ring module equivalence. For either ringed site, compose
this identity-site ringed morphism with geometric direct image. Resolve a
K-injective I after scalar restriction by a K-injective J. The ringed-topos
composition theorem shows that applying direct image to this resolution arrow
is a quasi-isomorphism. Its proof uses flat-term K-flat test resolutions:
extension of scalars and geometric pullback take the test resolutions to the
corresponding K-flat classes, and their Hom adjunctions identify the localized
Hom groups into I and J. Yoneda makes the localized direct-image resolution map
invertible. Since scalar restriction is exact, its ordinary value computes its
derived value, so the composite-unit equation makes the direct-image unit on
the restricted I invertible. Transport this fact through the section-preserving
constant-ring and sequence-site presentations. Finally, the universal units of
Rf and Rt determine their unique comparisons with these computed models; their
components are isomorphisms, so the same unit invertibility holds for the given
models. The argument uses no preservation of K-injectives by scalar restriction,
no finite-level K-injectivity assertion, and no invertibility of l on X or S.
For identity maps the unit is already invertible on every complex; empty sites
and the first positive quotient satisfy the same argument.
-/
theorem diagonalTrace_restrictedPush_acyclic (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (rX : Restriction l (ULift.{u} (Padic l)) X)
    (Rf : DiagonalRightDerived
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f))
    (Rt : DiagonalRightDerived (diagonalTraceSystemPush l f)) :
    (∀ I : CochainComplex (Systems X (Arings l (ULift.{u} (Padic l)) X)) ℤ,
      I.IsKInjective →
        IsIso (Rt.η.app ((rX.F.mapHomologicalComplex (.up ℤ)).obj I))) ∧
    (∀ I : CochainComplex (DiagonalCompleted l X) ℤ, I.IsKInjective →
      IsIso (Rf.η.app (((diagonalCompletedRestriction l X).mapHomologicalComplex
        (.up ℤ)).obj I))) := by
  constructor
  · intro I hI
    have : I.IsKInjective := hI
    have : IsGrothendieckAbelian.{u + 1} (DiagonalMod l X) :=
      GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) X
    have : IsGrothendieckAbelian.{u + 1} (DiagonalSystems l X) :=
      CategoryTheory.RingedStrictTowerProof.tower_grothendieck (DiagonalMod l X)
    apply unit_isIso_of_resolution _ Rt
    intro J hJ j hj
    have : J.IsKInjective := hJ
    have : QuasiIso j := hj
    exact tower_resolution_quasiIso l (ULift.{u} (Padic l)) f rX I J j
  · intro I hI
    have : I.IsKInjective := hI
    have : IsGrothendieckAbelian.{u + 1} (DiagonalMod l X) :=
      GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) X
    apply unit_isIso_of_resolution _ Rf
    intro J hJ j hj
    have : J.IsKInjective := hJ
    have : QuasiIso j := hj
    exact completed_resolution_quasiIso l f I J j

end AlgebraicGeometry.ProEtale.DiagonalTrace
