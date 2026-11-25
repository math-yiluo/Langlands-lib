/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingRestrictionSquare
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedReductionPullbackSquare
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteReductionExchangeRectangle
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement

/-! # Strict tower exchange and the canonical mate

Source: literature/blueprint/master/blueprint/sec-proper-base-change/
sk-thm-properbasechange/lemma-weil-pbc-completed-exchange-coherence.md,
proof, first two sentences; Stacks Tag 07A7
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization).

The comparison functors are termwise functors on module towers, localized only
**after** forming the tower category. The strict finite exchange is the
projection-formula realization in `CompletedTowerCompatibility`. Restriction
comparisons retain their normalization on ordinary modules and K-injectives.

## Main definitions

* `exchangeTowerRes`: exact coefficient restriction on strict derived towers.
* `StrictTowerRingedSquare.exchangeTowerMate`: the canonical termwise adjunction mate.
* `exchangeCornerB`, `exchangeCornerD`: the specified natural corner comparisons.
* `strictTowerExchangeMateNormalization`: strict realization and mate equality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Avoid replaying the large dependent coefficient transports for tactic linting.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicDerivedChange

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private theorem exchangeAdjunctCompComparison {C D E : Type*}
    [Category C] [Category D] [Category E]
    {Lg : C ⥤ D} {Rg : D ⥤ C} {Lf : D ⥤ E} {Rf : E ⥤ D}
    {L : C ⥤ E} {R : E ⥤ C}
    (adjg : Lg ⊣ Rg) (adjf : Lf ⊣ Rf) (adj : L ⊣ R)
    (e : Rf ⋙ Rg ≅ R) {A : C} {B : D} {T : E}
    (h : A ⟶ Rg.obj B) (k : B ⟶ Rf.obj T) :
    (adj.homEquiv A T).symm (h ≫ Rg.map k ≫ e.hom.app T) =
      ((conjugateEquiv (adjg.comp adjf) adj).symm e.hom).app A ≫
        Lf.map ((adjg.homEquiv A B).symm h) ≫ (adjf.homEquiv B T).symm k := by
  apply (adj.homEquiv A T).injective
  rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_right]
  change _ = (adj.unit.app A ≫ R.map _) ≫ R.map _
  rw [← unit_conjugateEquiv_symm (adjg.comp adjf) adj e.hom A,
    Category.assoc, ← e.hom.naturality]
  conv_rhs => rw [← Category.assoc]
  change _ = ((adjg.comp adjf).homEquiv A T)
    (Lf.map ((adjg.homEquiv A B).symm h) ≫ (adjf.homEquiv B T).symm k) ≫ _
  rw [Adjunction.comp_homEquiv]
  change _ = (adjg.homEquiv _ _) ((adjf.homEquiv _ _) _) ≫ _
  rw [adjf.homEquiv_naturality_left, Equiv.apply_symm_apply,
    adjg.homEquiv_naturality_right, Equiv.apply_symm_apply]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem exchangeConstantComparisonComp {X Y Z : Scheme.{t}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : CommRingCat.{t + 1}) :
    (proEtaleConstantComparison (f ≫ g)).app A =
      (proEtaleRingInverseImageComp f g).hom.app
        ((constantSheaf (ProEt.topology Z) CommRingCat.{t + 1}).obj A) ≫
          (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
            ((proEtaleConstantComparison g).app A) ≫
          (proEtaleConstantComparison f).app A := by
  let e := Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp
      (P := @WeaklyEtale) (Q := ⊤) f g).symm) CommRingCat.{t + 1}
        (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)
  have hρ : proEtaleConstantDirectImageMap (f ≫ g) CommRingCat.{t + 1} A =
      proEtaleConstantDirectImageMap g CommRingCat.{t + 1} A ≫
        (proEtaleSheafDirectImage g CommRingCat.{t + 1}).map
          (proEtaleConstantDirectImageMap f CommRingCat.{t + 1} A) ≫
            e.hom.app ((constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).obj A) := by
    apply ((sheafificationAdjunction (ProEt.topology Z) CommRingCat.{t + 1}).homEquiv
      ((Functor.const Z.ProEtᵒᵖ).obj A) _).injective
    rw [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right]
    rw [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
    apply NatTrans.ext
    funext U
    have hf := Equiv.apply_symm_apply
      ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{t + 1}).homEquiv
        ((Functor.const Y.ProEtᵒᵖ).obj A)
          ((proEtaleSheafDirectImage f CommRingCat.{t + 1}).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).obj A)))
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
    have hfU := congrArg (fun t ↦ t.app ((proEtaleBaseChange g).op.obj U)) hf
    change (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange g).op.obj U) ≫
      (proEtaleConstantDirectImageMap f CommRingCat.{t + 1} A).hom.app
        ((proEtaleBaseChange g).op.obj U) =
          (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
            ((proEtaleBaseChange f).op.obj ((proEtaleBaseChange g).op.obj U)) at hfU
    change (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange (f ≫ g)).op.obj U) =
      ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
          ((proEtaleBaseChange g).op.obj U) ≫
        (proEtaleConstantDirectImageMap f CommRingCat.{t + 1} A).hom.app
          ((proEtaleBaseChange g).op.obj U)) ≫
            ((constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).obj A).obj.map
              ((MorphismProperty.Over.pullbackComp
                (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U.unop).op
    rw [hfU]
    have h := (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
      ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U.unop).op
    change 𝟙 A ≫ _ = _ at h
    rw [Category.id_comp] at h
    exact h
  change ((proEtaleSheafAdjunction (f ≫ g) CommRingCat.{t + 1}).homEquiv _ _).symm _ = _
  rw [hρ]
  exact exchangeAdjunctCompComparison (proEtaleSheafAdjunction g CommRingCat.{t + 1})
    (proEtaleSheafAdjunction f CommRingCat.{t + 1})
    (proEtaleSheafAdjunction (f ≫ g) CommRingCat.{t + 1}) e
    (proEtaleConstantDirectImageMap g CommRingCat.{t + 1} A)
    (proEtaleConstantDirectImageMap f CommRingCat.{t + 1} A)

/-- Constant coefficient identifications agree around the chosen scheme square.
Source: strict normalization, proof steps 5--6; Stacks 07A7
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization).
Proof: the two coefficient maps send every constant a to the constant a on X'.
The sheafification universal property identifies them. Transporting along the
commutativity of the scheme square gives the displayed heterogeneous equality. -/
theorem exchangeConstant_coherent (sq : ChosenCartesianSquare g' f' f g) :
    HEq (proEtaleRingCompositeCoefficients g' f
      (exchangeConstantRing Y A) (exchangeConstantRing X A) (exchangeConstantRing X' A)
      (exchangeConstantIso f A) (exchangeConstantIso g' A))
      (proEtaleRingCompositeCoefficients f' g
        (exchangeConstantRing Y A) (exchangeConstantRing Y' A) (exchangeConstantRing X' A)
        (exchangeConstantIso g A) (exchangeConstantIso f' A)) := by
  have hc {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V) :
      proEtaleRingCompositeCoefficients h k
        (exchangeConstantRing V A) (exchangeConstantRing W A) (exchangeConstantRing Z A)
        (exchangeConstantIso k A) (exchangeConstantIso h A) =
      exchangeConstantIso (h ≫ k) A := by
    apply Iso.ext
    exact (exchangeConstantComparisonComp h k (CommRingCat.of A)).symm
  have hw : HEq (exchangeConstantIso (g' ≫ f) A) (exchangeConstantIso (f' ≫ g) A) :=
    congr_arg_heq (fun u ↦ exchangeConstantIso u A) sq.w
  exact (heq_of_eq (hc g' f)).trans (hw.trans (heq_of_eq (hc f' g).symm))

/-- The constant-coefficient ringed square uses the specific constant-section identifications.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeConstantSquare (sq : ChosenCartesianSquare g' f' f g) :
    StrictTowerRingedSquare sq where
  RY := exchangeConstantRing Y A
  RX := exchangeConstantRing X A
  RY' := exchangeConstantRing Y' A
  RX' := exchangeConstantRing X' A
  cf := exchangeConstantIso f A
  cg := exchangeConstantIso g A
  cg' := exchangeConstantIso g' A
  cf' := exchangeConstantIso f' A
  coherent := exchangeConstant_coherent sq

/-- The coefficient map sends a constant to its compatible residues in the finite tower.
Source: strict normalization, proof step 5; Stacks 099M
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
abbrev exchangeScalar (T : Scheme.{t}) : exchangeConstantRing T A ⟶ d.completedRing T :=
  adicDatumScalar T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite } ≫ (pbcCompletedComparison T d).hom

/-- The scalar maps commute with the canonical coefficient inverse images.
Source: strict normalization, proof step 5; Stacks 099M
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization).
Proof: compose the two maps with each finite projection. The profinite comparison
projection formula and naturality of the constant-section map identify both maps
with the constant quotient section a mod I^(n+1). Projections of the completed ring
are jointly monic, so the two scalar maps agree. -/
theorem exchangeScalar_comm {U V : Scheme.{t}} (f : U ⟶ V) :
    (exchangeConstantIso f A).hom ≫ exchangeScalar d U =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map (exchangeScalar d V) ≫
        (d.integralRingIso f).hom := by
  have hp (T : Scheme.{t}) (n : ℕ) :
      exchangeScalar d T ≫ d.projection T n =
        (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
            (pbcLevelConstantComparison T d n).hom := by
    dsimp only [exchangeScalar, AdicCoefficientDatum.projection,
      completedReductionProjection, pbcCompletedComparison]
    rw [Category.assoc]
    erw [HasLimit.isoOfNatIso_hom_π]
    rw [← Category.assoc]
    erw [(adicDatumScalar_exists T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite }).exists.choose_spec n]
    rfl
  apply limit.hom_ext (F := reductionCoefficientSystem U d)
  intro n
  change _ ≫ d.projection U n.unop = _ ≫ d.projection U n.unop
  rw [Category.assoc, hp, Category.assoc, d.projection_comm]
  rw [← Functor.map_comp_assoc, hp]
  simp only [AdicCoefficientDatum.finiteRingIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom, exchangeConstantIso]
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  dsimp only [AdicCoefficientDatum.ringTower, Functor.ofOpSequence,
    Functor.ofSequence, Functor.leftOp]
  simpa only [Category.assoc, Functor.comp_map] using
    congrArg (fun z ↦ z ≫ (pbcLevelConstantComparison U d n.unop).hom)
    ((proEtaleConstantComparison f).naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n.unop + 1))))).symm

/-- Termwise restriction changes the scalar action but retains the whole strict diagram.
Source: strict normalization, paragraph 2; Stacks 03D3
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
abbrev exchangeTowerModuleRes (T : Scheme.{t}) :
    exchangeTowers T (d.completedRing T) ⥤ exchangeTowers T (exchangeConstantRing T A) :=
  (Functor.whiskeringRight _ _ _).obj (proEtaleRingRestrictScalars (exchangeScalar d T))

set_option backward.isDefEq.respectTransparency.types false in
private theorem termwiseRightAdjoint_kinjective
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {E : C ⥤ D} {F : D ⥤ C} [E.Additive] [F.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E] (adj : E ⊣ F) :
    ((Functor.whiskeringRight ℕᵒᵖ D C).obj F).PreservesKInjectiveComplexes := by
  have : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj E) :=
    ⟨fun J _ _ ↦ whiskeringRight_preservesLimitsOfShape (C := ℕᵒᵖ) (J := J) E⟩
  have : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj E) :=
    ⟨fun J _ _ ↦ whiskeringRight_preservesColimitsOfShape (C := ℕᵒᵖ) (J := J) E⟩
  exact (adj.whiskerRight ℕᵒᵖ).preservesKInjectiveComplexes

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exchangeTowerModuleRes_kinjective (T : Scheme.{t}) :
    (exchangeTowerModuleRes d T).PreservesKInjectiveComplexes := by
  letI : IsNoetherianRing A := d.noetherian
  let c := exchangeScalar d T
  have hc : ∀ n : ℕ, c ≫ (pbcCompletedComparison T d).inv ≫
      limit.π (adicLisseRingSystem T d.ideal) (op n) =
      (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) := by
    intro n
    dsimp only [c, exchangeScalar]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (adicDatumScalar_exists T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite }).exists.choose_spec n
  have he := (completed_constant_algebra_flat_quotients T d.ideal _
    (pbcCompletedComparison T d) c hc).2.1
  have : PreservesFiniteLimits (completedAdicChange T c) := he.1
  have : PreservesFiniteColimits (completedAdicChange T c) := he.2
  obtain ⟨_, _, h⟩ :=
    SheafOfModules.sheafRingCoefficientOrdinaryAdjunction.{t + 1, t + 1, t} c
  let adj : completedAdicChange T c ⊣ proEtaleRingRestrictScalars c :=
    (h (completedAdicChange T c)
      (completedAdicChangeData T c).choose_spec.choose
      (completedAdicChangeData T c).choose_spec.choose_spec.choose).choose
  exact termwiseRightAdjoint_kinjective
    (E := completedAdicChange T c) (F := proEtaleRingRestrictScalars c) adj

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of restriction on strict diagrams, with all transition maps retained.
Source: strict normalization, proof step 5; Stacks 03D3
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization).
Proof: ordinary restriction changes only the ring action and preserves kernels
and cokernels. These are computed pointwise in the strict functor category, giving
both finite-limit and finite-colimit preservation for the termwise functor. -/
theorem exchangeTowerModuleRes_exact (T : Scheme.{t}) :
    PreservesFiniteLimits (exchangeTowerModuleRes d T) ∧
      PreservesFiniteColimits (exchangeTowerModuleRes d T) := by
  have : PreservesFiniteLimits (proEtaleRingRestrictScalars (exchangeScalar d T)) :=
    proEtaleRingRestrictScalars_preservesFiniteLimits (exchangeScalar d T)
  have : PreservesFiniteColimits (proEtaleRingRestrictScalars (exchangeScalar d T)) :=
    proEtaleRingRestrictScalars_preservesFiniteColimits (exchangeScalar d T)
  constructor
  · exact ⟨fun _ _ _ ↦ inferInstance⟩
  · refine ⟨fun J _ _ ↦ ?_⟩
    let R : Sheaf (ProEt.topology T) RingCat.{t + 1} :=
      (sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (d.completedRing T)
    have hS : HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} := inferInstance
    have hW : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
      WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T
    have hP : HasColimitsOfShape J (_root_.PresheafOfModules.{t + 1} R.obj) := inferInstance
    have :=
      @SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf.{
        0, 0, t + 1, t, t + 1, t + 1} _ _ _ R hS hW J _ hP
    exact whiskeringRight_preservesColimitsOfShape.{0, 0, t + 1, t + 2, t + 1, t + 2, 0, 0}
      (C := ℕᵒᵖ) (J := J) (proEtaleRingRestrictScalars (exchangeScalar d T))

/-- Left exact restriction. Source: strict normalization, proof step 5
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
instance exchangeTowerModuleRes_finiteLimits (T : Scheme.{t}) :
    PreservesFiniteLimits (exchangeTowerModuleRes d T) := (exchangeTowerModuleRes_exact d T).1

/-- Right exact restriction. Source: strict normalization, proof step 5
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
instance exchangeTowerModuleRes_finiteColimits (T : Scheme.{t}) :
    PreservesFiniteColimits (exchangeTowerModuleRes d T) := (exchangeTowerModuleRes_exact d T).2

/-- Exact restriction on derived strict towers.
Source: strict normalization, paragraph 2; Stacks 03D3
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
abbrev exchangeTowerRes (T : Scheme.{t}) :
    DerivedCategory (exchangeTowers T (d.completedRing T)) ⥤
      DerivedCategory (exchangeTowers T (exchangeConstantRing T A)) :=
  (exchangeTowerModuleRes d T).mapDerivedCategory

/-- Constant-coefficient inverse image on derived strict towers.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
abbrev exchangeConstantPull {U V : Scheme.{t}} (f : U ⟶ V) :=
  exchangeTowerPull f (exchangeConstantRing V A) (exchangeConstantRing U A)
    (exchangeConstantIso f A)

/-- Total right derived constant-coefficient direct image on strict towers.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
abbrev exchangeConstantPush {U V : Scheme.{t}} (f : U ⟶ V) :=
  exchangeTowerPush f (exchangeConstantRing V A) (exchangeConstantRing U A)
    (exchangeConstantIso f A)

/-- The ordinary scalar-restriction comparison before forming strict diagrams.
Source: Stacks Tag 0D6D
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeOrdinaryResPull {U V : Scheme.{t}} (f : U ⟶ V) :
    proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f) ⋙ proEtaleRingRestrictScalars (exchangeScalar d U) ≅
      proEtaleRingRestrictScalars (exchangeScalar d V) ⋙
        proEtaleRingModulePullback f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A) :=
  (@asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv f
    (exchangeConstantRing V A) (d.completedRing V)
    (exchangeConstantRing U A) (d.completedRing U)
    (exchangeScalar d V) (exchangeScalar d U)
    (exchangeConstantIso f A) (d.integralRingIso f) (exchangeScalar_comm d f))
    (proEtaleRingRestrictionPullbackInv_isIso f
      (exchangeConstantRing V A) (d.completedRing V)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d V) (exchangeScalar d U)
      (exchangeConstantIso f A) (d.integralRingIso f) (exchangeScalar_comm d f))).symm

/-- The ordinary restriction/pullback comparison is the termwise normalized module mate.
Source: strict normalization, proof step 5; Stacks 0D6D
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeModuleResPull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerModulePull f ⋙ exchangeTowerModuleRes d U ≅
      exchangeTowerModuleRes d V ⋙ exchangeTowerModulePull f
        (exchangeConstantRing V A) (exchangeConstantRing U A) (exchangeConstantIso f A) :=
  NatIso.ofComponents
    (fun M ↦ Functor.isoWhiskerLeft M (exchangeOrdinaryResPull d f)) (by
      intro M N a
      apply NatTrans.ext
      funext n
      exact (exchangeOrdinaryResPull d f).hom.naturality (a.app n))

/-- The derived comparison is exact descent of the ordinary identity on inverse-image sheaves.
Source: strict normalization, proof step 5; Stacks 0D6D
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeResPull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerPull f ⋙ exchangeTowerRes d U ≅
      exchangeTowerRes d V ⋙ exchangeConstantPull (A := A) f :=
  Functor.mapDerivedCategorySquareIso (exchangeModuleResPull d f)

/-- The canonical right-derived unit on strict tower complexes, using complex localization.
Source: strict normalization, proof step 5; Stacks 07A5
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeTowerDerivedUnit {U V : Scheme.{t}} (f : U ⟶ V)
    (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S)
    (C : CochainComplex (exchangeTowers U S) ℤ) :
    DerivedCategory.Q.obj
        (((exchangeTowerModulePush f R S c).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (exchangeTowerPush f R S c).obj (DerivedCategory.Q.obj C) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (exchangeTowerModulePush f R S c).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj C) ≫
    (exchangeTowerPush f R S c).map ((DerivedCategory.quotientCompQhIso _).hom.app C)

/-- Ordinary direct image commutes with restriction by identity on every section and index.
Source: strict normalization, proof step 5; Stacks 0D6E
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeModuleResPush {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerModulePush f ⋙ exchangeTowerModuleRes d V ≅
      exchangeTowerModuleRes d U ⋙ exchangeTowerModulePush f
        (exchangeConstantRing V A) (exchangeConstantRing U A) (exchangeConstantIso f A) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
    (proEtaleRingRestrictionDirectImage f
      (exchangeConstantRing V A) (d.completedRing V)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d V) (exchangeScalar d U)
      (exchangeConstantIso f A) (d.integralRingIso f) (exchangeScalar_comm d f))

/-- The complex-level unit of a total right derived functor.
Source: Stacks Tag 07A5
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeDerivedUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (R : C ⥤ D) [R.Additive] (K : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      R.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
    R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
    R.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app K)

/-- Unit normalization of exact descent of a right-adjoint comparison.
Source: Stacks Tags 07A5 and 099M
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def ExchangeDerivedPushNormalized
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    (R : B ⥤ A) (R' : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
    [R.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (τ : R ⋙ G ≅ H ⋙ R')
    (e : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ R'.rightDerivedFunctor) : Prop :=
  ∀ K : CochainComplex B ℤ,
    G.mapDerivedCategory.map (exchangeDerivedUnit R K) ≫
      e.hom.app (DerivedCategory.Q.obj K) ≫
      R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app K) =
    G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex τ (.up ℤ)).hom.app K) ≫
      exchangeDerivedUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj K)

/-- Normalization of the direct-image comparison by the universal right-derived units.
It records the identity on the full diagram before deriving, rather than evaluations alone.
Source: strict normalization, proof step 5; Stacks 0D6E
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def ExchangeResPushNormalized {U V : Scheme.{t}} (f : U ⟶ V)
    (e : d.towerPush f ⋙ exchangeTowerRes d V ≅
      exchangeTowerRes d U ⋙ exchangeConstantPush (A := A) f) : Prop :=
  ExchangeDerivedPushNormalized (d.towerModulePush f)
    (exchangeTowerModulePush f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (exchangeTowerModuleRes d V) (exchangeTowerModuleRes d U) (exchangeModuleResPush d f) e

section ExactDerivedMate

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]

@[irreducible] private def exactDerivedMate
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H) :
    R.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ R'.rightDerivedFunctor :=
  (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso s).hom))

private theorem exactDerivedMate_factors
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (τ : R ⋙ G ≅ H ⋙ R')
    (hs : (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) = τ.hom)
    (K : CochainComplex B ℤ) :
    G.mapDerivedCategory.map (exchangeDerivedUnit R K) ≫
      (exactDerivedMate adj adj' s).app (DerivedCategory.Q.obj K) ≫
      R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app K) =
    G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex τ (.up ℤ)).hom.app K) ≫
      exchangeDerivedUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj K) := by
  rw [exactDerivedMate]
  have h := derived_mate_factors adj adj' s K
  rw [hs] at h
  exact h

private theorem exactDerivedMate_eq
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (τ : R ⋙ G ≅ H ⋙ R')
    (hs : (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) = τ.hom)
    (e : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ R'.rightDerivedFunctor)
    (he : ExchangeDerivedPushNormalized R R' G H τ e) :
    e.hom = exactDerivedMate adj adj' s := by
  apply derived_comp_ext R G (H.mapDerivedCategory ⋙ R'.rightDerivedFunctor)
  intro K
  apply (cancel_mono (R'.rightDerivedFunctor.map
    (H.mapDerivedCategoryFactors.hom.app K))).mp
  simpa only [exchangeDerivedUnit, chainDerivedUnit, Category.assoc] using
    (he K).trans (exactDerivedMate_factors adj adj' s τ hs K).symm

end ExactDerivedMate

set_option backward.isDefEq.respectTransparency.types false in
-- A normalized ordinary mate descends uniquely when the exact vertical functor
-- preserves K-injectives. Keeping this argument abstract avoids expanding coefficient models.
private theorem exactDerivedMate_existsUnique
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H) [H.PreservesKInjectiveComplexes]
    (τ : R ⋙ G ≅ H ⋙ R')
    (hs : (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) = τ.hom) :
    ∃! e : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ≅
        H.mapDerivedCategory ⋙ R'.rightDerivedFunctor,
      ExchangeDerivedPushNormalized R R' G H τ e := by
  let m := exactDerivedMate adj adj' s
  have hn := exactDerivedMate_factors adj adj' s τ hs
  have hI (I : CochainComplex B ℤ) [I.IsKInjective] :
      IsIso (m.app (DerivedCategory.Q.obj I)) := by
    have : IsIso (exchangeDerivedUnit R I) := chainDerivedUnit_isIso R I
    have : IsIso (exchangeDerivedUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj I)) :=
      chainDerivedUnit_isIso R' _
    have : IsIso (G.mapDerivedCategory.map (exchangeDerivedUnit R I) ≫
        m.app (DerivedCategory.Q.obj I) ≫
        R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I)) := by
      rw [hn I]
      infer_instance
    have := IsIso.of_isIso_comp_left (G.mapDerivedCategory.map (exchangeDerivedUnit R I))
      (m.app (DerivedCategory.Q.obj I) ≫
        R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I))
    exact IsIso.of_isIso_comp_right _
      (R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I))
  have (M : DerivedCategory B) : IsIso (m.app M) := by
    obtain ⟨I, hInj, ⟨eI⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
    have : I.IsKInjective := hInj
    have : IsIso (m.app (DerivedCategory.Q.obj I)) := hI I
    exact (NatTrans.isIso_app_iff_of_iso m eI).mpr inferInstance
  have : IsIso m := NatIso.isIso_of_isIso_app m
  refine ⟨asIso m, hn, ?_⟩
  intro e he
  apply Iso.ext
  apply derived_comp_ext R G (H.mapDerivedCategory ⋙ R'.rightDerivedFunctor)
  intro K
  apply (cancel_mono (R'.rightDerivedFunctor.map
    (H.mapDerivedCategoryFactors.hom.app K))).mp
  simpa only [exchangeDerivedUnit, chainDerivedUnit, Category.assoc, asIso_hom] using
    (he K).trans (hn K).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem exchangeModuleResPull_mate {U V : Scheme.{t}} (f : U ⟶ V) :
    (mateEquiv (d.towerModuleAdjunction f)
      (exchangeTowerModuleAdjunction f (exchangeConstantRing V A)
        (exchangeConstantRing U A) (exchangeConstantIso f A))
      (TwoSquare.mk _ _ _ _ (exchangeModuleResPull d f).inv)) =
        (exchangeModuleResPush d f).hom := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  have h := restrictionPullback_mate f
    (exchangeConstantRing V A) (d.completedRing V)
    (exchangeConstantRing U A) (d.completedRing U)
    (exchangeScalar d V) (exchangeScalar d U)
    (exchangeConstantIso f A) (d.integralRingIso f) (exchangeScalar_comm d f)
  exact congrArg (fun z ↦ z.app (M.obj n)) h

set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction/direct-image comparison is uniquely determined by the universal units.
Source: strict normalization, proof step 5; Stacks 0D6E and 099M
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization).
Proof: scalar extension from constant to completed coefficients is flat by
constant-completion-equivalence. Exact scalar extension and its adjunction lift
termwise to strict towers. Restriction, its right adjoint, preserves K-injectives.
On one K-injective tower representative the ordinary comparison
is identity on every section and transition, and both derived units are invertible.
This defines the comparison uniquely there. K-injective resolutions and the
universal property of the right-derived functor give its natural extension and
the displayed unit equation on every complex. -/
theorem exchangeResPush_existsUnique {U V : Scheme.{t}} (f : U ⟶ V) :
    ∃! e : d.towerPush f ⋙ exchangeTowerRes d V ≅
        exchangeTowerRes d U ⋙ exchangeConstantPush (A := A) f,
      ExchangeResPushNormalized d f e := by
  have : (exchangeTowerModuleRes d U).PreservesKInjectiveComplexes :=
    exchangeTowerModuleRes_kinjective d U
  exact exactDerivedMate_existsUnique
    (G := exchangeTowerModuleRes d V) (H := exchangeTowerModuleRes d U)
    (d.towerModuleAdjunction f)
    (exchangeTowerModuleAdjunction f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A))
    (exchangeModuleResPull d f).symm (exchangeModuleResPush d f)
    (exchangeModuleResPull_mate d f)

/-- The specified strict-tower direct-image comparison, with the unit normalization retained.
Source: strict normalization, proof step 5; Stacks 0D6E
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeResPush {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerPush f ⋙ exchangeTowerRes d V ≅
      exchangeTowerRes d U ⋙ exchangeConstantPush (A := A) f :=
  (exchangeResPush_existsUnique d f).choose

/-- The left strict corner comparison, natural in the complete input tower.
Source: strict normalization, final paragraph; Stacks 0D6D--0D6E
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeCornerB {X Y' Y : Scheme.{t}} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    (d.towerPush f ⋙ d.towerPull g) ⋙ exchangeTowerRes d Y' ≅
      exchangeTowerRes d X ⋙
        (exchangeConstantPush (A := A) f ⋙ exchangeConstantPull (A := A) g) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (exchangeResPull d g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (exchangeResPush d f) _ ≪≫ Functor.associator _ _ _

/-- The right strict corner comparison, natural in the complete input tower.
Source: strict normalization, final paragraph; Stacks 0D6D--0D6E
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeCornerD {X' X Y' : Scheme.{t}} (g' : X' ⟶ X) (f' : X' ⟶ Y') :
    (d.towerPull g' ⋙ d.towerPush f') ⋙ exchangeTowerRes d Y' ≅
      exchangeTowerRes d X ⋙
        (exchangeConstantPull (A := A) g' ⋙ exchangeConstantPush (A := A) f') :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (exchangeResPush d f') ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (exchangeResPull d g') _ ≪≫ Functor.associator _ _ _

/-- The explicit strict H: inverse pullback/reduction identification followed by h.
Its source is R(M), its target is B, and its projection factor is the adjunct
of the ambient counit tensored with the whole quotient diagram. The preceding
inverse chi identifies R(M) with L_g R_Y(Rf_*K), so h is H after chi.
Source: strict normalization, paragraph 3; Stacks 0B56
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeRealizationH (K : d.derived X) :
    (completedReductionTower Y' d).obj ((d.pull g).obj ((d.push f).obj K)) ≅
      (d.towerPull g).obj ((d.towerPush f).obj ((completedReductionTower X d).obj K)) :=
  ((d.reductionTowerPullbackIso g).symm.app ((d.push f).obj K)) ≪≫
    (d.towerPull g).mapIso (asIso (d.towerProjection f K))

/-- The explicit strict H prime, from R(N) to D: the diagram projection formula
for E followed by direct image of the inverse reduction/pullback identification.
Both H and H prime are isomorphisms before any evaluation is taken.
Source: strict normalization, paragraph 3; Stacks 0B56
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeRealizationHPrime (K : d.derived X) :
    (completedReductionTower Y' d).obj ((d.push f').obj ((d.pull g').obj K)) ≅
      (d.towerPush f').obj ((d.towerPull g').obj ((completedReductionTower X d).obj K)) :=
  asIso (d.towerProjection f' ((d.pull g').obj K)) ≪≫
    (d.towerPush f').mapIso ((d.reductionTowerPullbackIso g').symm.app K)

/-- The specified strict lift commutes with every morphism of the input object.
Source: strict normalization, final paragraph; Stacks 0E48
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization).
Proof: reduction and the ambient exchange are natural. The projection arrow is
its adjunction mate and hence natural in K. Pullback and direct image preserve
these naturality equations. Compose them for h inverse, v and h prime to obtain
the displayed equation for the specified strict composite towerV'. -/
theorem exchangeStrict_naturality (sq : ChosenCartesianSquare g' f' f g)
    {K L : d.derived X} (a : K ⟶ L) :
    (d.towerPull g).map ((d.towerPush f).map ((completedReductionTower X d).map a)) ≫
        d.towerV' sq L =
      d.towerV' sq K ≫
        (d.towerPush f').map ((d.towerPull g').map ((completedReductionTower X d).map a)) := by
  let pi (U V : Scheme.{t}) (u : U ⟶ V) :
      d.push u ⋙ completedReductionTower V d ≅
        completedReductionTower U d ⋙ d.towerPush u :=
    NatIso.ofComponents (fun K ↦ asIso (d.towerProjection u K))
      (fun {K L} a ↦ (d.towerProjection_properties u K).2.1 L a)
  let H := Functor.isoWhiskerRight (pi X Y f) (d.towerPull g)
  let v := Functor.whiskerLeft (d.push f) (d.reductionTowerPullbackIso g).hom ≫
    Functor.whiskerRight (d.integralExchange sq) (completedReductionTower Y' d)
  let H' := Functor.isoWhiskerLeft (d.pull g') (pi X' Y' f') ≪≫
    Functor.isoWhiskerRight (d.reductionTowerPullbackIso g').symm (d.towerPush f')
  exact (H.inv ≫ v ≫ H'.hom).naturality a

/-- The specified finite exchange is a natural transformation on strict derived towers.
Its naturality is inherited from the already specified projection-formula tower maps.
Source: strict normalization, final paragraph
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeStrictNatTrans (sq : ChosenCartesianSquare g' f' f g) :
    (completedReductionTower X d ⋙ d.towerPush f) ⋙ d.towerPull g ⟶
      (completedReductionTower X d ⋙ d.towerPull g') ⋙ d.towerPush f' where
  app K := d.towerV' sq K
  naturality _K _L a := exchangeStrict_naturality d sq a


-- Keep the standard tower localization visible when specializing the ringed square.
attribute [local instance 2000] exchangeTowers_hasDerived

end AlgebraicGeometry.Scheme
