/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcFiniteCompletedCoefficientMap
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.CategoryTheory.StageSystem.Basic
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData

/-!
# Scalar extension of completed integral coefficients and its raw rationalization

Source: blueprint, proper base change, order 1307
(blueprint: def-weil-pbc-finite-stage-pair-category).

The coefficient map is fixed by every finite quotient. Its derived tensor functor
is the recorded K-flat construction. Rationalization is uniquely fixed by its
composite with the integral localization, including its object function.

For objects `(E,K)` and `(F,L)`, an upstream `PairCategory.Rep` contains a finite
coefficient field `M`, inclusions `E ≤ M` and `F ≤ M`, and a morphism between
the two specified scalar extensions in `pbcStageCategory M`. Its transport is
`pbcScalarAssociator.inv ≫ pbcScalarExtension.map u ≫ pbcScalarAssociator.hom`.
The upstream quotient identifies exactly those representatives whose transports
agree at a further finite coefficient field; none of these data is a parameter
of `PbcFiniteStagePairCategory`.

## Main definitions

* `pbcStageCategory`: the recorded raw rational finite coefficient stage.
* `pbcScalarSystem`: its concrete normalized tensor extension system.
* `PbcFiniteStagePairCategory`: the common-stage quotient with its Hom group laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u c
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace CategoryTheory.StageSystem

universe w v z
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type z} [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)]
  (S : StageSystem C)

/-- Addition on classes is fixed by addition of representatives at any common stage.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category). -/
def PairPreadditiveNormalized (P : Preadditive S.PairCategory) : Prop := by
  letI := P
  exact ∀ (X Y : S.PairCategory) (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n)
    (f g : X.toStage hX ⟶ Y.toStage hY),
    PairCategory.mkHom n hX hY (f + g) =
      PairCategory.mkHom n hX hY f + PairCategory.mkHom n hX hY g ∧
    PairCategory.mkHom n hX hY (0 : X.toStage hX ⟶ Y.toStage hY) = 0

section AdditiveConstruction

variable [∀ i j (h : i ≤ j), (S.T h).Additive]

omit [IsDirectedOrder I] in
private lemma pair_tr_add {i j n p : I} {hi : i ≤ n} {hj : j ≤ n}
    (h : n ≤ p) {x : C i} {y : C j}
    (f g : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    S.tr h (f + g) = S.tr h f + S.tr h g := by
  simp [tr, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

omit [IsDirectedOrder I] in
private lemma pair_tr_zero {i j n p : I} {hi : i ≤ n} {hj : j ≤ n}
    (h : n ≤ p) {x : C i} {y : C j} :
    S.tr h (0 : (S.T hi).obj x ⟶ (S.T hj).obj y) = 0 := by
  simp [tr]

omit [IsDirectedOrder I] in
private lemma pair_tr_neg {i j n p : I} {hi : i ≤ n} {hj : j ≤ n}
    (h : n ≤ p) {x : C i} {y : C j}
    (f : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    S.tr h (-f) = -S.tr h f := by
  simp [tr]

open PairCategory in
private def pairAddRep {X Y : S.PairCategory} (r s : Rep X Y) : Rep X Y :=
  ⟨commonStage r.k s.k, r.hX.trans (le_commonStage_left _ _),
    r.hY.trans (le_commonStage_left _ _),
    S.tr (le_commonStage_left _ _) r.u + S.tr (le_commonStage_right _ _) s.u⟩

open PairCategory in
private lemma pairAddRep_rel {X Y : S.PairCategory} {r r' s s' : Rep X Y}
    (hr : Rep.Rel r r') (hs : Rep.Rel s s') :
    Rep.Rel (pairAddRep S r s) (pairAddRep S r' s') := by
  obtain ⟨p, h₁, h₂, e⟩ := hr
  obtain ⟨q, h₃, h₄, e'⟩ := hs
  obtain ⟨a, ha₁, ha₂⟩ := exists_ge_ge p q
  obtain ⟨b, hb₁, hb₂⟩ := exists_ge_ge (commonStage r.k s.k) (commonStage r'.k s'.k)
  obtain ⟨m, hm₁, hm₂⟩ := exists_ge_ge a b
  refine ⟨m, hb₁.trans hm₂, hb₂.trans hm₂, ?_⟩
  change S.tr _ (S.tr _ r.u + S.tr _ s.u) = S.tr _ (S.tr _ r'.u + S.tr _ s'.u)
  rw [pair_tr_add, pair_tr_add, tr_tr, tr_tr, tr_tr, tr_tr]
  exact congrArg₂ (· + ·)
    (Rep.rel_of_eq h₁ h₂ e (ha₁.trans hm₁))
    (Rep.rel_of_eq h₃ h₄ e' (ha₂.trans hm₁))

private def pairHomAdd {X Y : S.PairCategory} (f g : X ⟶ Y) : X ⟶ Y :=
  Quotient.map₂ (pairAddRep S) (fun _ _ hr _ _ hs ↦ pairAddRep_rel S hr hs) f g

open PairCategory in
private lemma pairHomAdd_mk {X Y : S.PairCategory} {n : I}
    {hX : X.stage ≤ n} {hY : Y.stage ≤ n} (f g : X.toStage hX ⟶ Y.toStage hY) :
    pairHomAdd S (mkHom n hX hY f) (mkHom n hX hY g) = mkHom n hX hY (f + g) := by
  change mkHom _ _ _ _ = _
  rw [mkHom_eq_mkHom_iff']
  refine ⟨commonStage n n, le_rfl, le_commonStage_left _ _, ?_⟩
  simp only [pair_tr_add, tr_tr]

private def pairHomNeg {X Y : S.PairCategory} (f : X ⟶ Y) : X ⟶ Y :=
  Quotient.map (fun r ↦ ⟨r.k, r.hX, r.hY, -r.u⟩)
    (by
      rintro r s ⟨p, hr, hs, e⟩
      exact ⟨p, hr, hs, by simpa only [pair_tr_neg] using congrArg Neg.neg e⟩) f

open PairCategory in
private lemma pairHomNeg_mk {X Y : S.PairCategory} {n : I}
    {hX : X.stage ≤ n} {hY : Y.stage ≤ n} (f : X.toStage hX ⟶ Y.toStage hY) :
    pairHomNeg S (mkHom n hX hY f) = mkHom n hX hY (-f) := rfl

open PairCategory in
private def pairHomZero (X Y : S.PairCategory) : X ⟶ Y :=
  mkHom (commonStage X.stage Y.stage) (le_commonStage_left _ _)
    (le_commonStage_right _ _) 0

open PairCategory in
private lemma pairHomZero_mk {X Y : S.PairCategory} (n : I)
    (hX : X.stage ≤ n) (hY : Y.stage ≤ n) :
    pairHomZero S X Y = mkHom n hX hY 0 := by
  rw [pairHomZero, mkHom_eq_mkHom_iff']
  obtain ⟨p, hp, hn⟩ := exists_ge_ge (commonStage X.stage Y.stage) n
  exact ⟨p, hp, hn, by simp only [pair_tr_zero]⟩

open PairCategory in
private abbrev pairHomGroup (X Y : S.PairCategory) : AddCommGroup (X ⟶ Y) := by
  letI : Add (X ⟶ Y) := ⟨pairHomAdd S⟩
  letI : Zero (X ⟶ Y) := ⟨pairHomZero S X Y⟩
  letI : Neg (X ⟶ Y) := ⟨pairHomNeg S⟩
  exact {
    add := pairHomAdd S
    zero := pairHomZero S X Y
    neg := pairHomNeg S
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc f g h := by
      change pairHomAdd S (pairHomAdd S f g) h = pairHomAdd S f (pairHomAdd S g h)
      induction f using hom_induction with
      | h n hX hY f =>
        induction g using hom_induction with
        | h n' hX' hY' g =>
          induction h using hom_induction with
          | h n'' hX'' hY'' h =>
            obtain ⟨a, ha, ha'⟩ := exists_ge_ge n n'
            obtain ⟨p, hp, hp'⟩ := exists_ge_ge a n''
            rw [← mkHom_tr (ha.trans hp) f, ← mkHom_tr (ha'.trans hp) g,
              ← mkHom_tr hp' h]
            simp only [pairHomAdd_mk, add_assoc]
    zero_add f := by
      change pairHomAdd S (pairHomZero S X Y) f = f
      induction f using hom_induction with
      | h n hX hY f => rw [pairHomZero_mk S n hX hY, pairHomAdd_mk, zero_add]
    add_zero f := by
      change pairHomAdd S f (pairHomZero S X Y) = f
      induction f using hom_induction with
      | h n hX hY f => rw [pairHomZero_mk S n hX hY, pairHomAdd_mk, add_zero]
    neg_add_cancel f := by
      change pairHomAdd S (pairHomNeg S f) f = pairHomZero S X Y
      induction f using hom_induction with
      | h n hX hY f =>
        rw [pairHomNeg_mk, pairHomAdd_mk, neg_add_cancel, pairHomZero_mk S n hX hY]
    add_comm f g := by
      change pairHomAdd S f g = pairHomAdd S g f
      obtain ⟨n, _, hX, hY, _, _, f, g, rfl, rfl⟩ :=
        exists_common_stage f g X.stage
      rw [pairHomAdd_mk, pairHomAdd_mk, add_comm] }

open PairCategory in
private abbrev pairPreadditiveStructure : Preadditive S.PairCategory where
  homGroup := pairHomGroup S
  add_comp X Y Z f g h := by
    induction f using hom_induction with
    | h n hX hY f =>
      induction g using hom_induction with
      | h n' hX' hY' g =>
        induction h using hom_induction with
        | h n'' hY'' hZ h =>
          obtain ⟨a, ha, ha'⟩ := exists_ge_ge n n'
          obtain ⟨p, hp, hp'⟩ := exists_ge_ge a n''
          rw [← mkHom_tr (ha.trans hp) f, ← mkHom_tr (ha'.trans hp) g,
            ← mkHom_tr hp' h]
          change pairHomAdd S _ _ ≫ _ = pairHomAdd S (_ ≫ _) (_ ≫ _)
          rw [pairHomAdd_mk, mkHom_comp_mkHom, mkHom_comp_mkHom,
            mkHom_comp_mkHom, pairHomAdd_mk, Preadditive.add_comp]
  comp_add X Y Z f g h := by
    induction f using hom_induction with
    | h n hX hY f =>
      induction g using hom_induction with
      | h n' hY' hZ g =>
        induction h using hom_induction with
        | h n'' hY'' hZ' h =>
          obtain ⟨a, ha, ha'⟩ := exists_ge_ge n n'
          obtain ⟨p, hp, hp'⟩ := exists_ge_ge a n''
          rw [← mkHom_tr (ha.trans hp) f, ← mkHom_tr (ha'.trans hp) g,
            ← mkHom_tr hp' h]
          change _ ≫ pairHomAdd S _ _ = pairHomAdd S (_ ≫ _) (_ ≫ _)
          rw [pairHomAdd_mk, mkHom_comp_mkHom, mkHom_comp_mkHom,
            mkHom_comp_mkHom, pairHomAdd_mk, Preadditive.comp_add]

end AdditiveConstruction

/-- The common-stage formulas determine a unique preadditive structure.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: transport is conjugation of an additive functor by associators, so it is
additive. For two representatives pass to their finite common upper stage and
add there. A second choice agrees after transport to a common further stage.
Negation and zero descend in the same way. All abelian-group identities and
bilinearity of composition hold after passing to one common stage. Every
morphism has a representative, so these equations also prove uniqueness. -/
theorem pairPreadditive_exists [∀ i j (h : i ≤ j), (S.T h).Additive] :
    ∃! P : Preadditive S.PairCategory, S.PairPreadditiveNormalized P := by
  refine ⟨pairPreadditiveStructure S, ?_, ?_⟩
  · intro X Y n hX hY f g
    exact ⟨(pairHomAdd_mk S f g).symm, (pairHomZero_mk S n hX hY).symm⟩
  · intro P hP
    apply Preadditive.ext
    funext X Y
    apply AddCommGroup.ext
    funext f g
    obtain ⟨n, _, hX, hY, _, _, f, g, rfl, rfl⟩ :=
      PairCategory.exists_common_stage f g X.stage
    exact ((hP X Y n hX hY f g).1).symm.trans (pairHomAdd_mk S f g).symm

/-- The preadditive structure determined by the common-stage group laws.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category). -/
instance pairPreadditive [∀ i j (h : i ≤ j), (S.T h).Additive] :
    Preadditive S.PairCategory := (S.pairPreadditive_exists).exists.choose

end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
variable {E F G : Padic.FiniteCoefficientFields l Ω}

variable (T : Scheme.{u})

/-- The existing bounded constructible complete integral stage, with its coefficient fixed.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcIntegralStage (E : Padic.FiniteCoefficientFields l Ω) :=
  PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)

/-- The ambient derived coefficient stage used by the integral full inclusion.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcAmbientStage (E : Padic.FiniteCoefficientFields l Ω) :=
  PbcCompletedDerived T (pbcStageDatum.{u} l Ω E)

/-- The existing full inclusion of the integral stage into its ambient derived category.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcStageInclusion (E : Padic.FiniteCoefficientFields l Ω) :
    pbcIntegralStage l Ω T E ⥤ pbcAmbientStage l Ω T E :=
  ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E))

/-- The recorded raw rationalization at the canonical small model of E.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcStageCategory (E : Padic.FiniteCoefficientFields l Ω) :=
  PbcRationalCategory T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)

/-- The recorded integral localization functor at this coefficient stage.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcStageLocalization (E : Padic.FiniteCoefficientFields l Ω) :=
  pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcStageCoefficientMap_eq (h : E ≤ F) :
    pbcCompletedScalarMap l Ω T h =
      pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) T := by
  have hc (E : Padic.FiniteCoefficientFields l Ω) (n : ℕ) :
      (pbcLevelConstantComparison T (pbcStageDatum.{u} l Ω E) n).hom =
        AdicCoefficients.constantComparison T
          ((PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) ⧸
            (pbcStageDatum.{u} l Ω E).ideal ^ (n + 1)) := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ ((pbcAdicRings T (pbcStageDatum.{u} l Ω E)).obj
      (op n)).property
    change toSheafify _ _ ≫ (pbcLevelConstantComparison T _ n).hom.hom =
      toSheafify _ _ ≫ sheafifyMap _ _
    rw [← toSheafify_naturality]
    ext U b
    exact (pbcLevelConstantComparison_exists T (pbcStageDatum.{u} l Ω E) n).exists.choose_spec U b
  have hf (n : ℕ) : pbcFiniteScalarMap l Ω T h n =
      AdicCoefficients.coefficientMap T
        (pbcScalarQuotientMap l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
          (pbcFiniteFieldInclusion l Ω h) n) := by
    dsimp only [pbcFiniteScalarMap]
    rw [← cancel_epi (pbcLevelConstantComparison T (pbcStageDatum.{u} l Ω E) n).hom,
      Iso.hom_inv_id_assoc]
    rw [hc E n, hc F n]
    change (presheafToSheaf _ CommRingCat).map _ ≫
        (presheafToSheaf _ CommRingCat).map _ =
      (presheafToSheaf _ CommRingCat).map _ ≫ (presheafToSheaf _ CommRingCat).map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
  apply (pbcCompletedScalarMap_exists l Ω T h).unique
  · exact (pbcCompletedScalarMap_exists l Ω T h).exists.choose_spec
  · intro n
    rw [hf n]
    exact (pbcScalarCoefficientMap_exists l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T).exists.choose_spec n

/-- Finite coefficient extension preserves the three defining integral conditions.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the target integer ring is finite free over the source integer ring.
Compute derived extension on K-flat representatives. Finite freeness commutes
with the reduction tower and its derived limit and preserves completion.
Tensor the common bounded local models and the compatible etale origins.
Their normalization equations follow from ordinary tensor balancing at every
finite quotient; neither the bounds nor the finite stratification changes. -/
theorem pbcAmbientScalarExtension_preserves (h : E ≤ F)
    [IsNoetherian T] (_hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : pbcIntegralStage l Ω T E) :
    PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F)
      ((pbcAmbientScalarExtension l Ω T h).obj K.obj) := by
  change PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F)
    ((pbcDerivedExtend (pbcCompletedScalarMap l Ω T h)).obj K.obj)
  rw [pbcStageCoefficientMap_eq l Ω T h]
  exact pbcEmbeddingAmbientTensor_preserves l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T _hdim _hl K

variable [IsNoetherian T] (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
  (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- Restriction of the specified ambient tensor extension to the integral subcategories.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcIntegralScalarExtension (h : E ≤ F) :
    pbcIntegralStage l Ω T E ⥤
      pbcIntegralStage l Ω T F :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F))
    ((pbcStageInclusion l Ω T E) ⋙
      pbcAmbientScalarExtension l Ω T h)
    (pbcAmbientScalarExtension_preserves l Ω T h hdim hl)

private abbrev pbcStageDenominators (E : Padic.FiniteCoefficientFields l Ω) :
    MorphismProperty (pbcIntegralStage l Ω T E) :=
  letI := pbcIntegralTriangulated l (pbcFiniteField.{u} l Ω E) T hdim hl
  Rationalization.W (Submonoid.powers (pbcStageUniformizer.{u} l Ω E))
    (pbcIntegralStage l Ω T E)

omit [IsAlgClosure (Padic l) Ω] in
private theorem pbcStageLocalization_isLocalization (E : Padic.FiniteCoefficientFields l Ω) :
    (pbcStageLocalization l Ω T E).IsLocalization
      (pbcStageDenominators l Ω T hdim hl E) := by
  let := pbcIntegralTriangulated l (pbcFiniteField.{u} l Ω E) T hdim hl
  exact ScalarLocalization.pbcScalarLocalization_isLocalization
    (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) (pbcIntegralStage l Ω T E)
    (pbcStageUniformizer.{u} l Ω E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcIntegralScalarExtension_eq (h : E ≤ F) :
    pbcIntegralScalarExtension l Ω T hdim hl h =
      pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) T hdim hl := by
  unfold pbcIntegralScalarExtension pbcEmbeddingIntegralTensor
  unfold pbcAmbientScalarExtension pbcEmbeddingAmbientTensor
  simp only [pbcStageCoefficientMap_eq l Ω T h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsAlgClosure (Padic l) Ω] in
include hdim hl in
private theorem pbcStageFunctor_ext
    {D : Type*} [Category* D] (B B' : pbcStageCategory l Ω T E ⥤ D)
    (h : pbcStageLocalization l Ω T E ⋙ B = pbcStageLocalization l Ω T E ⋙ B') : B = B' := by
  let Q := pbcStageLocalization l Ω T E
  let W := pbcStageDenominators l Ω T hdim hl E
  have : Q.IsLocalization W := pbcStageLocalization_isLocalization l Ω T hdim hl E
  let : Localization.Lifting Q W (Q ⋙ B) B := ⟨Iso.refl _⟩
  let : Localization.Lifting Q W (Q ⋙ B) B' := ⟨eqToIso h.symm⟩
  let e := Localization.liftNatIso Q W (Q ⋙ B) (Q ⋙ B) B B' (Iso.refl _)
  refine CategoryTheory.Functor.ext_of_iso e
    (fun K ↦ congrArg (fun J ↦ J.obj K.obj) h) ?_
  intro K
  obtain ⟨K⟩ := K
  change (Localization.liftNatTrans Q W (Q ⋙ B) (Q ⋙ B) B B' (𝟙 _)).app (Q.obj K) = _
  rw [Localization.liftNatTrans_app]
  change 𝟙 _ ≫ 𝟙 _ ≫ (eqToIso h.symm).inv.app K = _
  simp only [Category.id_comp, eqToIso.inv, eqToHom_app]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] ULift.module in
/-- Integral tensor extension has a unique factorization through raw localization.
The equality fixes objects as well as integral morphisms; inverses of uniformizer
multiples then fix every fraction. No arbitrary functor is chosen.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the image of the source uniformizer is a unit times a positive power of
the target uniformizer, so it becomes invertible in the target localization.
Send a fraction f/pi^n to the integral tensor image of f divided by the image of
pi^n. The tensor relations, bilinearity and balancing prove well-definedness
and functoriality. Every localized morphism is such a fraction, proving uniqueness. -/
theorem pbcRationalScalarExtension_exists (h : E ≤ F) :
    ∃! B : pbcStageCategory l Ω T E ⥤
        pbcStageCategory l Ω T F,
      pbcStageLocalization l Ω T E ⋙ B =
        pbcIntegralScalarExtension l Ω T hdim hl h ⋙
          pbcStageLocalization l Ω T F := by
  let B := pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T hdim hl
  have hb : pbcStageLocalization l Ω T E ⋙ B =
      pbcIntegralScalarExtension l Ω T hdim hl h ⋙ pbcStageLocalization l Ω T F := by
    rw [pbcIntegralScalarExtension_eq l Ω T hdim hl h]
    refine CategoryTheory.Functor.ext
      (F := pbcStageLocalization l Ω T E ⋙ B)
      (G := pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T hdim hl ⋙
          pbcStageLocalization l Ω T F) (fun _ ↦ rfl) ?_
    intro K L f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change pbcRationalScalarHom l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
      (pbcFiniteFieldInclusion l Ω h) T hdim hl K L (1 ⊗ₜ[_] f) = _
    rw [pbcRationalScalarHom_tmul]
    simp only [map_one]
    rfl
  refine ⟨B, hb, ?_⟩
  intro B' hB'
  exact pbcStageFunctor_ext l Ω T hdim hl B' B (hB'.trans hb.symm)

/-- Raw rationalized tensor extension. Equal coefficient fields use identity literally.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcScalarExtension (h : E ≤ F) :
    pbcStageCategory l Ω T E ⥤
      pbcStageCategory l Ω T F :=
  by
    classical
    exact if e : E = F then e ▸ 𝟭 _ else
      (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose

set_option linter.unusedSectionVars false in
/-- Coefficient maps compose exactly, including repeated fields.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: both composites have the same quotient projections, because the field
inclusions compose. Use uniqueness of the completed limit map. -/
theorem pbcCompletedScalarMap_comp (h : E ≤ F) (k : F ≤ G) :
    pbcCompletedScalarMap l Ω T h ≫ pbcCompletedScalarMap l Ω T k =
      pbcCompletedScalarMap l Ω T (h.trans k) := by
  have hi : (pbcIntegerInclusion l Ω k).comp (pbcIntegerInclusion l Ω h) =
      pbcIntegerInclusion l Ω (h.trans k) := by
    apply RingHom.ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    have hinc : pbcFiniteFieldInclusion l Ω k
        (pbcFiniteFieldInclusion l Ω h x.down.val) =
        pbcFiniteFieldInclusion l Ω (h.trans k) x.down.val := by
      change (Shrink.algEquiv (Padic l) G.val).symm
          (IntermediateField.inclusion k
            ((Shrink.algEquiv (Padic l) F.val)
              ((Shrink.algEquiv (Padic l) F.val).symm
                (IntermediateField.inclusion h
                  ((Shrink.algEquiv (Padic l) E.val) x.down.val))))) = _
      rw [AlgEquiv.apply_symm_apply]
      rfl
    simpa [pbcIntegerInclusion, WeilConjectures.integralScalarIntegerInclusion] using hinc
  have hq (n : ℕ) :
      (pbcQuotientInclusion l Ω k n).comp (pbcQuotientInclusion l Ω h n) =
        pbcQuotientInclusion l Ω (h.trans k) n := by
    apply RingHom.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    change Ideal.Quotient.mk _ (pbcIntegerInclusion l Ω k (pbcIntegerInclusion l Ω h x)) =
      Ideal.Quotient.mk _ (pbcIntegerInclusion l Ω (h.trans k) x)
    exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun hi x)
  have hf (n : ℕ) : pbcFiniteScalarMap l Ω T h n ≫ pbcFiniteScalarMap l Ω T k n =
      pbcFiniteScalarMap l Ω T (h.trans k) n := by
    dsimp only [pbcFiniteScalarMap]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc]
    congr 2
    exact congrArg ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map)
      (congrArg CommRingCat.ofHom (hq n))
  apply (pbcCompletedScalarMap_exists l Ω T (h.trans k)).unique
  · intro n
    dsimp only [pbcCompletedScalarMap]
    rw [Category.assoc,
      (pbcCompletedScalarMap_exists l Ω T k).exists.choose_spec n,
      ← Category.assoc,
      (pbcCompletedScalarMap_exists l Ω T h).exists.choose_spec n,
      Category.assoc, hf n]
  · exact (pbcCompletedScalarMap_exists l Ω T (h.trans k)).exists.choose_spec

set_option backward.isDefEq.respectTransparency false in
omit [IsNoetherian T] in
private theorem pbcCompletedScalarMap_id (E : Padic.FiniteCoefficientFields l Ω) :
    pbcCompletedScalarMap l Ω T (le_refl E) = 𝟙 _ := by
  have hi : pbcIntegerInclusion.{u} l Ω (le_refl E) = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    simp [pbcIntegerInclusion, WeilConjectures.integralScalarIntegerInclusion,
      pbcFiniteFieldInclusion]
  have hq (n : ℕ) : pbcQuotientInclusion.{u} l Ω (le_refl E) n = RingHom.id _ := by
    apply RingHom.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    change Ideal.Quotient.mk _ (pbcIntegerInclusion l Ω (le_refl E) x) = _
    rw [hi]
    rfl
  have hf (n : ℕ) : pbcFiniteScalarMap l Ω T (le_refl E) n = 𝟙 _ := by
    dsimp only [pbcFiniteScalarMap]
    rw [hq]
    have hm : CommRingCat.ofHom
        (RingHom.id ((PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) ⧸
          (pbcStageDatum.{u} l Ω E).ideal ^ (n + 1))) = 𝟙 _ := rfl
    rw [hm, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  apply (pbcCompletedScalarMap_exists l Ω T (le_refl E)).unique
  · exact (pbcCompletedScalarMap_exists l Ω T (le_refl E)).exists.choose_spec
  · intro n
    rw [hf, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsNoetherian T] in
private theorem pbcTensorSection_smul
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules T R) (U : T.ProEtᵒᵖ) (r : S.obj.obj U) (x : M.val.obj U) :
    pbcTensorSection φ M U r x = r • pbcTensorSection φ M U 1 x := by
  change completedAdicChangeTensor T φ M U r x =
    r • completedAdicChangeTensor T φ M U 1 x
  simpa only [mul_one] using completedTensor_smul T φ M U r 1 x

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- The tensor unit comparison is fixed on sheafified pure tensors.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: inclusion E→E is identity, also on completions. The balanced map
r tensor x ↦ r*x and x ↦ 1 tensor x are inverse sectionwise, commute with
restriction, and descend through sheafification. Pure tensors generate locally,
so the indicated formula determines the natural isomorphism uniquely. -/
theorem pbcOrdinaryScalarUnit_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! e : pbcExtend (pbcCompletedScalarMap l Ω T (le_refl E)) ≅
        𝟭 (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))),
      ∀ (M : pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)))
        (U : T.ProEtᵒᵖ) (r : (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)).obj.obj U)
        (x : M.val.obj U),
        (e.hom.app M).val.app U
          (pbcTensorSection (pbcCompletedScalarMap l Ω T (le_refl E)) M U r x) = r • x := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let φ := pbcCompletedScalarMap l Ω T (le_refl E)
  let ρ := SheafOfModules.systemScalarRestrictionUnit φ (pbcCompletedScalarMap_id l Ω T E)
  let a := (pbcScalarAdjunction φ).ofNatIsoRight ρ
  let e := a.leftAdjointUniq Adjunction.id
  have he (M : pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)))
      (U : T.ProEtᵒᵖ) (r : (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)).obj.obj U)
      (x : M.val.obj U) :
      (e.hom.app M).val.app U (pbcTensorSection φ M U r x) = r • x := by
    have h := Adjunction.unit_leftAdjointUniq_hom_app a Adjunction.id M
    have hx := congrArg (fun f ↦ f.val.app U x) h
    change (e.hom.app M).val.app U ((pbcScalarAdjunction φ).unit.app M |>.val.app U x) = x
      at hx
    erw [(pbcScalarAdjunction_exists φ).exists.choose_spec M U x] at hx
    rw [pbcTensorSection_smul, _root_.map_smul, hx]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (pbcScalarAdjunction φ).homEquiv _ _ |>.injective
  ext U x
  change (e'.hom.app M).val.app U ((pbcScalarAdjunction φ).unit.app M |>.val.app U x) =
    (e.hom.app M).val.app U ((pbcScalarAdjunction φ).unit.app M |>.val.app U x)
  erw [(pbcScalarAdjunction_exists φ).exists.choose_spec M U x, he', he]

/-- The section-normalized ordinary tensor unit.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcOrdinaryScalarUnit (E : Padic.FiniteCoefficientFields l Ω) :
    pbcExtend (pbcCompletedScalarMap l Ω T (le_refl E)) ≅
        𝟭 (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) :=
  (pbcOrdinaryScalarUnit_exists l Ω T E).exists.choose

private def pbcHomotopyScalarUnit (E : Padic.FiniteCoefficientFields l Ω) :
    (pbcExtend (pbcCompletedScalarMap l Ω T (le_refl E))).mapHomotopyCategory (.up ℤ) ≅
      𝟭 (HomotopyCategory
        (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) (.up ℤ)) :=
  { hom := NatTrans.mapHomotopyCategory (pbcOrdinaryScalarUnit l Ω T E).hom (.up ℤ)
    inv := NatTrans.mapHomotopyCategory (pbcOrdinaryScalarUnit l Ω T E).inv (.up ℤ)
    hom_inv_id := by
      rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
    inv_hom_id := by
      rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
        NatTrans.mapHomotopyCategory_id] } ≪≫
    Functor.mapHomotopyCategoryIdIso _ (.up ℤ)

private def pbcHomotopyScalarUnitQ (E : Padic.FiniteCoefficientFields l Ω) :
    (pbcExtend (pbcCompletedScalarMap l Ω T (le_refl E))).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh ≅ DerivedCategory.Qh :=
  Functor.isoWhiskerRight (pbcHomotopyScalarUnit l Ω T E) DerivedCategory.Qh ≪≫
    Functor.leftUnitor DerivedCategory.Qh

private def pbcDerivedScalarUnit (E : Padic.FiniteCoefficientFields l Ω) :
    pbcAmbientScalarExtension l Ω T (le_refl E) ≅ 𝟭 (pbcAmbientStage l Ω T E) := by
  let φ := pbcCompletedScalarMap l Ω T (le_refl E)
  let a : DerivedCategory.Qh ⋙ 𝟭 (pbcAmbientStage l Ω T E) ≅ DerivedCategory.Qh :=
    Functor.rightUnitor DerivedCategory.Qh
  let := pbcDerivedExtension_universal φ
  let := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso
      (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) (.up ℤ))
    (𝟭 (pbcAmbientStage l Ω T E)) a
  exact Functor.leftDerivedNatIso _ _ (pbcExtensionCounit φ) a.hom
    (HomotopyCategory.quasiIso
      (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) (.up ℤ))
    (pbcHomotopyScalarUnitQ l Ω T E)

private theorem pbcDerivedScalarUnit_homotopy (E : Padic.FiniteCoefficientFields l Ω)
    (H : HomotopyCategory
      (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) (.up ℤ)) :
    (pbcDerivedScalarUnit l Ω T E).hom.app (DerivedCategory.Qh.obj H) =
      (pbcExtensionCounit (pbcCompletedScalarMap l Ω T (le_refl E))).app H ≫
        DerivedCategory.Qh.map ((pbcHomotopyScalarUnit l Ω T E).hom.app H) := by
  let φ := pbcCompletedScalarMap l Ω T (le_refl E)
  let a : DerivedCategory.Qh ⋙ 𝟭 (pbcAmbientStage l Ω T E) ≅ DerivedCategory.Qh :=
    Functor.rightUnitor DerivedCategory.Qh
  let := pbcDerivedExtension_universal φ
  let := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso
      (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) (.up ℤ))
    (𝟭 (pbcAmbientStage l Ω T E)) a
  have h := Functor.leftDerivedNatTrans_app (pbcDerivedExtend φ) (𝟭 _)
    (pbcExtensionCounit φ) a.hom
    (HomotopyCategory.quasiIso
      (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) (.up ℤ))
    (pbcHomotopyScalarUnitQ l Ω T E).hom H
  change (pbcDerivedScalarUnit l Ω T E).hom.app (DerivedCategory.Qh.obj H) ≫ 𝟙 _ =
    (pbcExtensionCounit φ).app H ≫
      (DerivedCategory.Qh.map ((pbcHomotopyScalarUnit l Ω T E).hom.app H) ≫ 𝟙 _) at h
  simpa only [Category.comp_id] using h

/-- The derived tensor unit is uniquely fixed by its universal counit on complexes.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: tensor extension along identity is exact. Its universal left-derived
counit is invertible; descend the section-normalized ordinary tensor unit.
Localization of complexes is essentially surjective and full on natural
transformations, so this normalization determines the comparison uniquely. -/
theorem pbcAmbientScalarUnit_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! e : pbcAmbientScalarExtension l Ω T (le_refl E) ≅
        𝟭 (pbcAmbientStage l Ω T E),
      ∀ P : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) =
          pbcComplexCounit (pbcCompletedScalarMap l Ω T (le_refl E)) P ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex
                (pbcOrdinaryScalarUnit l Ω T E).hom (.up ℤ)).app P) := by
  let φ := pbcCompletedScalarMap l Ω T (le_refl E)
  let M := pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
  have he (P : CochainComplex M ℤ) :
      (pbcDerivedScalarUnit l Ω T E).hom.app (DerivedCategory.Q.obj P) =
        pbcComplexCounit φ P ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pbcOrdinaryScalarUnit l Ω T E).hom
            (.up ℤ)).app P) := by
    have hn := (pbcDerivedScalarUnit l Ω T E).hom.naturality
      ((DerivedCategory.quotientCompQhIso M).inv.app P)
    dsimp only [Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn
    have hf : ((pbcExtend φ).mapHomotopyCategoryFactors (.up ℤ)).hom.app P = 𝟙 _ := rfl
    have hu : (pbcHomotopyScalarUnit l Ω T E).hom.app
        ((HomotopyCategory.quotient M (.up ℤ)).obj P) =
        (HomotopyCategory.quotient M (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (pbcOrdinaryScalarUnit l Ω T E).hom
            (.up ℤ)).app P) := by
      simp only [pbcHomotopyScalarUnit, Iso.trans_hom, NatTrans.comp_app,
        Functor.mapHomotopyCategoryIdIso_hom_app_eq_id]
      rfl
    calc
      _ = (pbcAmbientScalarExtension l Ω T (le_refl E)).map
            ((DerivedCategory.quotientCompQhIso M).inv.app P) ≫
          (pbcDerivedScalarUnit l Ω T E).hom.app
            ((HomotopyCategory.quotient M (.up ℤ) ⋙ DerivedCategory.Qh).obj P) ≫
          (DerivedCategory.quotientCompQhIso M).hom.app P := by
        dsimp only [Functor.comp_obj]
        rw [reassoc_of% hn]
        simp only [Iso.inv_hom_id_app, Category.comp_id]
      _ = _ := by
        dsimp only [Functor.comp_obj]
        erw [pbcDerivedScalarUnit_homotopy l Ω T E
          ((HomotopyCategory.quotient M (.up ℤ)).obj P), hu]
        dsimp only [pbcComplexCounit]
        erw [hf, DerivedCategory.Qh.map_id]
        simp only [Category.assoc]
        erw [DerivedCategory.quotientCompQhIso_hom_naturality]
  refine ⟨pbcDerivedScalarUnit l Ω T E, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso M (.up ℤ))
  intro P
  exact (he' P).trans (he P).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsNoetherian T] in
private theorem pbcAdjunction_complexUnit
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P : CochainComplex (pbcModules T R) ℤ) :
    (pbcDerivedScalarAdjunction φ).unit.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have hr (X : HomotopyCategory (pbcModules T R) (.up ℤ)) :
      ∃ (K : HomotopyCategory (pbcModules T R) (.up ℤ)) (s : K ⟶ X),
        IsIso ((pbcExtensionCounit φ).app K) ∧
          HomotopyCategory.quasiIso (pbcModules T R) (.up ℤ) s := by
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨K, s, hK, hs⟩ :=
      ScalarReductionDerivedProof.kFlatResolutions.{u + 1, u, u + 1}
        (J := ProEt.topology T) (O := R) G
    exact ⟨_, (HomotopyCategory.quotient _ _).map s, pbcExtensionCounit_isIso φ K hK,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  obtain ⟨d, hd⟩ := ScalarReductionDerivedProof.derivedAdjunction_of_resolutions
    (pbcExtend φ) (pbcRestrict φ) (pbcScalarAdjunction φ)
    (pbcDerivedExtend φ) (pbcExtensionCounit φ) (pbcDerivedExtension_universal φ) hr
  have hn (K : CochainComplex (pbcModules T R) ℤ) :
        d.unit.app (DerivedCategory.Q.obj K) ≫
          (pbcRestrict φ).mapDerivedCategory.map
            ((pbcDerivedExtend φ).map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
              (pbcExtensionCounit φ).app ((HomotopyCategory.quotient _ _).obj K) ≫
              DerivedCategory.Qh.map
                (((pbcExtend φ).mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ≫
              (DerivedCategory.quotientCompQhIso _).hom.app
                (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj K)) ≫
          (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
            (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj K) =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app K) := by
    have hp := hd ((HomotopyCategory.quotient _ _).obj K)
    change d.unit.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ _).obj K)) ≫
      (pbcRestrict φ).mapDerivedCategory.map
        ((pbcExtensionCounit φ).app ((HomotopyCategory.quotient _ _).obj K)) ≫
      (pbcRestrict φ).mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj K)) = _ at hp
    simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
      Adjunction.mapHomotopyCategory_unit_app_quotient] at hp
    dsimp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
      Functor.mapHomotopyCategoryFactors, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id] at hp ⊢
    erw [(pbcDerivedExtend φ).map_id, DerivedCategory.Qh.map_id,
      Category.comp_id, Category.id_comp]
    erw [(pbcRestrict φ).mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
      Category.id_comp] at hp
    repeat' erw [Category.comp_id] at hp
    exact hp
  have he : d = pbcDerivedScalarAdjunction φ :=
    (pbcDerivedScalarAdjunction_exists φ).unique (fun K _ ↦ hn K)
      (pbcDerivedScalarAdjunction_exists φ).exists.choose_spec
  rw [← he]
  exact hn P

/-- The canonical derived tensor unit, rather than an arbitrary unit isomorphism.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcAmbientScalarUnit (E : Padic.FiniteCoefficientFields l Ω) :
    pbcAmbientScalarExtension l Ω T (le_refl E) ≅
        𝟭 (pbcAmbientStage l Ω T E) :=
  (pbcAmbientScalarUnit_exists l Ω T E).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsNoetherian T] in
private theorem pbcAdjunction_complexTranspose
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P : CochainComplex (pbcModules T R) ℤ) (K : CochainComplex (pbcModules T S) ℤ)
    (f : ((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P ⟶ K) :
    (pbcDerivedScalarAdjunction φ).homEquiv _ _
        (pbcComplexCounit φ P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
          (((pbcScalarAdjunction φ).mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.inv.app K := by
  have hu : (pbcDerivedScalarAdjunction φ).unit.app (DerivedCategory.Q.obj P) ≫
      (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) =
    DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P) ≫
      (pbcRestrict φ).mapDerivedCategoryFactors.inv.app
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) := by
    apply (cancel_mono ((pbcRestrict φ).mapDerivedCategoryFactors.hom.app _)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact pbcAdjunction_complexUnit T φ P
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, ← Category.assoc, hu,
    Category.assoc]
  erw [← (pbcRestrict φ).mapDerivedCategoryFactors.inv.naturality f]
  simp only [Functor.comp_map]
  erw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Adjunction.homEquiv_unit]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcAmbientScalarUnit_mate (E : Padic.FiniteCoefficientFields l Ω) :
    pbcAmbientScalarUnit l Ω T E =
      Adjunction.leftAdjointIdIso
        (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T (le_refl E)))
        (Functor.exactDerivedRestrictionUnit _
          (SheafOfModules.systemScalarRestrictionUnit
            (pbcCompletedScalarMap l Ω T (le_refl E)) (pbcCompletedScalarMap_id l Ω T E))) := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let φ := pbcCompletedScalarMap l Ω T (le_refl E)
  let Rφ := pbcRestrict φ
  let ρ := SheafOfModules.systemScalarRestrictionUnit φ (pbcCompletedScalarMap_id l Ω T E)
  let δ := Functor.exactDerivedRestrictionUnit Rφ ρ
  let ν := pbcOrdinaryScalarUnit l Ω T E
  let ac := (pbcScalarAdjunction φ).mapHomologicalComplex (.up ℤ)
  let ρc := NatIso.mapHomologicalComplex ρ (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  let νc := NatIso.mapHomologicalComplex ν (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  have hn (P : CochainComplex (pbcModules T (pbcAdicCompletion T
      (pbcStageDatum.{u} l Ω E))) ℤ) :
      ac.homEquiv _ _ (νc.hom.app P) ≫ ρc.hom.app P = 𝟙 P := by
    apply HomologicalComplex.hom_ext
    intro i
    change (pbcScalarAdjunction φ).homEquiv _ _ (ν.hom.app (P.X i)) ≫
      ρ.hom.app (P.X i) = 𝟙 _
    ext U x
    change (ν.hom.app (P.X i)).val.app U
      ((pbcScalarAdjunction φ).unit.app (P.X i) |>.val.app U x) = x
    erw [(pbcScalarAdjunction_exists φ).exists.choose_spec,
      (pbcOrdinaryScalarUnit_exists l Ω T E).exists.choose_spec]
    exact one_smul _ _
  have he := normalizedAdjunction_uniqueness
    (QA := DerivedCategory.Q) (QB := DerivedCategory.Q)
    ac Adjunction.id (pbcDerivedScalarAdjunction φ) Adjunction.id
    (pbcComplexCounit φ) (fun _ ↦ 𝟙 _) Rφ.mapDerivedCategoryFactors.inv.app
    (fun _ ↦ 𝟙 _) (pbcAdjunction_complexTranspose T φ)
    (by intros; simp only [Category.id_comp, Category.comp_id]; rfl)
    ρc δ νc.hom.app hn
    (by intro K; simpa only [Category.comp_id] using
      Functor.exactDerivedRestrictionUnit_inv_factors Rφ ρ K)
  have hcanon :
      ((pbcDerivedScalarAdjunction φ).ofNatIsoRight δ).leftAdjointUniq Adjunction.id =
        Adjunction.leftAdjointIdIso (pbcDerivedScalarAdjunction φ) δ := by
    apply Iso.ext
    ext K
    simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointIdIso,
      conjugateEquiv_symm_apply_app]
  symm
  apply (pbcAmbientScalarUnit_exists l Ω T E).unique _
    (pbcAmbientScalarUnit_exists l Ω T E).exists.choose_spec
  intro P
  have h := he P
  rw [hcanon] at h
  have hv : νc.hom.app P =
      (NatTrans.mapHomologicalComplex ν.hom (.up ℤ)).app P := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [νc, Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
      NatIso.mapHomologicalComplex_hom_app_f,
      Functor.mapHomologicalComplexIdIso_hom_app_f]
    exact Category.comp_id _
  rw [hv, Category.comp_id] at h
  exact h

/-- The integral tensor unit is the restriction of the canonical ambient one.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the integral subcategories are full. Lift each component of the ambient
unit and its inverse. Faithfulness gives naturality, inverse equations and
uniqueness. -/
theorem pbcIntegralScalarUnit_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! e : pbcIntegralScalarExtension l Ω T hdim hl (le_refl E) ≅
        𝟭 (pbcIntegralStage l Ω T E),
      Functor.whiskerRight e.hom
          (pbcStageInclusion l Ω T E) =
        Functor.whiskerLeft
          (pbcStageInclusion l Ω T E)
          (pbcAmbientScalarUnit l Ω T E).hom := by
  let e : pbcIntegralScalarExtension l Ω T hdim hl (le_refl E) ≅
      𝟭 (pbcIntegralStage l Ω T E) :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _ ((pbcAmbientScalarUnit l Ω T E).app K.obj))
      (fun f ↦ by
        apply ObjectProperty.hom_ext
        exact (pbcAmbientScalarUnit l Ω T E).hom.naturality f.hom)
  refine ⟨e, rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext _
  exact congrArg (fun η ↦ η.app K) he'

/-- Integral unit with its ambient normalization.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcIntegralScalarUnit (E : Padic.FiniteCoefficientFields l Ω) :
    pbcIntegralScalarExtension l Ω T hdim hl (le_refl E) ≅
        𝟭 (pbcIntegralStage l Ω T E) :=
  (pbcIntegralScalarUnit_exists l Ω T hdim hl E).exists.choose

/-- The integral/rational comparison is fixed by the tensor unit at equal fields
and the unique localization factorization at distinct fields.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: at equal fields use the section-normalized tensor unit. Otherwise use the
equality in the unique factorization through scalar localization. These cases
are exhaustive. Heterogeneous equality retains the exact functor indices under
the literal identity normalization. Either formula specifies every component
and hence gives uniqueness. -/
theorem pbcScalarIntegralComparison_exists (h : E ≤ F) :
    ∃! c : pbcStageLocalization l Ω T E ⋙
        pbcScalarExtension l Ω T hdim hl h ≅
      pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcStageLocalization l Ω T F,
      (E = F → HEq c
        ((Functor.rightUnitor
          (pbcStageLocalization l Ω T E)) ≪≫
        (Functor.leftUnitor
          (pbcStageLocalization l Ω T E)).symm ≪≫
        Functor.isoWhiskerRight (pbcIntegralScalarUnit l Ω T hdim hl E).symm
          (pbcStageLocalization l Ω T E))) ∧
      (E ≠ F → HEq c
        (eqToIso (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose_spec)) := by
  classical
  by_cases hEF : E = F
  · subst F
    have hs : pbcScalarExtension l Ω T hdim hl h = 𝟭 _ := by
      simp [pbcScalarExtension]
    rw [hs]
    let e := (Functor.rightUnitor (pbcStageLocalization l Ω T E)) ≪≫
      (Functor.leftUnitor (pbcStageLocalization l Ω T E)).symm ≪≫
      Functor.isoWhiskerRight (pbcIntegralScalarUnit l Ω T hdim hl E).symm
        (pbcStageLocalization l Ω T E)
    refine ⟨e, ⟨fun _ ↦ HEq.rfl, fun hne ↦ (hne rfl).elim⟩, ?_⟩
    intro e' he'
    exact eq_of_heq (he'.1 rfl)
  · have hs : pbcScalarExtension l Ω T hdim hl h =
        (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose := by
      simp [pbcScalarExtension, hEF]
    rw [hs]
    refine ⟨eqToIso
      (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose_spec,
      ⟨fun heq ↦ (hEF heq).elim, fun _ ↦ HEq.rfl⟩, ?_⟩
    intro e' he'
    exact eq_of_heq (he'.2 hEF)

/-- The uniquely normalized comparison with integral scalar extension.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcScalarIntegralComparison (h : E ≤ F) :
    pbcStageLocalization l Ω T E ⋙
        pbcScalarExtension l Ω T hdim hl h ≅
      pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcStageLocalization l Ω T F :=
  (pbcScalarIntegralComparison_exists l Ω T hdim hl h).exists.choose

/-- The ambient tensor associator is the mate of composition of actual scalar
restrictions, normalized by their identity on sections.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcAmbientScalarAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcAmbientScalarExtension l Ω T h ⋙ pbcAmbientScalarExtension l Ω T k ≅
      pbcAmbientScalarExtension l Ω T (h.trans k) :=
  Adjunction.leftAdjointCompIso
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T h))
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T k))
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T (h.trans k)))
    (pbcDerivedRestrictComp (pbcCompletedScalarMap l Ω T h)
      (pbcCompletedScalarMap l Ω T k) (pbcCompletedScalarMap l Ω T (h.trans k))
      (pbcCompletedScalarMap_comp l Ω T h k))

/-- Restriction of the canonical ambient associator to the full integral subcategories.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: lift its components and inverse components using fullness. Naturality and
inverse equations follow after the faithful inclusion; the same inclusion gives
uniqueness. -/
theorem pbcIntegralScalarAssociator_exists (h : E ≤ F) (k : F ≤ G) :
    ∃! e : pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcIntegralScalarExtension l Ω T hdim hl k ≅
        pbcIntegralScalarExtension l Ω T hdim hl (h.trans k),
      Functor.whiskerRight e.hom
          (pbcStageInclusion l Ω T G) =
        Functor.whiskerLeft
          (pbcStageInclusion l Ω T E)
          (pbcAmbientScalarAssociator l Ω T h k).hom := by
  let e : pbcIntegralScalarExtension l Ω T hdim hl h ⋙
      pbcIntegralScalarExtension l Ω T hdim hl k ≅
      pbcIntegralScalarExtension l Ω T hdim hl (h.trans k) :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _ ((pbcAmbientScalarAssociator l Ω T h k).app K.obj))
      (fun f ↦ by
        apply ObjectProperty.hom_ext
        exact (pbcAmbientScalarAssociator l Ω T h k).hom.naturality f.hom)
  refine ⟨e, rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext _
  exact congrArg (fun η ↦ η.app K) he'

/-- The integral associator with the ambient tensor normalization.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcIntegralScalarAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcIntegralScalarExtension l Ω T hdim hl k ≅
        pbcIntegralScalarExtension l Ω T hdim hl (h.trans k) :=
  (pbcIntegralScalarAssociator_exists l Ω T hdim hl h k).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcDerivedRestriction_leftUnit (h : E ≤ F) :
    pbcDerivedRestrictComp (pbcCompletedScalarMap l Ω T (le_refl E))
        (pbcCompletedScalarMap l Ω T h) (pbcCompletedScalarMap l Ω T h)
        (pbcCompletedScalarMap_comp l Ω T (le_refl E) h) =
      Functor.isoWhiskerLeft (pbcDerivedRestrict (pbcCompletedScalarMap l Ω T h))
          (Functor.exactDerivedRestrictionUnit _
            (SheafOfModules.systemScalarRestrictionUnit
              (pbcCompletedScalarMap l Ω T (le_refl E)) (pbcCompletedScalarMap_id l Ω T E))) ≪≫
        Functor.rightUnitor (pbcDerivedRestrict (pbcCompletedScalarMap l Ω T h)) := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let φ := pbcCompletedScalarMap l Ω T (le_refl E)
  let ψ := pbcCompletedScalarMap l Ω T h
  let ρ := SheafOfModules.systemScalarRestrictionUnit φ (pbcCompletedScalarMap_id l Ω T E)
  have he : pbcRestrictComp φ ψ ψ
      (pbcCompletedScalarMap_comp l Ω T (le_refl E) h) =
      Functor.isoWhiskerLeft (pbcRestrict ψ) ρ := by
    apply Iso.ext
    ext M U x
    change ((pbcRestrictComp φ ψ ψ
      (pbcCompletedScalarMap_comp l Ω T (le_refl E) h)).hom.app M).val.app U x = x
    exact (pbcRestrictComp_exists φ ψ ψ
      (pbcCompletedScalarMap_comp l Ω T (le_refl E) h)).exists.choose_spec M U x
  unfold pbcDerivedRestrictComp
  dsimp only [pbcDerivedRestrict]
  rw [he]
  apply Iso.ext
  ext X
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft
    (pbcRestrict ψ) ρ) X
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_comp_id (pbcRestrict ψ)) X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hn hu
  simp only [Functor.exactDerivedRestrictionUnit, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso (pbcRestrict ψ)
    (pbcRestrict φ)).inv.app X)).1
  erw [Iso.inv_hom_id_app_assoc]
  simp only [← Category.assoc]
  rw [← hn]
  simp only [Category.assoc]
  simp only [NatTrans.id_app] at hu
  erw [reassoc_of% hu]
  erw [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcDerivedRestriction_rightUnit (h : E ≤ F) :
    pbcDerivedRestrictComp (pbcCompletedScalarMap l Ω T h)
        (pbcCompletedScalarMap l Ω T (le_refl F)) (pbcCompletedScalarMap l Ω T h)
        (pbcCompletedScalarMap_comp l Ω T h (le_refl F)) =
      Functor.isoWhiskerRight
          (Functor.exactDerivedRestrictionUnit _
            (SheafOfModules.systemScalarRestrictionUnit
              (pbcCompletedScalarMap l Ω T (le_refl F)) (pbcCompletedScalarMap_id l Ω T F)))
          (pbcDerivedRestrict (pbcCompletedScalarMap l Ω T h)) ≪≫
        Functor.leftUnitor (pbcDerivedRestrict (pbcCompletedScalarMap l Ω T h)) := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let φ := pbcCompletedScalarMap l Ω T h
  let ψ := pbcCompletedScalarMap l Ω T (le_refl F)
  let ρ := SheafOfModules.systemScalarRestrictionUnit ψ (pbcCompletedScalarMap_id l Ω T F)
  have he : pbcRestrictComp φ ψ φ
      (pbcCompletedScalarMap_comp l Ω T h (le_refl F)) =
      Functor.isoWhiskerRight ρ (pbcRestrict φ) := by
    apply Iso.ext
    ext M U x
    change ((pbcRestrictComp φ ψ φ
      (pbcCompletedScalarMap_comp l Ω T h (le_refl F))).hom.app M).val.app U x = x
    exact (pbcRestrictComp_exists φ ψ φ
      (pbcCompletedScalarMap_comp l Ω T h (le_refl F))).exists.choose_spec M U x
  unfold pbcDerivedRestrictComp
  dsimp only [pbcDerivedRestrict]
  rw [he]
  apply Iso.ext
  ext X
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight
    ρ (pbcRestrict φ)) X
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp (pbcRestrict φ)) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hn hu
  simp only [Functor.exactDerivedRestrictionUnit, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, CategoryTheory.Functor.map_comp]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso (pbcRestrict ψ)
    (pbcRestrict φ)).inv.app X)).1
  erw [Iso.inv_hom_id_app_assoc]
  simp only [← Category.assoc]
  rw [← hn]
  simp only [Category.assoc]
  simp only [NatTrans.id_app] at hu
  erw [reassoc_of% hu]
  erw [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcAmbientAssociator_leftUnit (h : E ≤ F) (K : pbcAmbientStage l Ω T E) :
    (pbcAmbientScalarAssociator l Ω T (le_refl E) h).hom.app K =
      (pbcAmbientScalarExtension l Ω T h).map ((pbcAmbientScalarUnit l Ω T E).hom.app K) := by
  have hx := congrArg (fun e ↦ e.hom.app K)
    (Adjunction.leftAdjointCompIso_id_comp
      (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T (le_refl E)))
      (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T h))
      _ _ (pbcDerivedRestriction_leftUnit l Ω T h))
  rw [← pbcAmbientScalarUnit_mate l Ω T E] at hx
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hx
  erw [Category.comp_id] at hx
  exact hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcAmbientAssociator_rightUnit (h : E ≤ F) (K : pbcAmbientStage l Ω T E) :
    (pbcAmbientScalarAssociator l Ω T h (le_refl F)).hom.app K =
      (pbcAmbientScalarUnit l Ω T F).hom.app ((pbcAmbientScalarExtension l Ω T h).obj K) := by
  have hx := congrArg (fun e ↦ e.hom.app K)
    (Adjunction.leftAdjointCompIso_comp_id
      (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T h))
      (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T (le_refl F)))
      _ _ (pbcDerivedRestriction_rightUnit l Ω T h))
  rw [← pbcAmbientScalarUnit_mate l Ω T F] at hx
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at hx
  erw [Category.comp_id] at hx
  exact hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcAmbientScalarAssociator_cocycle
    {H : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) (k : F ≤ G) (j : G ≤ H)
    (K : pbcAmbientStage l Ω T E) :
    (pbcAmbientScalarExtension l Ω T j).map
        ((pbcAmbientScalarAssociator l Ω T h k).hom.app K) ≫
      (pbcAmbientScalarAssociator l Ω T (h.trans k) j).hom.app K =
    (pbcAmbientScalarAssociator l Ω T k j).hom.app
        ((pbcAmbientScalarExtension l Ω T h).obj K) ≫
      (pbcAmbientScalarAssociator l Ω T h (k.trans j)).hom.app K := by
  let a := pbcCompletedScalarMap l Ω T h
  let b := pbcCompletedScalarMap l Ω T k
  let c := pbcCompletedScalarMap l Ω T j
  let ab := pbcCompletedScalarMap l Ω T (h.trans k)
  let bc := pbcCompletedScalarMap l Ω T (k.trans j)
  let abc := pbcCompletedScalarMap l Ω T (h.trans (k.trans j))
  let eab := pbcRestrictComp a b ab (pbcCompletedScalarMap_comp l Ω T h k)
  let ebc := pbcRestrictComp b c bc (pbcCompletedScalarMap_comp l Ω T k j)
  let eabc := pbcRestrictComp a bc abc (pbcCompletedScalarMap_comp l Ω T h (k.trans j))
  let eab_c := pbcRestrictComp ab c abc (pbcCompletedScalarMap_comp l Ω T (h.trans k) j)
  have he : Functor.isoWhiskerLeft (pbcRestrict c) eab ≪≫ eab_c =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ebc (pbcRestrict a) ≪≫ eabc := by
    apply Iso.ext
    ext M U x
    change (eab_c.hom.app M).val.app U ((eab.hom.app ((pbcRestrict c).obj M)).val.app U x) =
      (eabc.hom.app M).val.app U ((ebc.hom.app M).val.app U x)
    erw [(pbcRestrictComp_exists a b ab
        (pbcCompletedScalarMap_comp l Ω T h k)).exists.choose_spec,
      (pbcRestrictComp_exists ab c abc
        (pbcCompletedScalarMap_comp l Ω T (h.trans k) j)).exists.choose_spec,
      (pbcRestrictComp_exists b c bc
        (pbcCompletedScalarMap_comp l Ω T k j)).exists.choose_spec,
      (pbcRestrictComp_exists a bc abc
        (pbcCompletedScalarMap_comp l Ω T h (k.trans j))).exists.choose_spec]
  have hd := SheafOfModules.SuccessiveDerivedQuotient.exactComp_assoc
    (pbcRestrict a) (pbcRestrict b) (pbcRestrict c)
    (pbcRestrict ab) (pbcRestrict bc) (pbcRestrict abc) eab ebc eabc eab_c he
  have hh := Adjunction.leftAdjointCompIso_assoc
    (pbcDerivedScalarAdjunction a) (pbcDerivedScalarAdjunction b)
    (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction ab)
    (pbcDerivedScalarAdjunction bc) (pbcDerivedScalarAdjunction abc)
    (pbcDerivedRestrictComp a b ab _) (pbcDerivedRestrictComp b c bc _)
    (pbcDerivedRestrictComp a bc abc _) (pbcDerivedRestrictComp ab c abc _) hd
  have hx := congrArg (fun e ↦ e.hom.app K) hh
  simpa only [pbcAmbientScalarAssociator, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] using hx.symm

private theorem pbcIntegralScalarAssociator_hom (h : E ≤ F) (k : F ≤ G)
    (K : pbcIntegralStage l Ω T E) :
    ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K).hom =
      (pbcAmbientScalarAssociator l Ω T h k).hom.app K.obj := by
  exact congrArg (fun η ↦ η.app K)
    (pbcIntegralScalarAssociator_exists l Ω T hdim hl h k).exists.choose_spec

private theorem pbcIntegralScalarUnit_hom (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω T E) :
    ((pbcIntegralScalarUnit l Ω T hdim hl E).hom.app K).hom =
      (pbcAmbientScalarUnit l Ω T E).hom.app K.obj := by
  exact congrArg (fun η ↦ η.app K)
    (pbcIntegralScalarUnit_exists l Ω T hdim hl E).exists.choose_spec

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcIntegralAssociator_leftUnit (h : E ≤ F)
    (K : pbcIntegralStage l Ω T E) :
    (pbcIntegralScalarAssociator l Ω T hdim hl (le_refl E) h).hom.app K =
      (pbcIntegralScalarExtension l Ω T hdim hl h).map
        ((pbcIntegralScalarUnit l Ω T hdim hl E).hom.app K) := by
  apply ObjectProperty.hom_ext
  change _ = (pbcAmbientScalarExtension l Ω T h).map
    (((pbcIntegralScalarUnit l Ω T hdim hl E).hom.app K).hom)
  erw [pbcIntegralScalarAssociator_hom, pbcIntegralScalarUnit_hom]
  exact pbcAmbientAssociator_leftUnit l Ω T h K.obj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcIntegralAssociator_rightUnit (h : E ≤ F)
    (K : pbcIntegralStage l Ω T E) :
    (pbcIntegralScalarAssociator l Ω T hdim hl h (le_refl F)).hom.app K =
      (pbcIntegralScalarUnit l Ω T hdim hl F).hom.app
        ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) := by
  apply ObjectProperty.hom_ext
  erw [pbcIntegralScalarAssociator_hom, pbcIntegralScalarUnit_hom]
  exact pbcAmbientAssociator_rightUnit l Ω T h K.obj

private theorem pbcIntegralScalarAssociator_cocycle
    {H : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) (k : F ≤ G) (j : G ≤ H)
    (K : pbcIntegralStage l Ω T E) :
    (pbcIntegralScalarExtension l Ω T hdim hl j).map
        ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K) ≫
      (pbcIntegralScalarAssociator l Ω T hdim hl (h.trans k) j).hom.app K =
    (pbcIntegralScalarAssociator l Ω T hdim hl k j).hom.app
        ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) ≫
      (pbcIntegralScalarAssociator l Ω T hdim hl h (k.trans j)).hom.app K := by
  apply ObjectProperty.hom_ext
  change (pbcAmbientScalarExtension l Ω T j).map
      (((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K).hom) ≫ _ = _
  simp only [ObjectProperty.FullSubcategory.comp_hom, pbcIntegralScalarAssociator_hom]
  exact pbcAmbientScalarAssociator_cocycle l Ω T h k j K.obj

/-- The rational associator is uniquely determined on the unchanged integral objects.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: apply target rationalization to the integral associator, conjugating by
the integral comparisons. Naturality holds on integral morphisms and hence on
their fractions. Rationalization is surjective on objects, giving uniqueness. -/
theorem pbcScalarAssociator_exists (h : E ≤ F) (k : F ≤ G) :
    ∃! e : pbcScalarExtension l Ω T hdim hl h ⋙
        pbcScalarExtension l Ω T hdim hl k ≅
        pbcScalarExtension l Ω T hdim hl (h.trans k),
      ∀ K : pbcIntegralStage l Ω T E,
        e.hom.app
            ((pbcStageLocalization l Ω T E).obj K) =
          (pbcScalarExtension l Ω T hdim hl k).map
              ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K) ≫
            (pbcScalarIntegralComparison l Ω T hdim hl k).hom.app
              ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) ≫
            (pbcStageLocalization l Ω T G).map
              ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K) ≫
            (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k)).inv.app K := by
  let Q := pbcStageLocalization l Ω T E
  let W := pbcStageDenominators l Ω T hdim hl E
  have : Q.IsLocalization W := pbcStageLocalization_isLocalization l Ω T hdim hl E
  let Bh := pbcScalarExtension l Ω T hdim hl h
  let Bk := pbcScalarExtension l Ω T hdim hl k
  let Bhk := pbcScalarExtension l Ω T hdim hl (h.trans k)
  let Ih := pbcIntegralScalarExtension l Ω T hdim hl h
  let Ik := pbcIntegralScalarExtension l Ω T hdim hl k
  let QF := pbcStageLocalization l Ω T F
  let QG := pbcStageLocalization l Ω T G
  let c : Q ⋙ (Bh ⋙ Bk) ≅ Q ⋙ Bhk :=
    (Functor.associator Q Bh Bk).symm ≪≫
      Functor.isoWhiskerRight (pbcScalarIntegralComparison l Ω T hdim hl h) Bk ≪≫
      Functor.associator Ih QF Bk ≪≫
      Functor.isoWhiskerLeft Ih (pbcScalarIntegralComparison l Ω T hdim hl k) ≪≫
      (Functor.associator Ih Ik QG).symm ≪≫
      Functor.isoWhiskerRight (pbcIntegralScalarAssociator l Ω T hdim hl h k) QG ≪≫
      (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k)).symm
  let e := Localization.liftNatIso Q W (Q ⋙ (Bh ⋙ Bk)) (Q ⋙ Bhk) (Bh ⋙ Bk) Bhk c
  have he (K : pbcIntegralStage l Ω T E) :
      e.hom.app (Q.obj K) =
        Bk.map ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K) ≫
        (pbcScalarIntegralComparison l Ω T hdim hl k).hom.app (Ih.obj K) ≫
        QG.map ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K) ≫
        (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k)).inv.app K := by
    change (Localization.liftNatTrans Q W _ _ _ _ c.hom).app (Q.obj K) = _
    rw [Localization.liftNatTrans_app]
    simp only [Localization.Lifting.iso, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Category.id_comp, Category.comp_id]
    simp only [c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Category.id_comp]
    erw [Category.id_comp, Category.id_comp]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact (he' K.obj).trans (he K.obj).symm

/-- The scalar associator induced by tensor balancing, including the normalized units.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcScalarAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcScalarExtension l Ω T hdim hl h ⋙
        pbcScalarExtension l Ω T hdim hl k ≅
        pbcScalarExtension l Ω T hdim hl (h.trans k) :=
  (pbcScalarAssociator_exists l Ω T hdim hl h k).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcScalarAssociator_normalization (h : E ≤ F) (k : F ≤ G)
    (K : pbcIntegralStage l Ω T E) :
    (pbcScalarAssociator l Ω T hdim hl h k).hom.app
        ((pbcStageLocalization l Ω T E).obj K) ≫
      (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k)).hom.app K =
    (pbcScalarExtension l Ω T hdim hl k).map
        ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K) ≫
      (pbcScalarIntegralComparison l Ω T hdim hl k).hom.app
        ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) ≫
      (pbcStageLocalization l Ω T G).map
        ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K) := by
  unfold pbcScalarAssociator
  rw [(pbcScalarAssociator_exists l Ω T hdim hl h k).exists.choose_spec K]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

-- Keep chosen comparisons folded while rewriting their normalization equations.
attribute [local irreducible] pbcScalarIntegralComparison pbcScalarAssociator
  pbcIntegralScalarAssociator

/-- The tensor associators satisfy the pentagon in component form.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the ambient associators are mates of identity-on-sections restriction
comparisons. Their two four-field composites therefore agree. Full integral
inclusions and rational integral comparisons transport that equality; every
rational object is an integral object, so these tests prove the displayed equality. -/
theorem pbcScalarAssociator_cocycle {H : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (k : F ≤ G) (j : G ≤ H)
    (K : pbcStageCategory l Ω T E) :
    (pbcScalarExtension l Ω T hdim hl j).map
          ((pbcScalarAssociator l Ω T hdim hl h k).hom.app K) ≫
        (pbcScalarAssociator l Ω T hdim hl (h.trans k) j).hom.app K =
      (pbcScalarAssociator l Ω T hdim hl k j).hom.app
          ((pbcScalarExtension l Ω T hdim hl h).obj K) ≫
        (pbcScalarAssociator l Ω T hdim hl h (k.trans j)).hom.app K := by
  obtain ⟨KE⟩ := K
  let Ih := pbcIntegralScalarExtension l Ω T hdim hl h
  let Ik := pbcIntegralScalarExtension l Ω T hdim hl k
  let Bj := pbcScalarExtension l Ω T hdim hl j
  let Bk := pbcScalarExtension l Ω T hdim hl k
  let QH := pbcStageLocalization l Ω T H
  have hn := (pbcScalarAssociator l Ω T hdim hl k j).hom.naturality
    ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app KE)
  have hc := (pbcScalarIntegralComparison l Ω T hdim hl j).hom.naturality
    ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app KE)
  apply (cancel_mono
    ((pbcScalarIntegralComparison l Ω T hdim hl (h.trans (k.trans j))).hom.app KE)).1
  simp only [Category.assoc]
  erw [pbcScalarAssociator_normalization l Ω T hdim hl (h.trans k) j KE,
    pbcScalarAssociator_normalization l Ω T hdim hl h (k.trans j) KE]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  erw [pbcScalarAssociator_normalization l Ω T hdim hl h k KE]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  simp only [Functor.comp_map] at hn hc
  erw [← reassoc_of% hn]
  erw [reassoc_of% hc]
  erw [reassoc_of% (pbcScalarAssociator_normalization l Ω T hdim hl k j (Ih.obj KE))]
  have hh := congrArg (fun f ↦ QH.map f)
    (pbcIntegralScalarAssociator_cocycle l Ω T hdim hl h k j KE)
  simp only [CategoryTheory.Functor.map_comp] at hh
  exact congrArg (fun f ↦
    Bj.map (Bk.map ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app KE)) ≫
      Bj.map ((pbcScalarIntegralComparison l Ω T hdim hl k).hom.app (Ih.obj KE)) ≫
      (pbcScalarIntegralComparison l Ω T hdim hl j).hom.app (Ik.obj (Ih.obj KE)) ≫ f) hh

private theorem pbcTransportIso_heq {C D : Type*} [Category* C] [Category* D]
    {A B C' : C ⥤ D} (h : A = B) (e : B ≅ C') : HEq (eqToIso h ≪≫ e) e := by
  subst B
  simp

private theorem pbcScalarIntegralComparison_refl
    (E : Padic.FiniteCoefficientFields l Ω)
    (hs : pbcScalarExtension l Ω T hdim hl (le_refl E) = 𝟭 _) :
    pbcScalarIntegralComparison l Ω T hdim hl (le_refl E) =
      eqToIso (congrArg (fun B ↦ pbcStageLocalization l Ω T E ⋙ B) hs) ≪≫
        (Functor.rightUnitor (pbcStageLocalization l Ω T E) ≪≫
          (Functor.leftUnitor (pbcStageLocalization l Ω T E)).symm ≪≫
          Functor.isoWhiskerRight (pbcIntegralScalarUnit l Ω T hdim hl E).symm
            (pbcStageLocalization l Ω T E)) := by
  unfold pbcScalarIntegralComparison
  apply eq_of_heq
  exact ((pbcScalarIntegralComparison_exists l Ω T hdim hl (le_refl E)).exists.choose_spec.1
    rfl).trans (pbcTransportIso_heq
      (congrArg (fun B ↦ pbcStageLocalization l Ω T E ⋙ B) hs) _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcScalarAssociator_leftUnit (h : E ≤ F)
    (hs : pbcScalarExtension l Ω T hdim hl (le_refl E) = 𝟭 _) :
    pbcScalarAssociator l Ω T hdim hl (le_refl E) h =
      eqToIso (congrArg (fun B ↦ B ⋙ pbcScalarExtension l Ω T hdim hl h) hs) ≪≫
        Functor.leftUnitor (pbcScalarExtension l Ω T hdim hl h) := by
  unfold pbcScalarAssociator
  symm
  apply (pbcScalarAssociator_exists l Ω T hdim hl (le_refl E) h).unique _
    (pbcScalarAssociator_exists l Ω T hdim hl (le_refl E) h).exists.choose_spec
  intro K
  apply (cancel_mono ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [pbcIntegralAssociator_leftUnit,
    pbcScalarIntegralComparison_refl l Ω T hdim hl E hs]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, NatTrans.comp_app,
    eqToHom_app, Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp,
    Functor.leftUnitor_hom_app]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (pbcScalarIntegralComparison l Ω T hdim hl h).hom.naturality
    ((pbcIntegralScalarUnit l Ω T hdim hl E).inv.app K)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]
  have hu := congrArg (fun f ↦ (pbcStageLocalization l Ω T F).map
    ((pbcIntegralScalarExtension l Ω T hdim hl h).map f))
    (Iso.inv_hom_id_app (pbcIntegralScalarUnit l Ω T hdim hl E) K)
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hu
  erw [hu]
  erw [Category.comp_id]
  simp only [eqToHom_map]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcScalarAssociator_rightUnit (h : E ≤ F)
    (hs : pbcScalarExtension l Ω T hdim hl (le_refl F) = 𝟭 _) :
    pbcScalarAssociator l Ω T hdim hl h (le_refl F) =
      eqToIso (congrArg (fun B ↦ pbcScalarExtension l Ω T hdim hl h ⋙ B) hs) ≪≫
        Functor.rightUnitor (pbcScalarExtension l Ω T hdim hl h) := by
  unfold pbcScalarAssociator
  symm
  apply (pbcScalarAssociator_exists l Ω T hdim hl h (le_refl F)).unique _
    (pbcScalarAssociator_exists l Ω T hdim hl h (le_refl F)).exists.choose_spec
  intro K
  apply (cancel_mono ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [pbcIntegralAssociator_rightUnit,
    pbcScalarIntegralComparison_refl l Ω T hdim hl F hs]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, NatTrans.comp_app,
    eqToHom_app, Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp,
    Category.assoc]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  erw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]
  have hn := (eqToIso hs).hom.naturality
    ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K)
  simpa only [eqToIso.hom, eqToHom_app, Functor.id_map] using hn.symm

/-- Normalized tensor identities give the literal identity transitions and unit associators.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the equal-field branch of pbcScalarExtension is identity by definition.
The ambient tensor-unit comparison is multiplication on pure tensors, and the
ambient associator is tensor balancing with the same ordinary adjunction units.
Their unit equations hold on those generators. Faithful integral inclusions and
rationalization transport the equations, including repeated coefficient fields. -/
theorem pbcScalarSystem_units (h : E ≤ F) :
    pbcScalarExtension l Ω T hdim hl (le_refl E) = 𝟭 _ ∧
      HEq (pbcScalarAssociator l Ω T hdim hl (le_refl E) h)
        (Functor.leftUnitor (pbcScalarExtension l Ω T hdim hl h)) ∧
      HEq (pbcScalarAssociator l Ω T hdim hl h (le_refl F))
        (Functor.rightUnitor (pbcScalarExtension l Ω T hdim hl h)) := by
  classical
  have hsE : pbcScalarExtension l Ω T hdim hl (le_refl E) = 𝟭 _ := by
    simp [pbcScalarExtension]
  have hsF : pbcScalarExtension l Ω T hdim hl (le_refl F) = 𝟭 _ := by
    simp [pbcScalarExtension]
  refine ⟨hsE, ?_, ?_⟩
  · exact (heq_of_eq (pbcScalarAssociator_leftUnit l Ω T hdim hl h hsE)).trans
      (pbcTransportIso_heq
        (congrArg (fun B ↦ B ⋙ pbcScalarExtension l Ω T hdim hl h) hsE) _)
  · exact (heq_of_eq (pbcScalarAssociator_rightUnit l Ω T hdim hl h hsF)).trans
      (pbcTransportIso_heq
        (congrArg (fun B ↦ pbcScalarExtension l Ω T hdim hl h ⋙ B) hsF) _)

/-- Rationalized tensor extension is additive.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: tensor extension is additive on complexes and derived morphisms. The
localization formula sends sums of fractions to sums; identity fields are
literal identity functors, which are additive as well. -/
@[instance] theorem pbcScalarExtension_additive (h : E ≤ F) :
    (pbcScalarExtension l Ω T hdim hl h).Additive := by
  classical
  by_cases hEF : E = F
  · subst F
    have hs : pbcScalarExtension l Ω T hdim hl h = 𝟭 _ := by
      simp [pbcScalarExtension]
    rw [hs]
    infer_instance
  · have hs : pbcScalarExtension l Ω T hdim hl h =
        (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose := by
      simp only [pbcScalarExtension, dite_eq_right hEF]
    rw [hs]
    have hB := (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose_spec
    have : (pbcIntegralScalarExtension l Ω T hdim hl h).Additive := by
      rw [pbcIntegralScalarExtension_eq l Ω T hdim hl h]
      let φ := pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T
      have : (pbcDerivedRestrict φ).Additive := by
        dsimp only [pbcDerivedRestrict]
        infer_instance
      have : (pbcDerivedExtend φ).Additive :=
        (pbcDerivedScalarAdjunction φ).left_adjoint_additive
      constructor
      intros X Y f g
      apply ObjectProperty.hom_ext
      exact (pbcDerivedExtend φ).map_add
    have : (pbcStageLocalization l Ω T E).IsLocalization
        (pbcStageDenominators l Ω T hdim hl E) :=
      pbcStageLocalization_isLocalization l Ω T hdim hl E
    apply (Localization.functor_additive_iff (pbcStageLocalization l Ω T E)
      (pbcStageDenominators l Ω T hdim hl E) _).2
    rw [hB]
    infer_instance

/-- The concrete finite-stage scalar system on the PBC raw rational categories.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcScalarSystem :
    StageSystem (fun E : Padic.FiniteCoefficientFields l Ω ↦
      pbcStageCategory l Ω T E) where
  T h := pbcScalarExtension l Ω T hdim hl h
  assoc h k := pbcScalarAssociator l Ω T hdim hl h k
  cocycle h k j K := pbcScalarAssociator_cocycle l Ω T hdim hl h k j K

/-- Finite composita give the common coefficient stages.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category). -/
instance pbcFiniteCoefficientFields_directed :
    IsDirectedOrder (Padic.FiniteCoefficientFields l Ω) :=
  ⟨fun E F ↦ ⟨Padic.finiteCoefficientCompositum l Ω E F,
    (Padic.finiteCoefficientFields_properties l Ω).1 E F⟩⟩

/-- The concrete PBC finite-stage pair category, without an idempotent envelope.
Its quotient representatives, transport, identities and common-stage composition
are exactly StageSystem.PairCategory with this concrete coefficient system.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev PbcFiniteStagePairCategory := (pbcScalarSystem l Ω T hdim hl).PairCategory

/-- The base field witnesses nonemptiness, including the empty-diagram case.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
instance pbcFiniteCoefficientFields_nonempty : Nonempty (Padic.FiniteCoefficientFields l Ω) :=
  ⟨Padic.finiteCoefficientBase l Ω⟩

end AlgebraicGeometry.Scheme
