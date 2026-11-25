/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Localized.LocalizedTStructure
public import WeilConjectures.CategoryTheory.StageSystem.PbcQbarCategory
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.CategoryTheory.StageSystem.Morphism.PbcDescentFunctors
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.Constructible
public import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackTriangles
import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import WeilConjectures.AlgebraicGeometry.Pbc.PbcConstructibleReductionPullback
import WeilConjectures.AlgebraicGeometry.Pbc.PbcConstructibleReductionCriterion
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionCriterion

import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousAffineEtaleLattice
import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseRepresentations
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
import Mathlib.GroupTheory.Index
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantCover
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTStructure
import WeilConjectures.AlgebraicGeometry.Lisse.LisseTensorScalarExtension
import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import all WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Constructible adic hearts, pullback, and geometric coefficient fibres

The finite-stage categories are the recorded raw localizations, and the algebraic
coefficient category is the recorded common-stage pair category. The fibres below
are normalized by completed geometric pullback, degree-zero cohomology, evaluation
at the final pro-etale object, and inversion of the uniformizer.

## Main definitions

* `rationalT`, `commonT`: the prescribed finite and common-stage standard t-structures.
* `rationalPull`, `commonPull`: the normalized actual completed pullback functors.
* `integralFiber`, `integralLimitFiber`, `fiber`: completed-section and adic-limit fibres.

## Main statement

* `adicHeartPullbackFibres`: all standard-heart, scalar, pullback and geometric-fibre clauses.

## References

* Bhatt--Scholze, The pro-etale topology for schemes, Section 6.8, Lemmas 6.8.2 and 6.8.7,
  Definitions 6.8.3, 6.8.6, 6.8.8 and 6.8.10, Propositions 6.8.4, 6.8.11 and 6.8.14, and Remark
  6.8.15
* BBD 1.3.3
* BBD 1.3.1
* Stacks Tag 06YY
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v r s
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory.Triangulated.TStructure

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- If `Q` is essentially surjective, maps the aisle of `t` into that of `t'` and commutes
with the truncations, then the aisle of `t'` is the essential image of the aisle of `t`. -/
lemma le_iff_exists_of_truncLE (t : TStructure C) (t' : TStructure D) (Q : C ⥤ D) (n : ℤ)
    (hQ : ∀ X : D, ∃ K : C, Nonempty (X ≅ Q.obj K))
    (htr : Nonempty (Q ⋙ t'.truncLE n ≅ t.truncLE n ⋙ Q))
    (hle : ∀ K : C, t.le n K → t'.le n (Q.obj K)) (X : D) :
    t'.le n X ↔ ∃ K : C, t.le n K ∧ Nonempty (X ≅ Q.obj K) := by
  refine ⟨fun hX ↦ ?_, fun ⟨K, hK, ⟨e⟩⟩ ↦ (t'.le n).prop_of_iso e.symm (hle K hK)⟩
  obtain ⟨K, ⟨e⟩⟩ := hQ X
  obtain ⟨e'⟩ := htr
  have : t'.IsLE (Q.obj K) n := ⟨(t'.le n).prop_of_iso e hX⟩
  exact ⟨(t.truncLE n).obj K, (t.isLE_truncLE_obj K n n le_rfl).le,
    ⟨e ≪≫ (asIso ((t'.truncLEι n).app (Q.obj K))).symm ≪≫ e'.app K⟩⟩

/-- If `Q` is essentially surjective, maps the coaisle of `t` into that of `t'` and
commutes with the truncations, then the coaisle of `t'` is the essential image of the
coaisle of `t`. -/
lemma ge_iff_exists_of_truncGE (t : TStructure C) (t' : TStructure D) (Q : C ⥤ D) (n : ℤ)
    (hQ : ∀ X : D, ∃ K : C, Nonempty (X ≅ Q.obj K))
    (htr : Nonempty (Q ⋙ t'.truncGE n ≅ t.truncGE n ⋙ Q))
    (hge : ∀ K : C, t.ge n K → t'.ge n (Q.obj K)) (X : D) :
    t'.ge n X ↔ ∃ K : C, t.ge n K ∧ Nonempty (X ≅ Q.obj K) := by
  refine ⟨fun hX ↦ ?_, fun ⟨K, hK, ⟨e⟩⟩ ↦ (t'.ge n).prop_of_iso e.symm (hge K hK)⟩
  obtain ⟨K, ⟨e⟩⟩ := hQ X
  obtain ⟨e'⟩ := htr
  have : t'.IsGE (Q.obj K) n := ⟨(t'.ge n).prop_of_iso e hX⟩
  exact ⟨(t.truncGE n).obj K, (t.isGE_truncGE_obj K n n le_rfl).ge,
    ⟨e ≪≫ asIso ((t'.truncGEπ n).app (Q.obj K)) ≪≫ e'.app K⟩⟩

/-- A t-structure is determined by its aisles and coaisles. -/
lemma ext_of_le_ge {t₁ t₂ : TStructure C} (hle : t₁.le = t₂.le) (hge : t₁.ge = t₂.ge) :
    t₁ = t₂ := by
  cases t₁
  cases t₂
  subst hle
  subst hge
  rfl

end CategoryTheory.Triangulated.TStructure

namespace AlgebraicGeometry.Scheme

section ExactScalarExtension

variable {X : Scheme.{u}} {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (f : R ⟶ S)
  [PreservesFiniteLimits (pbcExtend f)] [PreservesFiniteColimits (pbcExtend f)]

/-- An exact ordinary scalar extension computes its universal derived functor. -/
theorem pbcDerivedExtend_iso_mapDerivedCategory :
    Nonempty (pbcDerivedExtend f ≅ (pbcExtend f).mapDerivedCategory) := by
  have : (pbcDerivedExtend f).IsLeftDerivedFunctor (pbcExtensionCounit f)
      (HomotopyCategory.quasiIso (pbcModules X R) (.up ℤ)) := pbcDerivedExtension_universal f
  have : (pbcExtend f).mapDerivedCategory.IsLeftDerivedFunctor
      (pbcExtend f).mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (pbcModules X R) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ (pbcExtend f).mapDerivedCategoryFactorsh
  exact ⟨Functor.leftDerivedNatIso _ _ (pbcExtensionCounit f)
    (pbcExtend f).mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (pbcModules X R) (.up ℤ)) (Iso.refl _)⟩

/-- An exact scalar extension preserves the standard aisles. -/
theorem pbcDerivedExtend_le (K : DerivedCategory (pbcModules X R)) (n : ℤ)
    (hK : DerivedCategory.TStructure.t.le n K) :
    DerivedCategory.TStructure.t.le n ((pbcDerivedExtend f).obj K) := by
  obtain ⟨e⟩ := pbcDerivedExtend_iso_mapDerivedCategory f
  have : K.IsLE n := ⟨hK⟩
  have := (pbcExtend f).isLE_mapDerivedCategory_obj K n
  exact (DerivedCategory.TStructure.t.isLE_of_iso (e.app K).symm n).le

/-- An exact scalar extension preserves the standard coaisles. -/
theorem pbcDerivedExtend_ge (K : DerivedCategory (pbcModules X R)) (n : ℤ)
    (hK : DerivedCategory.TStructure.t.ge n K) :
    DerivedCategory.TStructure.t.ge n ((pbcDerivedExtend f).obj K) := by
  obtain ⟨e⟩ := pbcDerivedExtend_iso_mapDerivedCategory f
  have : K.IsGE n := ⟨hK⟩
  have := (pbcExtend f).isGE_mapDerivedCategory_obj K n
  exact (DerivedCategory.TStructure.t.isGE_of_iso (e.app K).symm n).ge

end ExactScalarExtension

section StageScalarExtension

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
  (T : Scheme.{u}) {E F : Padic.FiniteCoefficientFields l Ω}

/-- Ordinary finite coefficient extension between stages preserves finite limits. -/
theorem pbcExtend_completedScalarMap_preservesFiniteLimits (h : E ≤ F) :
    PreservesFiniteLimits (pbcExtend (pbcCompletedScalarMap l Ω T h)) := by
  rw [pbcStageCoefficientMap_eq l Ω T h]
  exact (WeilConjectures.scalarExtension_exact l _ _ _ T).1

/-- Ordinary finite coefficient extension between stages preserves finite colimits. -/
theorem pbcExtend_completedScalarMap_preservesFiniteColimits (h : E ≤ F) :
    PreservesFiniteColimits (pbcExtend (pbcCompletedScalarMap l Ω T h)) := by
  rw [pbcStageCoefficientMap_eq l Ω T h]
  exact (WeilConjectures.scalarExtension_exact l _ _ _ T).2

end StageScalarExtension

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.PerAdic

/-- A separated finite-type k-scheme; no geometric connectedness or nonemptiness is imposed. -/
structure Base (k : Type u) [Field k] where
  scheme : Scheme.{u}
  [isOver : scheme.Over (Spec (.of k))]
  [finiteTypeLocal : LocallyOfFiniteType (scheme ↘ Spec (.of k))]
  [finiteTypeCompact : QuasiCompact (scheme ↘ Spec (.of k))]
  [separated : IsSeparated (scheme ↘ Spec (.of k))]

attribute [instance] Base.isOver Base.finiteTypeLocal Base.finiteTypeCompact Base.separated

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [hl : Fact (IsUnit (l : k))]

set_option linter.unusedSectionVars false in
include hl in
/-- Finite type over a field gives exactly the hypotheses of the recorded adic categories. -/
theorem base_properties (W : Base k) :
    IsNoetherian W.scheme ∧ (∃ n : ℕ, topologicalKrullDim W.scheme ≤ n) ∧
      (∀ x : W.scheme, IsUnit (l : W.scheme.presheaf.stalk x)) := by
  have hloc : IsLocallyNoetherian W.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.scheme ↘ Spec (.of k))
  have hcompact : CompactSpace W.scheme :=
    QuasiCompact.compactSpace_of_compactSpace (W.scheme ↘ Spec (.of k))
  refine ⟨⟨⟩, exists_topologicalKrullDim_le (W.scheme ↘ Spec (.of k)), ?_⟩
  intro x
  simpa only [map_natCast] using hl.out.map
    (((Scheme.ΓSpecIso (.of k)).inv ≫ (W.scheme ↘ Spec (.of k)).appTop) ≫
      W.scheme.presheaf.germ ⊤ x trivial).hom

/-- The two geometric finiteness properties do not depend on the coefficient prime. -/
theorem base_geometric_properties (W : Base k) :
    IsNoetherian W.scheme ∧ (∃ n : ℕ, topologicalKrullDim W.scheme ≤ n) := by
  have hloc : IsLocallyNoetherian W.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.scheme ↘ Spec (.of k))
  have hcompact : CompactSpace W.scheme :=
    QuasiCompact.compactSpace_of_compactSpace (W.scheme ↘ Spec (.of k))
  exact ⟨⟨⟩, exists_topologicalKrullDim_le (W.scheme ↘ Spec (.of k))⟩

/-- The noetherian structure supplied by the finite-type hypothesis. -/
instance baseNoetherian (W : Base k) : IsNoetherian W.scheme :=
  (base_geometric_properties W).1

/-- The finite dimension bound supplied by the finite-type hypothesis. -/
instance baseDimension (W : Base k) : Fact (∃ n : ℕ, topologicalKrullDim W.scheme ≤ n) :=
  ⟨(base_geometric_properties W).2⟩

/-- Invertibility of the coefficient prime on every local ring. -/
instance basePrimeUnit (W : Base k) : Fact (∀ x : W.scheme,
    IsUnit (l : W.scheme.presheaf.stalk x)) :=
  ⟨(base_properties l W).2.2⟩

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded localized standard t-structure; its classes are fixed by integral images. -/
@[irreducible]
def rationalT (W : Base k) :
    Triangulated.TStructure
      (PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  @Classical.choose _ _ (pbc_localized_tstructure W.scheme l E
    (hNoeth := baseNoetherian W) (hDim := baseDimension W)
    (hInv := basePrimeUnit l W))

/-- The recorded finite-stage aisle, exposed as an object predicate independently
of competing stage shift instances. -/
abbrev rationalLE (W : Base k) (n : ℤ) :
    ObjectProperty (PbcRationalCategory W.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)) := (rationalT l E W).le n

/-- The recorded finite-stage coaisle, exposed as an object predicate. -/
abbrev rationalGE (W : Base k) (n : ℤ) :
    ObjectProperty (PbcRationalCategory W.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)) := (rationalT l E W).ge n

/-- The aisles of the recorded localized t-structure consist of the images of integral
objects in the corresponding integral aisles. -/
theorem rationalLE_iff (W : Base k) (n : ℤ)
    (X : PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)) :
    rationalLE l E W n X ↔
      ∃ K : PbcBoundedConstructibleComplete W.scheme (pbcIntegralDatum l E),
      (pbcIntegralTStructure W.scheme l E).le n K ∧
        Nonempty (X ≅ (pbcRationalization W.scheme (pbcIntegralDatum l E)
          (pbcUniformizer l E)).obj K) := by
  unfold rationalLE rationalT
  have h := Classical.choose_spec (pbc_localized_tstructure W.scheme l E
    (hNoeth := baseNoetherian W) (hDim := baseDimension W) (hInv := basePrimeUnit l W))
  exact Triangulated.TStructure.le_iff_exists_of_truncLE _ _ _ n
    (fun X ↦ ⟨X.obj, ⟨Iso.refl _⟩⟩) (h.2.2.2.1 n).1 (fun K ↦ (h.2.2.1 K n).1) X

/-- The coaisles of the recorded localized t-structure consist of the images of integral
objects in the corresponding integral coaisles. -/
theorem rationalGE_iff (W : Base k) (n : ℤ)
    (X : PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)) :
    rationalGE l E W n X ↔
      ∃ K : PbcBoundedConstructibleComplete W.scheme (pbcIntegralDatum l E),
      (pbcIntegralTStructure W.scheme l E).ge n K ∧
        Nonempty (X ≅ (pbcRationalization W.scheme (pbcIntegralDatum l E)
          (pbcUniformizer l E)).obj K) := by
  unfold rationalGE rationalT
  have h := Classical.choose_spec (pbc_localized_tstructure W.scheme l E
    (hNoeth := baseNoetherian W) (hDim := baseDimension W) (hInv := basePrimeUnit l W))
  exact Triangulated.TStructure.ge_iff_exists_of_truncGE _ _ _ n
    (fun X ↦ ⟨X.obj, ⟨Iso.refl _⟩⟩) (h.2.2.2.1 n).2 (fun K ↦ (h.2.2.1 K n).2) X

/-- The recorded localized t-structure is bounded. -/
theorem rationalT_bounded (W : Base k) : (rationalT l E W).bounded = ⊤ := by
  unfold rationalT
  exact (Classical.choose_spec (pbc_localized_tstructure W.scheme l E
    (hNoeth := baseNoetherian W) (hDim := baseDimension W)
    (hInv := basePrimeUnit l W))).2.1

/-- Orthogonality of the recorded localized aisle and shifted coaisle. -/
theorem rational_hom_eq_zero (W : Base k)
    {X Y : PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)}
    (f : X ⟶ Y) (hX : rationalLE l E W 0 X) (hY : rationalGE l E W 1 Y) : f = 0 :=
  (rationalT l E W).zero' f hX hY

/-- The recorded localized aisles increase. -/
theorem rationalLE_zero_one (W : Base k)
    (X : PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
    (hX : rationalLE l E W 0 X) : rationalLE l E W 1 X :=
  (rationalT l E W).le_zero_le X hX

/-- The recorded localized coaisles decrease. -/
theorem rationalGE_one_zero (W : Base k)
    (X : PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
    (hX : rationalGE l E W 1 X) : rationalGE l E W 0 X :=
  (rationalT l E W).ge_one_le X hX

/-- Every object is bounded for the recorded localized t-structure. -/
theorem rational_exists_bounds (W : Base k)
    (X : PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)) :
    (∃ a : ℤ, rationalGE l E W a X) ∧ ∃ b : ℤ, rationalLE l E W b X := by
  have hX : (rationalT l E W).bounded X := by
    rw [rationalT_bounded]
    trivial
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hX
  exact ⟨⟨a, ha.ge⟩, ⟨b, hb.le⟩⟩

variable (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
  [IsAlgClosure (Padic l) Qbar]

/-- The recorded coherent scalar system at a separated finite-type base. -/
abbrev stages (W : Base k) :=
  pbcScalarSystem l Qbar W.scheme (baseDimension W).out (basePrimeUnit l W).out

/-- The existing inclusion of a finite coefficient field in the raw common-stage category. -/
abbrev inclusion (W : Base k) (L : Padic.FiniteCoefficientFields l Qbar) :=
  (stages l Qbar W).ι L

/-- Common-stage classes are precisely the isomorphism closures of finite-stage classes. -/
@[irreducible]
def commonClass (W : Base k) (nonpositive : Bool) (n : ℤ) :
    ObjectProperty (pbcQbarCategory l Qbar W.scheme) :=
  fun K ↦ ∃ (L : Padic.FiniteCoefficientFields l Qbar)
    (M : pbcStageCategory l Qbar W.scheme L),
    (if nonpositive then rationalLE l (pbcFiniteField.{u} l Qbar L) W n M
      else rationalGE l (pbcFiniteField.{u} l Qbar L) W n M) ∧
      Nonempty (K ≅ (inclusion l Qbar W L).obj M)

/-- The nonpositive common-stage classes, unfolded. -/
theorem commonClass_true_iff (W : Base k) (n : ℤ) (K : pbcQbarCategory l Qbar W.scheme) :
    commonClass l Qbar W true n K ↔ ∃ (L : Padic.FiniteCoefficientFields l Qbar)
      (M : pbcStageCategory l Qbar W.scheme L),
      rationalLE l (pbcFiniteField.{u} l Qbar L) W n M ∧
        Nonempty (K ≅ (inclusion l Qbar W L).obj M) := by
  unfold commonClass
  exact Iff.rfl

/-- The nonnegative common-stage classes, unfolded. -/
theorem commonClass_false_iff (W : Base k) (n : ℤ) (K : pbcQbarCategory l Qbar W.scheme) :
    commonClass l Qbar W false n K ↔ ∃ (L : Padic.FiniteCoefficientFields l Qbar)
      (M : pbcStageCategory l Qbar W.scheme L),
      rationalGE l (pbcFiniteField.{u} l Qbar L) W n M ∧
        Nonempty (K ≅ (inclusion l Qbar W L).obj M) := by
  unfold commonClass
  exact Iff.rfl

/-- Finite scalar extension between stages preserves the finite-stage aisles. -/
theorem rationalLE_stageExtension (W : Base k) {L L' : Padic.FiniteCoefficientFields l Qbar}
    (h : L ≤ L') (n : ℤ) (M : pbcStageCategory l Qbar W.scheme L)
    (hM : rationalLE l (pbcFiniteField.{u} l Qbar L) W n M) :
    rationalLE l (pbcFiniteField.{u} l Qbar L') W n (((stages l Qbar W).T h).obj M) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := (rationalLE_iff l _ W n M).1 hM
  have := pbcExtend_completedScalarMap_preservesFiniteLimits l Qbar W.scheme h
  have := pbcExtend_completedScalarMap_preservesFiniteColimits l Qbar W.scheme h
  exact (rationalLE_iff l _ W n _).2
    ⟨(pbcIntegralScalarExtension l Qbar W.scheme (baseDimension W).out
        (basePrimeUnit l W).out h).obj K,
      pbcDerivedExtend_le (pbcCompletedScalarMap l Qbar W.scheme h) K.obj n hK,
      ⟨((stages l Qbar W).T h).mapIso e ≪≫ (pbcScalarIntegralComparison l Qbar W.scheme
        (baseDimension W).out (basePrimeUnit l W).out h).app K⟩⟩

/-- Finite scalar extension between stages preserves the finite-stage coaisles. -/
theorem rationalGE_stageExtension (W : Base k) {L L' : Padic.FiniteCoefficientFields l Qbar}
    (h : L ≤ L') (n : ℤ) (M : pbcStageCategory l Qbar W.scheme L)
    (hM : rationalGE l (pbcFiniteField.{u} l Qbar L) W n M) :
    rationalGE l (pbcFiniteField.{u} l Qbar L') W n (((stages l Qbar W).T h).obj M) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := (rationalGE_iff l _ W n M).1 hM
  have := pbcExtend_completedScalarMap_preservesFiniteLimits l Qbar W.scheme h
  have := pbcExtend_completedScalarMap_preservesFiniteColimits l Qbar W.scheme h
  exact (rationalGE_iff l _ W n _).2
    ⟨(pbcIntegralScalarExtension l Qbar W.scheme (baseDimension W).out
        (basePrimeUnit l W).out h).obj K,
      pbcDerivedExtend_ge (pbcCompletedScalarMap l Qbar W.scheme h) K.obj n hK,
      ⟨((stages l Qbar W).T h).mapIso e ≪≫ (pbcScalarIntegralComparison l Qbar W.scheme
        (baseDimension W).out (basePrimeUnit l W).out h).app K⟩⟩

/-- The finite-stage aisles are stable under the normalized stage shift. -/
theorem rationalLE_shift (W : Base k) (L : Padic.FiniteCoefficientFields l Qbar)
    (n a n' : ℤ) (hn : a + n' = n) (M : pbcStageCategory l Qbar W.scheme L)
    (hM : rationalLE l (pbcFiniteField.{u} l Qbar L) W n M) :
    rationalLE l (pbcFiniteField.{u} l Qbar L) W n'
      ((@shiftFunctor (pbcStageCategory l Qbar W.scheme L) ℤ _ _
        (pbcRationalHasShift l Qbar W.scheme L) a).obj M) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := (rationalLE_iff l _ W n M).1 hM
  exact (rationalLE_iff l _ W n' _).2 ⟨(shiftFunctor _ a).obj K,
    (pbcIntegralTStructure W.scheme l _).le_shift n a n' hn K hK,
    ⟨(@shiftFunctor (pbcStageCategory l Qbar W.scheme L) ℤ _ _
        (pbcRationalHasShift l Qbar W.scheme L) a).mapIso e ≪≫
      ((pbcStageLocalization l Qbar W.scheme L).commShiftIso a).symm.app K⟩⟩

/-- The finite-stage coaisles are stable under the normalized stage shift. -/
theorem rationalGE_shift (W : Base k) (L : Padic.FiniteCoefficientFields l Qbar)
    (n a n' : ℤ) (hn : a + n' = n) (M : pbcStageCategory l Qbar W.scheme L)
    (hM : rationalGE l (pbcFiniteField.{u} l Qbar L) W n M) :
    rationalGE l (pbcFiniteField.{u} l Qbar L) W n'
      ((@shiftFunctor (pbcStageCategory l Qbar W.scheme L) ℤ _ _
        (pbcRationalHasShift l Qbar W.scheme L) a).obj M) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := (rationalGE_iff l _ W n M).1 hM
  exact (rationalGE_iff l _ W n' _).2 ⟨(shiftFunctor _ a).obj K,
    (pbcIntegralTStructure W.scheme l _).ge_shift n a n' hn K hK,
    ⟨(@shiftFunctor (pbcStageCategory l Qbar W.scheme L) ℤ _ _
        (pbcRationalHasShift l Qbar W.scheme L) a).mapIso e ≪≫
      ((pbcStageLocalization l Qbar W.scheme L).commShiftIso a).symm.app K⟩⟩

/-- The common-stage classes are closed under isomorphisms. -/
theorem commonClass_of_iso (W : Base k) (b : Bool) (n : ℤ)
    {X Y : pbcQbarCategory l Qbar W.scheme} (e : X ≅ Y) (hX : commonClass l Qbar W b n X) :
    commonClass l Qbar W b n Y := by
  unfold commonClass at hX ⊢
  obtain ⟨L, M, hM, ⟨e'⟩⟩ := hX
  exact ⟨L, M, hM, ⟨e.symm ≪≫ e'⟩⟩

/-- The nonpositive common-stage classes are stable under shifts. -/
theorem commonClass_true_shift (W : Base k) (n a n' : ℤ) (hn : a + n' = n)
    (X : pbcQbarCategory l Qbar W.scheme) (hX : commonClass l Qbar W true n X) :
    commonClass l Qbar W true n' (X⟦a⟧) := by
  obtain ⟨L, M, hM, ⟨e⟩⟩ := (commonClass_true_iff l Qbar W n X).1 hX
  exact (commonClass_true_iff l Qbar W n' _).2 ⟨L, _,
    rationalLE_shift l Qbar W L n a n' hn M hM,
    ⟨(shiftFunctor _ a).mapIso e ≪≫ ((inclusion l Qbar W L).commShiftIso a).symm.app M⟩⟩

/-- The nonnegative common-stage classes are stable under shifts. -/
theorem commonClass_false_shift (W : Base k) (n a n' : ℤ) (hn : a + n' = n)
    (X : pbcQbarCategory l Qbar W.scheme) (hX : commonClass l Qbar W false n X) :
    commonClass l Qbar W false n' (X⟦a⟧) := by
  obtain ⟨L, M, hM, ⟨e⟩⟩ := (commonClass_false_iff l Qbar W n X).1 hX
  exact (commonClass_false_iff l Qbar W n' _).2 ⟨L, _,
    rationalGE_shift l Qbar W L n a n' hn M hM,
    ⟨(shiftFunctor _ a).mapIso e ≪≫ ((inclusion l Qbar W L).commShiftIso a).symm.app M⟩⟩

/-- Orthogonality of the common-stage classes, checked at a common field. -/
theorem commonClass_hom_eq_zero (W : Base k) {X Y : pbcQbarCategory l Qbar W.scheme}
    (f : X ⟶ Y) (hX : commonClass l Qbar W true 0 X) (hY : commonClass l Qbar W false 1 Y) :
    f = 0 := by
  obtain ⟨L, M, hM, ⟨eX⟩⟩ := (commonClass_true_iff l Qbar W 0 X).1 hX
  obtain ⟨L', N, hN, ⟨eY⟩⟩ := (commonClass_false_iff l Qbar W 1 Y).1 hY
  rw [← cancel_epi eX.inv, ← cancel_mono eY.hom, Limits.comp_zero, Limits.zero_comp,
    Category.assoc]
  obtain ⟨P, -, hL, hL', u, hu⟩ :=
    StageSystem.PairCategory.exists_le_mkHom_eq (eX.inv ≫ f ≫ eY.hom) L
  rw [hu, rational_hom_eq_zero l _ W u (rationalLE_stageExtension l Qbar W hL 0 M hM)
    (rationalGE_stageExtension l Qbar W hL' 1 N hN)]
  exact ((stages l Qbar W).pairPreadditive_exists.exists.choose_spec _ _ P hL hL' 0 0).2

/-- The finite-stage truncation triangle gives the common-stage decomposition. -/
theorem commonClass_exists_triangle (W : Base k) (A : pbcQbarCategory l Qbar W.scheme) :
    ∃ (X Y : pbcQbarCategory l Qbar W.scheme) (_ : commonClass l Qbar W true 0 X)
      (_ : commonClass l Qbar W false 1 Y) (f : X ⟶ A) (g : A ⟶ Y)
      (h : Y ⟶ X⟦(1 : ℤ)⟧), Pretriangulated.Triangle.mk f g h ∈ distTriang _ := by
  let t := pbcIntegralTStructure W.scheme l (pbcFiniteField.{u} l Qbar A.stage)
  have hQD := ((qbarStagePretriangulated_exists l Qbar W.scheme A.stage).exists.choose_spec
    _).2 ⟨_, t.triangleLEGE_distinguished 0 1 (by simp) A.obj.obj, ⟨Iso.refl _⟩⟩
  have hD := ((StageSystem.commonStage_verdier_existsUnique
    (stages l Qbar W)).exists.choose_spec.1 _).2 ⟨A.stage, _, hQD, ⟨Iso.refl _⟩⟩
  exact ⟨_, _, (commonClass_true_iff l Qbar W 0 _).2 ⟨A.stage, _,
      (rationalLE_iff l _ W 0 _).2 ⟨_, (t.isLE_truncLE_obj _ 0 0 le_rfl).le, ⟨Iso.refl _⟩⟩,
      ⟨Iso.refl _⟩⟩,
    (commonClass_false_iff l Qbar W 1 _).2 ⟨A.stage, _,
      (rationalGE_iff l _ W 1 _).2 ⟨_, (t.isGE_truncGE_obj _ 1 1 le_rfl).ge, ⟨Iso.refl _⟩⟩,
      ⟨Iso.refl _⟩⟩, _, _, _, hD⟩

/-- Every common-stage object is bounded for the common-stage classes. -/
theorem commonClass_exists_bounds (W : Base k) (A : pbcQbarCategory l Qbar W.scheme) :
    (∃ a : ℤ, commonClass l Qbar W false a A) ∧
      ∃ b : ℤ, commonClass l Qbar W true b A := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := rational_exists_bounds l _ W A.obj
  exact ⟨⟨a, (commonClass_false_iff l Qbar W a A).2
      ⟨A.stage, A.obj, ha, ⟨Iso.refl _⟩⟩⟩,
    ⟨b, (commonClass_true_iff l Qbar W b A).2 ⟨A.stage, A.obj, hb, ⟨Iso.refl _⟩⟩⟩⟩

/-- The nonpositive common-stage classes increase. -/
theorem commonClass_true_zero_one (W : Base k) (X : pbcQbarCategory l Qbar W.scheme)
    (hX : commonClass l Qbar W true 0 X) : commonClass l Qbar W true 1 X := by
  obtain ⟨L, M, hM, e⟩ := (commonClass_true_iff l Qbar W 0 X).1 hX
  exact (commonClass_true_iff l Qbar W 1 X).2 ⟨L, M, rationalLE_zero_one l _ W M hM, e⟩

/-- The nonnegative common-stage classes decrease. -/
theorem commonClass_false_one_zero (W : Base k) (X : pbcQbarCategory l Qbar W.scheme)
    (hX : commonClass l Qbar W false 1 X) : commonClass l Qbar W false 0 X := by
  obtain ⟨L, M, hM, e⟩ := (commonClass_false_iff l Qbar W 1 X).1 hX
  exact (commonClass_false_iff l Qbar W 0 X).2 ⟨L, M, rationalGE_one_zero l _ W M hM, e⟩

/-- The t-structure on the common-stage category with the prescribed classes. -/
def commonTStructure (W : Base k) :
    Triangulated.TStructure (pbcQbarCategory l Qbar W.scheme) where
  le := commonClass l Qbar W true
  ge := commonClass l Qbar W false
  le_isClosedUnderIsomorphisms n := ⟨commonClass_of_iso l Qbar W true n⟩
  ge_isClosedUnderIsomorphisms n := ⟨commonClass_of_iso l Qbar W false n⟩
  le_shift := commonClass_true_shift l Qbar W
  ge_shift := commonClass_false_shift l Qbar W
  zero' _ _ := commonClass_hom_eq_zero l Qbar W
  le_zero_le := commonClass_true_zero_one l Qbar W
  ge_one_le := commonClass_false_one_zero l Qbar W
  exists_triangle_zero_one := commonClass_exists_triangle l Qbar W

/-- The common-stage t-structure is bounded. -/
theorem commonTStructure_bounded (W : Base k) : (commonTStructure l Qbar W).bounded = ⊤ := by
  refine le_antisymm le_top fun A _ ↦ ?_
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := commonClass_exists_bounds l Qbar W A
  exact ⟨⟨a, ⟨ha⟩⟩, ⟨b, ⟨hb⟩⟩⟩

/-- The common-stage t-structure is fixed by its two finite-stage image classes. -/
theorem commonT_existsUnique (W : Base k) :
    ∃! t : Triangulated.TStructure (pbcQbarCategory l Qbar W.scheme),
      (∀ n : ℤ, t.le n = commonClass l Qbar W true n ∧
        t.ge n = commonClass l Qbar W false n) ∧ t.bounded = ⊤ := by
  refine ⟨commonTStructure l Qbar W,
    ⟨fun n ↦ ⟨rfl, rfl⟩, commonTStructure_bounded l Qbar W⟩, ?_⟩
  rintro t' ⟨h', -⟩
  exact Triangulated.TStructure.ext_of_le_ge (funext fun n ↦ (h' n).1)
    (funext fun n ↦ (h' n).2)

/-- The bounded common-stage t-structure, determined by its specified classes. -/
@[irreducible]
def commonT (W : Base k) :
    Triangulated.TStructure (pbcQbarCategory l Qbar W.scheme) :=
  (commonT_existsUnique l Qbar W).exists.choose

end AlgebraicGeometry.Scheme.PerAdic

