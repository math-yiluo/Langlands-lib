/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CommonStageWeilShriek
public import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.IntegralPullbackCompletedComparison
public import WeilConjectures.DeligneLaumon.FieldShriekLowerBound
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.PoincareDuality.SemilinearFieldOperationLifts
import WeilConjectures.SmoothPurity.Automorphism.AutomorphismConstructibleStageEquivalence
import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Sf.SfRationalDirectImageAdjunction
import all WeilConjectures.SmoothPurity.Sf.SfIntegralPullbackLinearAdjunction
import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorCoherence
import WeilConjectures.SmoothPurity.IntegralSupportNormalization.IntegralSupportFunctorNormalization
import WeilConjectures.DeligneLaumon.FieldShriekCompositionQcqs
import WeilConjectures.DeligneLaumon.ZlFrobeniusCompactSupportComparison
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Normalized shifts and finite-stage Weil compact support

Source: blueprint main-20261015, lem-zl-composition-weight-bound.proof.md,
first paragraph; lem-fix-weil-operations.proof.md, first two paragraphs;
Stacks Tags 014E, 0941 and 099N(5); SGA 4 XVII, sections 5--6
(blueprint: def-zl-field-weil-shriek-shift-data).

The common-stage proper/open functors and exchanges are reused. Their finite-stage
counterparts are adjoints of the recorded rational pullbacks. Shift comparisons
are fixed by signed Roos reindexing, localization, and adjunction mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived

attribute [-instance] SheafOfModules.cochainModulesMonoidal
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective

private theorem fieldShift_ext
    {C B : Type*} [Category C] [Category B] [HasShift C ℤ] [HasShift B ℤ]
    {F : C ⥤ B} (s t : F.CommShift ℤ)
    (h : ∀ r, s.commShiftIso r = t.commShiftIso r) : s = t := by
  cases s
  cases t
  congr
  funext r
  exact h r

private theorem fieldShift_pred
    {C B : Type*} [Category C] [Category B] [HasShift C ℤ] [HasShift B ℤ]
    {F : C ⥤ B} (s t : F.CommShift ℤ) (n : ℤ)
    (h : s.commShiftIso (n + 1) = t.commShiftIso (n + 1))
    (h1 : s.commShiftIso 1 = t.commShiftIso 1) :
    s.commShiftIso n = t.commShiftIso n := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (shiftFunctor B (1 : ℤ)).map_injective
  have hh := congrArg (fun e ↦ e.hom.app K) h
  rw [s.commShiftIso_add, t.commShiftIso_add] at hh
  simp only [Functor.CommShift.isoAdd_hom_app, h1] at hh
  exact (cancel_mono ((shiftFunctorAdd B n 1).inv.app (F.obj K))).mp
    ((cancel_epi (F.map ((shiftFunctorAdd C n 1).hom.app K) ≫
      (t.commShiftIso 1).hom.app (K⟦n⟧))).mp (by
        simpa only [Category.assoc] using hh))

private theorem fieldShift_ext_one
    {C B : Type*} [Category C] [Category B] [HasShift C ℤ] [HasShift B ℤ]
    {F : C ⥤ B} (s t : F.CommShift ℤ)
    (h : s.commShiftIso 1 = t.commShiftIso 1) : s = t := by
  apply fieldShift_ext
  intro n
  induction n using Int.induction_on with
  | zero => exact s.commShiftIso_zero.trans t.commShiftIso_zero.symm
  | @succ n ih =>
      rw [s.commShiftIso_add, t.commShiftIso_add, ih, h]
  | @pred n ih =>
      apply fieldShift_pred s t (-(n : ℤ) - 1) _ h
      rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by omega]
      exact ih

section PullbackShift
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

section InitialShiftElaboration
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence HasDerivedCategory.standard
  Scheme.residueField

private theorem fieldChainShift_unique
    (c c' : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (hc : IntegralCompletedComparison.ShiftCoordinates l E f c)
    (hc' : IntegralCompletedComparison.ShiftCoordinates l E f c') : c = c' := by
  apply fieldShift_ext
  intro r
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro j
  apply CategoryTheory.SignedCoconeShift.cocone_ext_from
    (IntegralCompletedComparison.roosEnd l E f (P⟦r⟧)) j
  · exact ((hc P r).1 j).trans ((hc' P r).1 j).symm
  · exact ((hc P r).2 (j - 1) j (by omega)).trans
      ((hc' P r).2 (j - 1) j (by omega)).symm

private theorem fieldIntegralShift_unique
    (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (d d' : (integralDerivedPullback l E f).CommShift ℤ)
    (hd : IntegralCompletedComparison.ShiftDescent l E f c d)
    (hd' : IntegralCompletedComparison.ShiftDescent l E f c d') : d = d' := by
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E Y).ι
  let := integralOperationsGoodLocalization_isLocalization l E Y
  apply fieldShift_ext
  intro r
  apply Iso.ext
  apply Localization.natTrans_ext (integralOperationsGoodLocalization l E Y) W
  intro P
  obtain ⟨hP, hp⟩ := hd P r
  obtain ⟨hP', hp'⟩ := hd' P r
  apply (cancel_mono (((integralDerivedPullbackComparison l E f).hom.app P)⟦r⟧')).mp
  exact hp.trans hp'.symm

/-- The integral shift is uniquely fixed by the actual signed Roos coordinates and
its retained comparison on every good representative. Source: Stacks 014E, 0941,
099N(5) (blueprint: def-zl-field-weil-shriek-shift-data).
Proof: the product reindexing and diagonal mapping-cocone map (1,(-1)^r) give
natural coherent chain isomorphisms. Shifted flat-term K-flat complexes remain good.
Descend through the recorded good localization. Its resolving equivalence determines
the descended comparison uniquely from the displayed square. -/
theorem fieldIntegralPullShift_existsUnique :
    ∃! d : (integralDerivedPullback l E f).CommShift ℤ,
      ∃ c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ,
        IntegralCompletedComparison.ShiftCoordinates l E f c ∧
          IntegralCompletedComparison.ShiftDescent l E f c d := by
  let T : Scheme.{u} := ∅
  let : ∀ x : T, Invertible (l : T.residueField x) := fun x ↦ PEmpty.elim x
  obtain ⟨C, _⟩ := automorphismConstructibleStage_comparison_system.{u} l
  obtain ⟨c, d, hc, hd⟩ :=
    (automorphismConstructibleStage_integral_shifts l E C (𝟙 T) (1 : Aut T)
      (1 : Aut T) (by simp)).1 X Y f
  refine ⟨d, ⟨c, hc, hd⟩, ?_⟩
  rintro d' ⟨c', hc', hd'⟩
  have he := fieldChainShift_unique l E f c' c hc' hc
  subst c'
  exact fieldIntegralShift_unique l E f c d' d hd' hd

/-- The representative-normalized integral shift. Source: Stacks 0941, 099N(5)
(blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldIntegralPullShift : (integralDerivedPullback l E f).CommShift ℤ :=
  (fieldIntegralPullShift_existsUnique l E f).exists.choose

end InitialShiftElaboration

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Restrict the ambient shift through the fully faithful constructible inclusion.
Source: Stacks 099N(5) (blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldConstructiblePullShift : (constructibleIntegralPullback l E f).CommShift ℤ :=
  letI : (integralDerivedPullback l E f).CommShift ℤ := fieldIntegralPullShift l E f
  letI : ((sfIntegralConstructible l E Y).ι).CommShift ℤ := inferInstance
  Functor.CommShift.ofComp
    (F := constructibleIntegralPullback l E f) (G := (sfIntegralConstructible l E X).ι)
    (Iso.refl ((sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E f)) ℤ

attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι in
private theorem fieldConstructibleShift_normalization
    (c : (constructibleIntegralPullback l E f).CommShift ℤ)
    (h : automorphismStageIntegralShiftNormalization l E f c) :
    c = fieldConstructiblePullShift l E f := by
  obtain ⟨a, d, ha, hd, hc⟩ := h
  have he : d = fieldIntegralPullShift l E f :=
    (fieldIntegralPullShift_existsUnique l E f).unique ⟨a, ha, hd⟩
      (fieldIntegralPullShift_existsUnique l E f).exists.choose_spec
  subst d
  apply fieldShift_ext
  intro r
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (sfIntegralConstructible l E X).ι.map_injective
  have hK := hc K r
  apply eq_of_heq
  exact hK.trans (by
    dsimp only [fieldConstructiblePullShift, Functor.CommShift.ofComp,
      Functor.commShiftIso]
    erw [Functor.CommShift.OfComp.map_iso_hom_app]
    simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      Functor.commShiftIso_comp_hom_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp,
      CategoryTheory.Functor.map_id, Category.comp_id]
    erw [Category.id_comp]
    rfl)

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence HasDerivedCategory.standard
  Scheme.residueField

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local irreducible] constructibleIntegralPullback integralDerivedPullback
  rationalDerivedPullback commonStageDerivedPullback

/-- Localize the fixed integral shift at one; the CommShift laws determine all integer
shifts. Source: blueprint coefficient passage; Stacks 014E, 099N(5)
(blueprint: def-zl-field-weil-shriek-shift-data).
Proof: tensor the integral comparison with one. The rational shift and localization
comparison at one have precisely these integral objects and identity components.
Naturality on integral arrows extends to tensor Homs. Zero and addition descend,
and every rational object is an integral object, proving uniqueness. -/
theorem fieldRationalPullShift_existsUnique :
    ∃! c : (rationalDerivedPullback l E f).CommShift ℤ,
      ∀ K : sfIntegralConstructibleCategory l E Y,
        HEq ((Functor.commShiftIso (rationalDerivedPullback l E f)
          (self := c) (1 : ℤ)).hom.app ((sfRationalConstructibleLocalization l E Y).obj K))
          ((sfRationalConstructibleLocalization l E X).map
            (((constructibleIntegralPullback l E f).commShiftIso (1 : ℤ)).hom.app K)) := by
  obtain ⟨C, _⟩ := automorphismConstructibleStage_comparison_system.{u} l
  obtain ⟨c, _, _, hc, _⟩ :=
    (automorphismConstructibleStage_descended_shifts l (AlgebraicClosure (Padic l)) C f
      (1 : Aut Y) (1 : Aut X) (by simp)).1 E
  obtain ⟨s, hs, hn⟩ := hc
  have he := fieldConstructibleShift_normalization l E f s hs
  subst s
  refine ⟨c, (fun K ↦ hn.1 ⟨K⟩), ?_⟩
  intro c' hc'
  apply fieldShift_ext_one
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((hc' K.obj).trans (hn.1 K).symm)

/-- The localized canonical pullback shift. Source: blueprint coefficient passage
(blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldRationalPullShift : (rationalDerivedPullback l E f).CommShift ℤ :=
  (fieldRationalPullShift_existsUnique l E f).exists.choose
end PullbackShift

section CommonShift
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X Y : Scheme.{u}} (f : X ⟶ Y)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

omit [IsAlgClosure (Padic l) Ω] in
private theorem fieldRationalShift_normalization
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (c : (rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).CommShift ℤ)
    (h : automorphismStageRationalShiftNormalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f c) :
    c = fieldRationalPullShift l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f := by
  obtain ⟨s, hs, hn⟩ := h
  have he := fieldConstructibleShift_normalization l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f s hs
  subst s
  apply (fieldRationalPullShift_existsUnique l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).unique
  · intro K
    exact hn.1 ⟨K⟩
  · exact (fieldRationalPullShift_existsUnique l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).exists.choose_spec

/-- The common-stage shift is the class of the normalized rational shift at the
object's finite field. Source: blueprint common-stage coefficient passage
(blueprint: def-zl-field-weil-shriek-shift-data).
Proof: scalar comparison maps come from integral tensor maps and commute with signed
reindexing. Thus the rational comparisons agree upon enlargement and descend to every
representative. Every pair lies in its own finite stage, determining the components.
The finite zero and addition equations descend and give uniqueness. -/
theorem fieldCommonPullShift_existsUnique :
    ∃! c : (commonStageDerivedPullback l Ω f).CommShift ℤ,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y L),
        HEq ((Functor.commShiftIso (commonStageDerivedPullback l Ω f)
          (self := c) (1 : ℤ)).hom.app
            ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K))
          ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map
            (((rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).commShiftIso
                (1 : ℤ)).hom.app K)) := by
  obtain ⟨C, _⟩ := automorphismConstructibleStage_comparison_system.{u} l
  obtain ⟨c, _, _, hc, _⟩ :=
    (automorphismConstructibleStage_descended_shifts l Ω C f
      (1 : Aut Y) (1 : Aut X) (by simp)).2
  have hn (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y L) :
      HEq ((Functor.commShiftIso (commonStageDerivedPullback l Ω f)
        (self := c) (1 : ℤ)).hom.app
          ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K))
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map
          (((rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).commShiftIso
              (1 : ℤ)).hom.app K)) := by
    obtain ⟨s, hs, hn⟩ := hc L
    have he := fieldRationalShift_normalization l Ω f L s hs
    subst s
    exact hn K 1
  refine ⟨c, hn, ?_⟩
  intro c' hc'
  apply fieldShift_ext_one
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((hc' K.stage K.obj).trans (hn K.stage K.obj).symm)

/-- The representative-normalized common-stage shift. Source: blueprint coefficient passage
(blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldCommonPullShift : (commonStageDerivedPullback l Ω f).CommShift ℤ :=
  (fieldCommonPullShift_existsUnique l Ω f).exists.choose
end CommonShift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option allowUnsafeReducibility true in
attribute [local semireducible] constructibleIntegralPullback integralDerivedPullback
  rationalDerivedPullback commonStageDerivedPullback

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem fieldRationalPull_eq_lift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [(constructibleIntegralPullback l E f).Additive]
    [(constructibleIntegralPullback l E f).Linear (Padic.coefficientExtensionIntegers l E)] :
    ScalarLocalization.liftLinear (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionUniformizer l E) (constructibleIntegralPullback l E f) =
      rationalDerivedPullback l E f := by
  apply (rationalDerivedPullback_existsUnique l E f).unique _
    (rationalDerivedPullback_existsUnique l E f).exists.choose_spec
  refine ⟨inferInstance, (fun _ ↦ rfl), ?_⟩
  intro K N b c
  exact heq_of_eq (ScalarLocalization.liftLinear_tmul _ _ _ c b)

private instance fieldFiber_finiteType (T : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    LocallyOfFiniteType (D.geometricFiber T).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (pullback.snd T.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

private instance fieldFiber_quasiCompact (T : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    QuasiCompact (D.geometricFiber T).hom :=
  inferInstanceAs (QuasiCompact
    (pullback.snd T.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

private instance fieldFiber_structureFiniteType (T : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    LocallyOfFiniteType ((D.geometricFiber T).left ↘ Spec (.of D.k)) :=
  inferInstanceAs (LocallyOfFiniteType (D.geometricFiber T).hom)

private instance fieldFiber_structureQuasiCompact (T : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    QuasiCompact ((D.geometricFiber T).left ↘ Spec (.of D.k)) :=
  inferInstanceAs (QuasiCompact (D.geometricFiber T).hom)

private instance fieldFiber_rawStructureFiniteType (T : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    LocallyOfFiniteType
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T).left ↘
        Spec (.of D.k)) := fieldFiber_structureFiniteType D T

private instance fieldFiber_rawStructureQuasiCompact (T : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    QuasiCompact
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T).left ↘
        Spec (.of D.k)) := fieldFiber_structureQuasiCompact D T

set_option allowUnsafeReducibility true in
attribute [local reducible] FiniteFieldDatum.geometricFiber zlFiberMap

section FiniteGeometry
variable (k : Type u) [Field k] (hk : IsUnit (l : k))
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

include k hk in
private theorem fieldIntegralPull_linear :
    (constructibleIntegralPullback l E f).Additive ∧
      (constructibleIntegralPullback l E f).Linear (Padic.coefficientExtensionIntegers l E) := by
  obtain ⟨R, ⟨a⟩, hAdd, hLin⟩ := sfIntegralPullbackLinearAdjunction l E k hk f
  let := hAdd
  let := hLin
  exact ⟨CategoryTheory.additiveLeftOfLinearRight a,
    CategoryTheory.linearLeftOfLinearRight _ a⟩

end FiniteGeometry

section OpenGeometry
variable {U X : Over (Spec (.of D.k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]
  [∀ x : U.left, Invertible (l : U.left.residueField x)]
  [∀ x : X.left, Invertible (l : X.left.residueField x)]

local instance : LocallyOfFiniteType (U.left ↘ Spec (.of D.k)) :=
  inferInstanceAs (LocallyOfFiniteType U.hom)
local instance : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) :=
  inferInstanceAs (LocallyOfFiniteType X.hom)
local instance : QuasiCompact (U.left ↘ Spec (.of D.k)) :=
  inferInstanceAs (QuasiCompact U.hom)
local instance : QuasiCompact (X.left ↘ Spec (.of D.k)) :=
  inferInstanceAs (QuasiCompact X.hom)

local instance : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
local instance : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
local instance : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
local instance : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom

private theorem fieldOpenIntegralAdjunction :
    Nonempty (sfCompactSupportFiniteIntegralFunctor l D.k (zlClosurePrimeUnit D l hl)
      (Compactification.ofIsOpenImmersion j.left) E ⊣
        constructibleIntegralPullback l E j.left) := by
  have pb : IsPullback (𝟙 U.left) j.left j.left (𝟙 X.left) := IsPullback.of_id_fst
  let sq : OpenImmersionSquare (𝟙 U.left) j.left j.left (𝟙 X.left) :=
    { w := by simp
      isoPullback := pb.isoPullback
      hom_fst := pb.isoPullback_hom_fst
      hom_snd := pb.isoPullback_hom_snd
      isOpenImmersion := inferInstance
      isOpenImmersion' := inferInstance }
  obtain ⟨o⟩ := OpenFactorCoherence.openFactorCoherence l E D hl U U X X
    (𝟙 U) j j (𝟙 X) sq
  let d := o.openData
  let t := CategoryTheory.Functor.whiskerLeft
    (sfIntegralConstructible l E X.left).ι (d.pull.unit l E)
  let : ∀ K : sfIntegralConstructibleCategory l E X.left, IsIso (t.app K) :=
    fun K ↦ d.pull_unit K.obj K.property.1
  have ht : IsIso t := NatIso.isIso_of_isIso_app t
  let e : (sfIntegralConstructible l E X.left).ι ⋙
      OpenFactorCoherence.star l E j.left ≅
      constructibleIntegralPullback l E j.left ⋙ (sfIntegralConstructible l E U.left).ι :=
    @asIso _ _ _ _ t ht
  let h := (sfQcqsCompactSupportRealization l E D.k (zlClosurePrimeUnit D l hl)
    (Compactification.ofIsOpenImmersion j.left)).symm ≪≫
      CategoryTheory.Functor.isoWhiskerLeft (sfIntegralConstructible l E U.left).ι
        (IntegralSupportNormalization.openIdentity l E j.left)
  exact ⟨(PurCompactSupport.openDerivedAdjunction
    (PurCompactSupport.completed l E) j.left).restrictFullyFaithful
      (sfIntegralConstructible l E U.left).fullyFaithfulι
      (sfIntegralConstructible l E X.left).fullyFaithfulι h.symm e⟩

private theorem fieldOpenRationalAdjunction :
    Nonempty (sfCompactSupportFiniteFunctor l D.k (zlClosurePrimeUnit D l hl)
      (Compactification.ofIsOpenImmersion j.left) E ⊣ rationalDerivedPullback l E j.left) := by
  let hk := zlClosurePrimeUnit D l hl
  have hi := fieldIntegralPull_linear l E D.k hk j.left
  let := hi.1
  let := hi.2
  obtain ⟨a⟩ := fieldOpenIntegralAdjunction D l hl E j
  let : (sfCompactSupportFiniteIntegralFunctor l D.k hk
      (Compactification.ofIsOpenImmersion j.left) E).Additive :=
    CategoryTheory.additiveLeftOfLinearRight a
  let : (sfCompactSupportFiniteIntegralFunctor l D.k hk
      (Compactification.ofIsOpenImmersion j.left) E).Linear
      (Padic.coefficientExtensionIntegers l E) :=
    CategoryTheory.linearLeftOfLinearRight _ a
  have aQ := ScalarLocalization.liftAdjunction (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E)
    (sfCompactSupportFiniteIntegralFunctor l D.k hk
      (Compactification.ofIsOpenImmersion j.left) E) (constructibleIntegralPullback l E j.left) a
  rw [fieldRationalPull_eq_lift l E j.left] at aQ
  exact ⟨aQ⟩
end OpenGeometry

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The rational inverse image along the geometric fibre map. Source: blueprint
lem-fix-weil-operations.proof, first paragraph
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilPull {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :=
  @rationalDerivedPullback l _ E _ _ _ _ _ (zlFiberMap D f₀)
    (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl Y₀)

private theorem fieldTransport_heq {C : Type*} [Category C] {A B A' B' : C}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    eqToHom hA.symm ≫ f ≫ eqToHom hB = g := by
  subst A'
  subst B'
  simpa using eq_of_heq h

private theorem fieldMap_heq {C B : Type*} [Category C] [Category B] (F : C ⥤ B)
    {A A' Z Z' : C} (hA : A = A') (hZ : Z = Z') {f : A ⟶ Z} {g : A' ⟶ Z'}
    (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst A'
  subst Z'
  cases h
  rfl

-- Tensor naturality needs only additivity and the prescribed action, not a chosen
-- integral linearity structure. This also keeps the normalization of the given functors.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem fieldLocalizeIso
    (R : Type*) [CommRing R] (p : R)
    {C B : Type*} [Category C] [Category B] [Preadditive C] [Preadditive B]
    [Linear R C] [Linear R B] (I J : C ⥤ B)
    (F G : ScalarLocalization R C p ⥤ ScalarLocalization R B p)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨I.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨J.obj K.obj⟩)
    (mF : ∀ (K N : C) (a : K ⟶ N) (c : Localization.Away p),
      HEq (F.map (c ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ⟨N⟩))
        (c ⊗ₜ[R] I.map a))
    (mG : ∀ (K N : C) (a : K ⟶ N) (c : Localization.Away p),
      HEq (G.map (c ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ⟨N⟩))
        (c ⊗ₜ[R] J.map a))
    (e : I ≅ J) :
    ∃ c : F ≅ G, ∀ K,
      HEq (c.hom.app K) ((ScalarLocalization.localization R B p).map (e.hom.app K.obj)) := by
  let Q := ScalarLocalization.localization R B p
  let F' := F.copyObj (fun K ↦ Q.obj (I.obj K.obj)) (fun K ↦ eqToIso (hF K))
  let G' := G.copyObj (fun K ↦ Q.obj (J.obj K.obj)) (fun K ↦ eqToIso (hG K))
  have : F'.Additive := Functor.additive_of_iso (F.isoCopyObj _ _)
  have : G'.Additive := Functor.additive_of_iso (G.isoCopyObj _ _)
  have hmF (K N : C) (a : K ⟶ N) (c : Localization.Away p) :
      F'.map (c ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ⟨N⟩) = c ⊗ₜ[R] I.map a :=
    fieldTransport_heq (hF ⟨K⟩) (hF ⟨N⟩) _ _ (mF K N a c)
  have hmG (K N : C) (a : K ⟶ N) (c : Localization.Away p) :
      G'.map (c ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ⟨N⟩) = c ⊗ₜ[R] J.map a :=
    fieldTransport_heq (hG ⟨K⟩) (hG ⟨N⟩) _ _ (mG K N a c)
  let c : F' ≅ G' := NatIso.ofComponents (fun K ↦ Q.mapIso (e.app K.obj)) (by
    intro K N a
    induction a using TensorProduct.inductionOn with
    | tmul c a =>
      rw [hmF K.obj N.obj a c, hmG K.obj N.obj a c]
      change ScalarLocalization.composition _ _ _ _ _ _
          (1 ⊗ₜ (e.hom.app N.obj)) (c ⊗ₜ I.map a) =
        ScalarLocalization.composition _ _ _ _ _ _
          (c ⊗ₜ J.map a) (1 ⊗ₜ (e.hom.app K.obj))
      simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
      exact congrArg (fun b ↦ c ⊗ₜ b) (e.hom.naturality a)
    | add a b ha hb =>
      change F'.map ((a : K ⟶ N) + b) ≫ _ = _
      rw [Functor.map_add, Preadditive.add_comp, Functor.map_add, Preadditive.comp_add]
      exact congrArg₂ (· + ·) ha hb)
  refine ⟨F.isoCopyObj _ _ ≪≫ c ≪≫ (G.isoCopyObj _ _).symm, ?_⟩
  intro K
  change HEq (eqToHom (hF K) ≫ Q.map (e.hom.app K.obj) ≫ eqToHom (hG K).symm) _
  simpa only [Category.assoc] using (comp_eqToHom_heq
    (eqToHom (hF K) ≫ Q.map (e.hom.app K.obj)) (hG K).symm).trans
      (eqToHom_comp_heq (Q.map (e.hom.app K.obj)) (hF K))

/-- Rational composition is the localization of the already normalized integral
composition. Source: Stacks 099N(5), blueprint pullback composition
(blueprint: def-zl-field-weil-shriek-shift-data).
Proof: localize the integral component fixed by integralPullbackComposition.
Naturality extends from integral maps to fractions. The prescribed object action
identifies the endpoints; these components determine the natural isomorphism. -/
theorem fieldRationalPullComp_existsUnique {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! c : rationalDerivedPullback l E (f ≫ g) ≅
        rationalDerivedPullback l E g ⋙ rationalDerivedPullback l E f,
      ∀ K : sfIntegralConstructibleCategory l E Z,
        HEq (c.hom.app ((sfRationalConstructibleLocalization l E Z).obj K))
          ((sfRationalConstructibleLocalization l E X).map
            (((integralPullbackComposition l E).choose f g).hom.app K)) := by
  let F := rationalDerivedPullback l E f
  let G := rationalDerivedPullback l E g
  let H := rationalDerivedPullback l E (f ≫ g)
  let I := constructibleIntegralPullback l E f
  let J := constructibleIntegralPullback l E g
  let Q := sfRationalConstructibleLocalization l E X
  have hf := (rationalDerivedPullback_existsUnique l E f).exists.choose_spec
  have hg := (rationalDerivedPullback_existsUnique l E g).exists.choose_spec
  have hh := (rationalDerivedPullback_existsUnique l E (f ≫ g)).exists.choose_spec
  have : F.Additive := hf.1
  have : G.Additive := hg.1
  have : H.Additive := hh.1
  have hobj (K : sfRationalConstructibleCategory l E Z) :
      (G ⋙ F).obj K = Q.obj ((J ⋙ I).obj K.obj) :=
    (hf.2.1 (G.obj K)).trans
      (congrArg (fun N : sfRationalConstructibleCategory l E Y ↦ Q.obj (I.obj N.obj)) (hg.2.1 K))
  have hmap (K N : sfIntegralConstructibleCategory l E Z) (a : K ⟶ N)
      (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      HEq ((G ⋙ F).map (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a :
        (sfRationalConstructibleLocalization l E Z).obj K ⟶
          (sfRationalConstructibleLocalization l E Z).obj N))
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] (J ⋙ I).map a) :=
    (fieldMap_heq F (hg.2.1 ⟨K⟩) (hg.2.1 ⟨N⟩) (hg.2.2 K N a c)).trans
      (hf.2.2 (J.obj K) (J.obj N) (J.map a) c)
  obtain ⟨c, hc⟩ := fieldLocalizeIso (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E)
    (constructibleIntegralPullback l E (f ≫ g)) (J ⋙ I) H (G ⋙ F)
    hh.2.1 hobj hh.2.2 hmap ((integralPullbackComposition l E).choose f g)
  refine ⟨c, (fun K ↦ hc ⟨K⟩), ?_⟩
  intro c' hc'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((hc' K.obj).trans (hc K).symm)

/-- The fixed rational pullback composition. Source: Stacks 099N(5)
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldRationalPullComp {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (fieldRationalPullComp_existsUnique l E f g).exists.choose

section Finite

attribute [local irreducible] constructibleIntegralPullback integralDerivedPullback
  rationalDerivedPullback commonStageDerivedPullback

variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The finite-stage Frobenius square uses the normalized composition and the actual
semilinear geometric-Frobenius naturality equality. Source: blueprint
lem-fix-weil-operations.proof, first paragraph
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilPullSquare (f₀ : X₀ ⟶ Y₀) :
    fieldWeilPull D l hl E f₀ ⋙ sfWeilFrobeniusPullback D l hl X₀ E ≅
      sfWeilFrobeniusPullback D l hl Y₀ E ⋙ fieldWeilPull D l hl E f₀ :=
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Y₀
  (fieldRationalPullComp l E (D.geometricFrobenius X₀).asIso.hom (zlFiberMap D f₀)).symm ≪≫
    eqToIso (congrArg (fun f ↦ rationalDerivedPullback l E f)
      (zlFrobenius_naturality D f₀)) ≪≫
    fieldRationalPullComp l E (zlFiberMap D f₀) (D.geometricFrobenius Y₀).asIso.hom

/-- Proper rational pullback has its constructible right adjoint, and open rational
pullback has its extension-by-zero left adjoint. Source: SGA 4 XVII, sections 5--6
(blueprint: def-zl-field-weil-shriek-shift-data).
Proof: the finite proper/open adjunctions preserve bounded constructibility. Their
coherent complete towers restrict the adjunctions to integral constructible objects.
Localizing the linear Hom bijections gives the asserted rational adjunctions. -/
theorem fieldWeilPull_adjoints (f₀ : X₀ ⟶ Y₀) :
    (IsProper f₀.left → (fieldWeilPull D l hl E f₀).IsLeftAdjoint) ∧
      (IsOpenImmersion f₀.left → (fieldWeilPull D l hl E f₀).IsRightAdjoint) := by
  let := sfWeilPrimeInvertible D l hl X₀
  let := sfWeilPrimeInvertible D l hl Y₀
  constructor
  · intro hp
    let := hp
    exact rationalSystemPullback_isLeftAdjoint l E D.k (zlClosurePrimeUnit D l hl)
      (zlFiberMap D f₀)
  · intro hj
    let := hj
    have : IsOpenImmersion (zlFiberMap D f₀) :=
      MorphismProperty.overPullbackMap (P := fun {A B : Scheme.{u}} (f : A ⟶ B) ↦ IsOpenImmersion f)
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ hj
    have : LocallyOfFiniteType (D.geometricFiber X₀).hom :=
      inferInstanceAs (LocallyOfFiniteType
        (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    have : QuasiCompact (D.geometricFiber X₀).hom :=
      inferInstanceAs (QuasiCompact
        (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    have : LocallyOfFiniteType (D.geometricFiber Y₀).hom :=
      inferInstanceAs (LocallyOfFiniteType
        (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    have : QuasiCompact (D.geometricFiber Y₀).hom :=
      inferInstanceAs (QuasiCompact
        (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    let : IsOpenImmersion
        (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left) :=
      inferInstanceAs (IsOpenImmersion (zlFiberMap D f₀))
    obtain ⟨a⟩ := fieldOpenRationalAdjunction D l hl E
      (U := D.geometricFiber X₀) (X := D.geometricFiber Y₀)
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀)
    exact ⟨_, ⟨a⟩⟩

/-- The adjunction-determined proper image. Source: SGA 4 XVII, section 5
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilProper (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left] :=
  letI := (fieldWeilPull_adjoints D l hl E p₀).1 inferInstance
  (fieldWeilPull D l hl E p₀).rightAdjoint

/-- The actual proper adjunction. Source: SGA 4 XVII, section 5
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilProperAdj (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left] :
    fieldWeilPull D l hl E p₀ ⊣ fieldWeilProper D l hl E p₀ :=
  letI := (fieldWeilPull_adjoints D l hl E p₀).1 inferInstance
  Adjunction.ofIsLeftAdjoint _

/-- The adjunction-determined open extension. Source: SGA 4 XVII, section 5
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilOpen (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] :=
  letI := (fieldWeilPull_adjoints D l hl E j₀).2 inferInstance
  (fieldWeilPull D l hl E j₀).leftAdjoint

/-- The actual open adjunction. Source: SGA 4 XVII, section 5
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilOpenAdj (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] :
    fieldWeilOpen D l hl E j₀ ⊣ fieldWeilPull D l hl E j₀ :=
  letI := (fieldWeilPull_adjoints D l hl E j₀).2 inferInstance
  Adjunction.ofIsRightAdjoint _

/-- The proper exchange is the right mate of inverse-image exchange.
Source: blueprint lem-fix-weil-operations.proof, first paragraph
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilProperExchangeMap (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left] :=
  (mateEquiv (fieldWeilProperAdj D l hl E p₀) (fieldWeilProperAdj D l hl E p₀)
    (TwoSquare.mk _ _ _ _ (fieldWeilPullSquare D l hl E p₀).inv))

/-- The inverse open exchange is the left mate of inverse-image exchange.
Source: blueprint lem-fix-weil-operations.proof, first paragraph
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilOpenExchangeInverseMap (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] :=
  ((mateEquiv (fieldWeilOpenAdj D l hl E j₀) (fieldWeilOpenAdj D l hl E j₀)).symm
    (TwoSquare.mk _ _ _ _ (fieldWeilPullSquare D l hl E j₀).hom))

-- The finite Frobenius equivalence is already part of the recorded semilinear transport.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem fieldFrobenius_isEquivalence
    (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    (sfWeilFrobeniusPullback D l hl T₀ E).IsEquivalence := by
  have h := (semilinearFieldOperationLifts D l hl T₀ T₀ (𝟙 T₀) E
    (AlgebraicClosure (Padic l))).2.2.1.1
  rcases h with ⟨_, _, _, _, _, _, _, h, _⟩
  exact h

-- Dualize the right-mate lemma to preserve the specified inverse open exchange.
private theorem fieldInverseMate_isIso
    {A B C F : Type*} [Category A] [Category B] [Category C] [Category F]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ F} {R' : F ⥤ C}
    {G : A ⥤ C} {H : B ⥤ F} [G.IsEquivalence] [H.IsEquivalence]
    (a : L ⊣ R) (b : L' ⊣ R') (β : R ⋙ G ≅ H ⋙ R') :
    IsIso (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β.hom))) := by
  let α := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β.hom))
  let βop : TwoSquare H.op R.op R'.op G.op :=
    TwoSquare.mk _ _ _ _ (NatTrans.op β.hom)
  have hi := isIso_mateEquiv_of_isEquivalence a.op b.op βop
  have he : NatTrans.op α = (mateEquiv a.op b.op βop) := by
    ext X
    simp [α, βop, mateEquiv]
  have : IsIso (NatTrans.op α) := by rw [he]; exact hi
  have (X : A) : IsIso (α.app X) := by
    have : IsIso ((α.app X).op) :=
      NatIso.isIso_app_of_isIso (NatTrans.op α) (Opposite.op X)
    exact isIso_of_op (α.app X)
  exact NatIso.isIso_of_isIso_app α

/-- The specified proper and open mates are isomorphisms.
Source: blueprint lem-fix-weil-operations.proof, inverse automorphism square
(blueprint: def-zl-field-weil-shriek-shift-data).
Proof: form the same mates for the inverse geometric-Frobenius square. Pullback
composition coherence and mate pasting identify both composites with identities.
This proves invertibility of these particular maps. -/
theorem fieldWeilExchange_isIso :
    (∀ (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left],
      IsIso (fieldWeilProperExchangeMap D l hl E p₀)) ∧
    (∀ (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left],
      IsIso (fieldWeilOpenExchangeInverseMap D l hl E j₀)) := by
  have := fieldFrobenius_isEquivalence D l hl E X₀
  have := fieldFrobenius_isEquivalence D l hl E Y₀
  constructor
  · intro p₀ hp
    exact isIso_mateEquiv_of_isEquivalence
      (fieldWeilProperAdj D l hl E p₀) (fieldWeilProperAdj D l hl E p₀)
      (TwoSquare.mk _ _ _ _ (fieldWeilPullSquare D l hl E p₀).inv)
  · intro j₀ hj
    exact fieldInverseMate_isIso (fieldWeilOpenAdj D l hl E j₀)
      (fieldWeilOpenAdj D l hl E j₀) (fieldWeilPullSquare D l hl E j₀)

/-- Proper exchange, with its prescribed forward mate.
Source: blueprint lem-fix-weil-operations.proof
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilProperExchange (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left] :=
  @asIso _ _ _ _ (fieldWeilProperExchangeMap D l hl E p₀)
    ((fieldWeilExchange_isIso D l hl E).1 p₀)

/-- Open exchange, inverse to its prescribed left mate.
Source: blueprint lem-fix-weil-operations.proof
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilOpenExchange (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] :=
  (@asIso _ _ _ _ (fieldWeilOpenExchangeInverseMap D l hl E j₀)
    ((fieldWeilExchange_isIso D l hl E).2 j₀)).symm

/-- Finite-stage compact support, first open extension, then proper image.
Source: SGA 4 XVII, sections 5--6 (blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilShriek (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :=
  letI : IsProper (zlCompactificationProper D f₀ c).left := inferInstanceAs (IsProper c.g)
  fieldWeilOpen D l hl E (zlCompactificationOpen D f₀ c) ⋙
    fieldWeilProper D l hl E (zlCompactificationProper D f₀ c)

/-- Compact-support exchange is the proper exchange followed by the open exchange.
Source: blueprint lem-fix-weil-operations.proof, compact-support paragraph
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilShriekExchange (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    fieldWeilShriek D l hl E f₀ c ⋙ sfWeilFrobeniusPullback D l hl Y₀ E ≅
      sfWeilFrobeniusPullback D l hl X₀ E ⋙ fieldWeilShriek D l hl E f₀ c :=
  letI : IsProper (zlCompactificationProper D f₀ c).left := inferInstanceAs (IsProper c.g)
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (fieldWeilProperExchange D l hl E (zlCompactificationProper D f₀ c)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (fieldWeilOpenExchange D l hl E (zlCompactificationOpen D f₀ c)) _ ≪≫
    Functor.associator _ _ _

set_option allowUnsafeReducibility true in
attribute [local semireducible] FiniteFieldDatum.geometricFiber zlFiberMap

end Finite

set_option allowUnsafeReducibility true in
attribute [local semireducible] FiniteFieldDatum.geometricFiber zlFiberMap

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The canonical finite-stage Frobenius shift. Source: Stacks 099N(5), blueprint
geometric Frobenius (blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldWeilFrobeniusShift (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (sfWeilFrobeniusPullback D l hl X₀ E).CommShift ℤ :=
  @fieldRationalPullShift l _ E _ _ _ _ _ (D.geometricFrobenius X₀).asIso.hom
    (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀)

/-- The canonical common-stage Frobenius shift. Source: blueprint geometric Frobenius
(blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldCommonWeilFrobeniusShift (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).CommShift ℤ :=
  @fieldCommonPullShift l _ Ω _ _ _ _ _ (D.geometricFrobenius X₀).asIso.hom
    (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀)

end WeilConjectures
