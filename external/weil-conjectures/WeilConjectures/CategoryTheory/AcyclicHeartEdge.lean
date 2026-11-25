/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TruncationHypercohomology
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Single
import WeilConjectures.Algebra.Homology.UpperTruncationStepSES
import WeilConjectures.CategoryTheory.TruncationRawExact
import WeilConjectures.CategoryTheory.TruncationQuadrantVanishing
import WeilConjectures.CategoryTheory.TruncationAbutmentCocone
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.CategoryTheory.TruncationTriangle

/-! # The canonical edge for acyclic cohomology objects

Source: Stacks Project, sites-cohomology.tex, Tag 0D7U, lemma-equivalence-bounded;
the truncation spectral sequence of Tags 0D7S/0D7T.
(blueprint: lem-fd-acyclic-heart-edge).

The normalization below specifies the edge by its composite with the canonical
truncation inclusion. Under column collapse this is precisely the quotient to
the zeroth graded piece followed by the canonical abutment identification Theta.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B]

omit [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B] in
private theorem column_page_zero (X : BigradedExactCouple B 0)
    (hE : ∀ p q : ℤ, p ≠ 0 → IsZero (X.E p q))
    (r : ℕ) (p q : ℤ) (hp : p ≠ 0) : IsZero ((X.pageCouple r).E p q) := by
  induction r with
  | zero => exact hE p q hp
  | succ r ih =>
    have : Epi ((X.pageCouple r).derivedEProjection p q) := by
      dsimp [BigradedExactCouple.derivedEProjection, BigradedExactCouple.derivedE]
      infer_instance
    exact IsZero.of_epi ((X.pageCouple r).derivedEProjection p q)
      (IsZero.of_mono (kernel.ι ((X.pageCouple r).d p q)) ih)

omit [HasDerivedCategory.{w₂} B] in
private theorem pullback_bot_eq_kernel {T U : B} (f : T ⟶ U) :
    (Subobject.pullback f).obj ⊥ = kernelSubobject f := by
  apply le_antisymm
  · apply Subobject.le_of_factors
    apply kernelSubobject_factors
    have hw := (Subobject.isPullback f (⊥ : Subobject U)).w
    simpa using hw.symm
  · apply Subobject.le_of_factors
    apply pullback_factors
    rw [kernelSubobject_arrow_comp]
    exact Subobject.factors_zero

omit [HasDerivedCategory.{w₂} B] in
private theorem column_tower (X : BigradedExactCouple B 0)
    (hE : ∀ p q : ℤ, p ≠ 0 → IsZero (X.E p q)) (r : ℕ) (q : ℤ) :
    X.cycleBoundaryTower.Z r 0 q = ⊤ ∧ X.cycleBoundaryTower.B r 0 q = ⊥ := by
  have hs (t : ℕ) :
      X.cycleBoundaryTower.Z (t + 1) 0 q = X.cycleBoundaryTower.Z t 0 q ∧
      X.cycleBoundaryTower.B (t + 1) 0 q = X.cycleBoundaryTower.B t 0 q := by
    have hout : (X.pageCouple t).d 0 q = 0 :=
      (column_page_zero X hE t (0 + 2 + t) (q - 1 - t) (by omega)).eq_zero_of_tgt _
    have hin : (X.pageCouple t).dInto 0 q = 0 :=
      (column_page_zero X hE t (0 - t - 2) (q + t + 1) (by omega)).eq_zero_of_src _
    constructor
    · rw [X.cycleBoundaryTower.Z_succ, hout, kernelSubobject_zero,
        Subobject.pullback_top, Subobject.exists_iso_map, Subobject.map_top,
        Subobject.mk_arrow]
    · rw [X.cycleBoundaryTower.B_succ, hin, imageSubobject_zero,
        pullback_bot_eq_kernel, X.cycleBoundaryTower.projection_kernel,
        Subobject.exists_iso_map, Subobject.map_mk]
      simp only [Subobject.ofLE_arrow, Subobject.mk_arrow]
  induction r with
  | zero => exact ⟨X.cycleBoundaryTower.Z_zero 0 q, X.cycleBoundaryTower.B_zero 0 q⟩
  | succ r ih => exact ⟨(hs r).1.trans ih.1, (hs r).2.trans ih.2⟩

omit [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B] in
-- Finite induction in the truncation index replaces the filtration descent.
private theorem positive_D_zero (X : BigradedExactCouple B 0) (a : ℤ)
    (hD : ∀ p q : ℤ, q < a → IsZero (X.D p q))
    (hE : ∀ p q : ℤ, p ≠ 0 → IsZero (X.E p q)) :
    ∀ p q : ℤ, 0 < p → IsZero (X.D p q) := by
  have step (p q : ℤ) (hp : 1 < p) (hz : IsZero (X.D p q)) :
      IsZero (X.D (p - 1) (q + 1)) := by
    let S := ShortComplex.mk (X.alpha p q) (X.g (p - 1) (q + 1))
      (X.g_alpha_zero p q)
    have he : S.Exact := (ShortComplex.exact_iff_image_eq_kernel S).2 (X.exact_g p q)
    exact he.isZero_X₂ (hz.eq_zero_of_src _)
      (by
        have hz : IsZero (X.E ((p - 1) + (0 : ℕ)) ((q + 1) - (0 : ℕ))) := by
          simpa using hE (p - 1) (q + 1) (by omega)
        exact hz.eq_zero_of_tgt _)
  have h (t : ℕ) : ∀ p q : ℤ, q < a + t → 0 < p → IsZero (X.D p q) := by
    intro p q hq hp
    induction t generalizing p q with
    | zero => exact hD p q (by omega)
    | succ t ih =>
      simpa only [add_sub_cancel_right, sub_add_cancel] using
        step (p + 1) (q - 1) (by omega) (ih (p + 1) (q - 1) (by omega) (by omega))
  intro p q hp
  exact h (q - a + 1).toNat p q (by omega) hp

private noncomputable def rawCouple (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) : BigradedExactCouple B 0 := by
  let h := truncation_raw_exact F K
  exact
    { D := TruncationCouple.D F K
      E := TruncationCouple.E F K
      alpha := TruncationCouple.alpha F K
      f := TruncationCouple.f F K
      g := fun p q ↦ TruncationCouple.g F K p q ≫ eqToHom (by simp)
      alpha_f_zero := fun p q ↦ (h.1 p q).choose
      f_g_zero := fun p q ↦ (h.2.1 p q).choose
      g_alpha_zero := fun p q ↦ (h.2.2 p q).choose
      exact_alpha := fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp
        (h.1 p q).choose_spec
      exact_f := fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp
        (h.2.1 p q).choose_spec
      exact_g := fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp
        (h.2.2 p q).choose_spec }

private theorem initial_column_zero (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A)
    (hK : ∀ (j : ℤ) (p : ℕ), 0 < p →
      IsZero ((F.rightDerived p).obj (K.obj.homology j))) :
    ∀ p q : ℤ, p ≠ 0 → IsZero (TruncationCouple.E F K p q) := by
  obtain ⟨a, ha⟩ := K.property
  have hbound (q : ℤ) (hq : q < a) : IsZero (K.obj.homology q) := by
    have := ha
    exact (K.obj.exactAt_of_isGE a q hq).isZero_homology
  obtain ⟨hneg, _, _⟩ := truncation_quadrant_vanishing F K a hbound
  intro p q hp
  by_cases h : p < 0
  · exact hneg p q h
  · let e := (DerivedCategory.homologyFunctor B (p + q)).mapIso
        (F.rightDerivedFunctor.mapIso
          (((DerivedCategory.singleFunctors A).shiftIso (-q) q 0
            (by omega)).app (K.obj.homology q)).symm) ≪≫
      (DerivedCategory.homologyFunctor B (p + q)).mapIso
        ((F.rightDerivedFunctor.commShiftIso (-q)).app
          ((DerivedCategory.singleFunctor A 0).obj (K.obj.homology q))) ≪≫
      ((DerivedCategory.homologyFunctor B 0).shiftIso (-q) (p + q) p.toNat
        (by omega)).app
          (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor A 0).obj
            (K.obj.homology q))) ≪≫
      F.homologyRightDerivedFunctorObjSingleFunctorIso (K.obj.homology q) p.toNat
    exact ((hK q p.toNat (by omega)).of_iso e).of_iso
      (TruncationCouple.bridgeIso F (TruncationCouple.cohomologyComplex K q) (p + q)).symm

private theorem raw_positive_zero (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A)
    (hK : ∀ (j : ℤ) (p : ℕ), 0 < p →
      IsZero ((F.rightDerived p).obj (K.obj.homology j))) :
    ∀ p q : ℤ, 0 < p → IsZero (TruncationCouple.D F K p q) := by
  obtain ⟨a, ha⟩ := K.property
  have hbound (q : ℤ) (hq : q < a) : IsZero (K.obj.homology q) := by
    have := ha
    exact (K.obj.exactAt_of_isGE a q hq).isZero_homology
  exact positive_D_zero (rawCouple F K) a
    (truncation_quadrant_vanishing F K a hbound).2.1 (initial_column_zero F K hK)

private theorem inclusion_isIso (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor B n).map
      (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE n)))) := by
  obtain ⟨H, hH, j, c, hj, hc, hiso, _⟩ :=
    truncation_abutment_cocone F K (rawCouple F K) rfl
      (by intro p q; simp [rawCouple])
  subst H
  have hi := hiso n
  rw [hc, hj] at hi
  have hi' : IsIso
      ((TruncationCouple.bridgeIso F (TruncationCouple.truncation K n) n).inv ≫
        (DerivedCategory.homologyFunctor B n).map
          (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE n)))) := by
    simpa [rawCouple, TruncationCouple.D] using hi
  have := hi'
  exact IsIso.of_isIso_comp_left
    (TruncationCouple.bridgeIso F (TruncationCouple.truncation K n) n).inv _

private theorem raw_g_isIso (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A)
    (hK : ∀ (j : ℤ) (p : ℕ), 0 < p →
      IsZero ((F.rightDerived p).obj (K.obj.homology j))) (q : ℤ) :
    IsIso (TruncationCouple.g F K 0 q) := by
  obtain ⟨_, hf, hg⟩ := truncation_raw_exact F K
  have hz := raw_positive_zero F K hK
  have hmono : Mono (TruncationCouple.g F K 0 q) := by
    have he := (hg 1 (q - 1)).choose_spec
    have hm := he.mono_g ((hz 1 (q - 1) (by omega)).eq_zero_of_src _)
    dsimp only at hm
    have := hm
    let z : TruncationCouple.E F K (1 - 1) ((q - 1) + 1) =
        TruncationCouple.E F K ((1 - 1) + (0 : ℕ)) (((q - 1) + 1) - (0 : ℕ)) := by
      simp
    have hm' := mono_of_mono
      (TruncationCouple.g F K (1 - 1) ((q - 1) + 1)) (eqToHom z)
    exact (show (1 : ℤ) - 1 = 0 by omega) ▸
      (show q - 1 + 1 = q by omega) ▸ hm'
  have hepi : Epi (TruncationCouple.g F K 0 q) := by
    have he := (hf 0 q).choose_spec.epi_f
      ((hz (0 + (0 : ℕ) + 2) (q - (0 : ℕ) - 1) (by omega)).eq_zero_of_tgt _)
    dsimp only at he
    let z : TruncationCouple.E F K 0 q =
        TruncationCouple.E F K (0 + (0 : ℕ)) (q - (0 : ℕ)) := by simp
    exact (epi_comp_iff_of_isIso (TruncationCouple.g F K 0 q) (eqToHom z)).mp he
  have := hmono
  have := hepi
  exact isIso_of_mono_of_epi _

omit [IsGrothendieckAbelian.{v₂} B] in
private theorem raw_g_iso_iff (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (p q n : ℤ) (hn : p + q = n) :
    IsIso (TruncationCouple.g F K p q) ↔
      IsIso ((TruncationCouple.bridgeIso F (TruncationCouple.truncation K q) n).inv ≫
        (DerivedCategory.homologyFunctor B n).map
          (F.rightDerivedFunctor.map (DerivedCategory.Q.map
            (TruncationCouple.projection K q))) ≫
        (TruncationCouple.bridgeIso F (TruncationCouple.cohomologyComplex K q) n).hom) := by
  subst n
  rfl

private theorem projection_isIso (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A)
    (hK : ∀ (j : ℤ) (p : ℕ), 0 < p →
      IsZero ((F.rightDerived p).obj (K.obj.homology j))) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor B q).map
      (F.rightDerivedFunctor.map (DerivedCategory.Q.map (TruncationCouple.projection K q)))) := by
  have hg := raw_g_isIso F K hK q
  have hg' : IsIso
      ((TruncationCouple.bridgeIso F (TruncationCouple.truncation K q) q).inv ≫
        (DerivedCategory.homologyFunctor B q).map
          (F.rightDerivedFunctor.map (DerivedCategory.Q.map
            (TruncationCouple.projection K q))) ≫
        (TruncationCouple.bridgeIso F (TruncationCouple.cohomologyComplex K q) q).hom) := by
    exact (raw_g_iso_iff F K 0 q q (by omega)).mp hg
  have := hg'
  have : IsIso
      ((DerivedCategory.homologyFunctor B q).map
          (F.rightDerivedFunctor.map (DerivedCategory.Q.map
            (TruncationCouple.projection K q))) ≫
        (TruncationCouple.bridgeIso F (TruncationCouple.cohomologyComplex K q) q).hom) :=
    IsIso.of_isIso_comp_left
      (TruncationCouple.bridgeIso F (TruncationCouple.truncation K q) q).inv _
  exact IsIso.of_isIso_comp_right _
    (TruncationCouple.bridgeIso F (TruncationCouple.cohomologyComplex K q) q).hom

private theorem filtration_images (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A)
    (hK : ∀ (j : ℤ) (p : ℕ), 0 < p →
      IsZero ((F.rightDerived p).obj (K.obj.homology j))) (n : ℤ) :
    imageSubobject ((DerivedCategory.homologyFunctor B n).map
      (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE n)))) = ⊤ ∧
    imageSubobject ((DerivedCategory.homologyFunctor B n).map
      (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE (n - 1))))) = ⊥ := by
  constructor
  · have := inclusion_isIso F K n
    rw [imageSubobject_mono, Subobject.mk_eq_top_of_isIso]
  · have hz : IsZero (F.rightDerivedCohomologyWithResolution
        (TruncationCouple.truncation K (n - 1))
        (CochainComplex.grothendieckKInjectiveResolutionChoice
          (TruncationCouple.truncation K (n - 1)).obj) n) := by
      simpa [TruncationCouple.D] using raw_positive_zero F K hK 1 (n - 1) (by omega)
    have hz' : IsZero ((DerivedCategory.homologyFunctor B n).obj
        (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj (K.obj.truncLE (n - 1))))) := by
      exact hz.of_iso
        (TruncationCouple.bridgeIso F (TruncationCouple.truncation K (n - 1)) n)
    have hm : (DerivedCategory.homologyFunctor B n).map
        (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE (n - 1)))) = 0 :=
      hz'.eq_zero_of_src _
    rw [hm, imageSubobject_zero]

private noncomputable def singleComparison (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (q : ℤ) :
    DerivedCategory.singleFunctor A q ⋙ F.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor B q ≅ F :=
  let e₁ := Functor.isoWhiskerRight
    (((DerivedCategory.singleFunctors A).shiftIso (-q) q 0 (by omega)).symm)
    (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q)
  let e₂ := Functor.isoWhiskerLeft (DerivedCategory.singleFunctor A 0)
    (Functor.isoWhiskerRight (F.rightDerivedFunctor.commShiftIso (-q))
      (DerivedCategory.homologyFunctor B q))
  let e₃ := Functor.isoWhiskerLeft
    (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor)
    ((DerivedCategory.homologyFunctor B 0).shiftIso (-q) q 0 (by omega))
  e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ F.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso

omit [IsGrothendieckAbelian.{v₂} B] in
omit [IsGrothendieckAbelian.{v₂} B] in
omit [IsGrothendieckAbelian.{v₁} A] in
private theorem bounded_representative (L : DerivedCategory.Plus A) :
    ∃ K : CochainComplex.Plus A, Nonempty (DerivedCategory.Q.obj K.obj ≅ L.obj) := by
  obtain ⟨a, ha⟩ := L.property
  have := ha
  obtain ⟨K, hK, ⟨e⟩⟩ := L.obj.exists_iso_Q_obj_of_isGE a
  exact ⟨⟨K, ⟨a, hK⟩⟩, ⟨e.symm⟩⟩

omit [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B] in
private theorem representative_acyclic (F : A ⥤ B) [F.Additive]
    (L : DerivedCategory.Plus A)
    (h : ∀ (j : ℤ) (p : ℕ), 0 < p →
      IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj L.obj)))
    (K : CochainComplex.Plus A) (e : DerivedCategory.Q.obj K.obj ≅ L.obj) :
    ∀ (j : ℤ) (p : ℕ), 0 < p → IsZero ((F.rightDerived p).obj (K.obj.homology j)) := by
  intro j p hp
  exact (h j p hp).of_iso ((F.rightDerived p).mapIso
    (((DerivedCategory.homologyFunctorFactors A j).app K.obj).symm ≪≫
      (DerivedCategory.homologyFunctor A j).mapIso e))

set_option linter.unusedVariables false in

/-- The degree-zero second-page identification, with an object placed in degree q.
This is exactly the shift and ordinary-derived comparison in
lemma-uniform-bound-proper-direct-image--1, followed by the inverse of the degree-zero augmentation.
Source: Stacks Tags 05TD and 0D7U (blueprint: lem-fd-acyclic-heart-edge). -/
noncomputable def acyclicHeartSingleIso (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (X : A) (q : ℤ) :
    (DerivedCategory.homologyFunctor B q).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor A q).obj X)) ≅ F.obj X :=
  (DerivedCategory.homologyFunctor B q).mapIso
      (F.rightDerivedFunctor.mapIso
        (((DerivedCategory.singleFunctors A).shiftIso (-q) q 0 (by omega)).app X).symm) ≪≫
    (DerivedCategory.homologyFunctor B q).mapIso
      ((F.rightDerivedFunctor.commShiftIso (-q)).app
        ((DerivedCategory.singleFunctor A 0).obj X)) ≪≫
    ((DerivedCategory.homologyFunctor B 0).shiftIso (-q) q 0 (by omega)).app
      (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor A 0).obj X)) ≪≫
    F.homologyRightDerivedFunctorObjSingleFunctorIso X 0 ≪≫ F.rightDerivedZeroIsoSelf.app X

/-- The type of edge families on bounded-below objects with F-acyclic cohomology.
The proof argument records precisely the positive-degree acyclicity assumption.
Source: Stacks Tag 0D7U (blueprint: lem-fd-acyclic-heart-edge). -/
def AcyclicHeartEdgeFamily (F : A ⥤ B) [F.Additive] :=
  ∀ (L : DerivedCategory.Plus A),
    (∀ (j : ℤ) (p : ℕ), 0 < p →
      IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj L.obj))) →
    ∀ q : ℤ, (DerivedCategory.homologyFunctor B q).obj
        (F.rightDerivedFunctor.obj L.obj) ⟶
      F.obj ((DerivedCategory.homologyFunctor A q).obj L.obj)

/-- Normalize an edge on every bounded-below representative and every representing
isomorphism. The left side precomposes with c_q, the derived truncation inclusion.
The right side is the map g of the truncation couple, with its bridge isomorphisms
cancelled, followed by the second-page degree-zero comparison. Thus this condition
specifies the quotient/Theta edge, rather than an unspecified isomorphism.
Source: Stacks Tag 0D7U and lemma-uniform-bound-proper-direct-image--1, part 6
(blueprint: lem-fd-acyclic-heart-edge). -/
def IsAcyclicHeartEdge (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (edge : F.AcyclicHeartEdgeFamily) : Prop :=
  ∀ (L : DerivedCategory.Plus A)
    (h : ∀ (j : ℤ) (p : ℕ), 0 < p →
      IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj L.obj)))
    (K : CochainComplex.Plus A) (e : DerivedCategory.Q.obj K.obj ≅ L.obj) (q : ℤ),
    (DerivedCategory.homologyFunctor B q).map
        (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE q))) ≫
      (DerivedCategory.homologyFunctor B q).map (F.rightDerivedFunctor.map e.hom) ≫
      edge L h q =
    (DerivedCategory.homologyFunctor B q).map
        (F.rightDerivedFunctor.map (DerivedCategory.Q.map (TruncationCouple.projection K q))) ≫
      (F.acyclicHeartSingleIso (K.obj.homology q) q).hom ≫
      F.map (((DerivedCategory.homologyFunctorFactors A q).app K.obj).inv ≫
        (DerivedCategory.homologyFunctor A q).map e.hom)

omit [IsGrothendieckAbelian.{v₂} B] in
/-- The single-object comparison has the components of `acyclicHeartSingleIso`. -/
private theorem singleComparison_hom_app (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (q : ℤ) (X : A) :
    (singleComparison F q).hom.app X = (F.acyclicHeartSingleIso X q).hom := by
  simp [singleComparison, acyclicHeartSingleIso,
    singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso]

omit [IsGrothendieckAbelian.{v₂} B] in
/-- Naturality of `acyclicHeartSingleIso` in the object. -/
@[reassoc]
private theorem acyclicHeartSingleIso_hom_naturality (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (q : ℤ) {X Y : A} (φ : X ⟶ Y) :
    (DerivedCategory.homologyFunctor B q).map
        (F.rightDerivedFunctor.map ((DerivedCategory.singleFunctor A q).map φ)) ≫
      (F.acyclicHeartSingleIso Y q).hom =
    (F.acyclicHeartSingleIso X q).hom ≫ F.map φ := by
  rw [← singleComparison_hom_app, ← singleComparison_hom_app]
  exact (singleComparison F q).hom.naturality φ

omit [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
  [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B] in
/-- The incoming differential of `τ_{≤q}K` is killed by the quotient to `H^q(K)`. -/
private theorem truncLE_d_comp_homologyπ' (K : CochainComplex A ℤ) (q : ℤ) (r : ℤ)
    (_ : (ComplexShape.up ℤ).Rel r q) :
    (K.truncLE q).d r q ≫ (K.truncLEXIsoCycles q).hom ≫ K.homologyπ q = 0 := by
  obtain ⟨i, j, b, hi, hs, hz, he, hj, hn⟩ :=
    CochainComplex.exists_upperTruncationStepSES (C := A)
  rw [← (hj K q).1, ← Category.assoc, ← (j K q).comm r q]
  simp

/-- The projection `τ_{≤q}K → H^q(K)[-q]` for an arbitrary cochain complex; on
bounded-below complexes it is `TruncationCouple.projection`. -/
private noncomputable def truncProjection (K : CochainComplex A ℤ) (q : ℤ) :
    K.truncLE q ⟶ (CochainComplex.singleFunctor A q).obj (K.homology q) :=
  HomologicalComplex.mkHomToSingle
    ((K.truncLEXIsoCycles q).hom ≫ K.homologyπ q) (truncLE_d_comp_homologyπ' K q)

omit [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
  [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B] in
/-- Naturality of the truncation projection. -/
private theorem truncProjection_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (q : ℤ) :
    CochainComplex.truncLEMap f q ≫ truncProjection L q =
      truncProjection K q ≫
        (CochainComplex.singleFunctor A q).map (HomologicalComplex.homologyMap f q) := by
  obtain ⟨i, j, b, hi, hs, hz, he, hj, hn⟩ :=
    CochainComplex.exists_upperTruncationStepSES (C := A)
  have hp (M : CochainComplex A ℤ) : truncProjection M q = j M q := by
    apply HomologicalComplex.to_single_hom_ext
    apply (cancel_mono
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (M.homology q)).hom).1
    rw [(hj M q).1]
    simp [truncProjection, HomologicalComplex.mkHomToSingle_f]
  obtain ⟨g, hg₁, hg₂⟩ := (hn f q).2
  rw [hp, hp, (hj K q).2.2.1, (hj L q).2.2.1, ← Category.assoc, hg₁, Category.assoc,
    Category.assoc, hg₂]

/-- The projection `τ_{≤q} → H^q[-q]` as a natural transformation of functors on
cochain complexes. -/
private noncomputable def truncProjectionNatTrans (q : ℤ) :
    (ComplexShape.embeddingUpIntLE q).truncLEFunctor A ⟶
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙
        CochainComplex.singleFunctor A q where
  app K := truncProjection K q
  naturality _ _ f := truncProjection_naturality f q

omit [IsGrothendieckAbelian.{v₂} B] in
/-- Descent of `K ↦ H^q(RF(τ_{≤q}K))` along `Q`, with the truncation inclusion `c` and
the projection `g` to `F(H^q)` (theorem-pbc-injective-acyclicity). -/
private theorem descent_data (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] (q : ℤ) :
    ∃ (T : DerivedCategory A ⥤ B)
      (c : T ⟶ F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q)
      (g : T ⟶ DerivedCategory.homologyFunctor A q ⋙ F)
      (e : ∀ K : CochainComplex A ℤ, T.obj (DerivedCategory.Q.obj K) ≅
        (DerivedCategory.homologyFunctor B q).obj
          (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj (K.truncLE q)))),
      (∀ K : CochainComplex.Plus A, c.app (DerivedCategory.Q.obj K.obj) =
        (e K.obj).hom ≫ (DerivedCategory.homologyFunctor B q).map
          (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE q)))) ∧
      (∀ K : CochainComplex.Plus A, g.app (DerivedCategory.Q.obj K.obj) =
        (e K.obj).hom ≫ (DerivedCategory.homologyFunctor B q).map
          (F.rightDerivedFunctor.map
            (DerivedCategory.Q.map (TruncationCouple.projection K q))) ≫
          (F.acyclicHeartSingleIso (K.obj.homology q) q).hom ≫
          F.map ((DerivedCategory.homologyFunctorFactors A q).app K.obj).inv) := by
  obtain ⟨_, h₁, _, _⟩ := (DerivedCategory.truncation_triangle A q).2.1
  let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  let τ := (ComplexShape.embeddingUpIntLE q).truncLEFunctor A
  let Λ := Localization.lift (τ ⋙ DerivedCategory.Q) h₁ DerivedCategory.Q
  let RH := F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q
  let σ : (τ ⋙ DerivedCategory.Q) ⋙ RH ⟶
      DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor A q ⋙ F :=
    { app K := RH.map (DerivedCategory.Q.map (truncProjection K q)) ≫
        (F.acyclicHeartSingleIso (K.homology q) q).hom ≫
        F.map ((DerivedCategory.homologyFunctorFactors A q).inv.app K)
      naturality K L f := by
        have h : τ.map f ≫ truncProjection L q = truncProjection K q ≫
            (CochainComplex.singleFunctor A q).map (HomologicalComplex.homologyMap f q) :=
          truncProjection_naturality f q
        have hh := (DerivedCategory.homologyFunctorFactors A q).inv.naturality f
        have hs := acyclicHeartSingleIso_hom_naturality_assoc F q
          (HomologicalComplex.homologyMap f q)
          (F.map ((DerivedCategory.homologyFunctorFactors A q).inv.app L))
        dsimp only [Functor.comp_map, RH, HomologicalComplex.homologyFunctor_map] at hh hs ⊢
        rw [Category.assoc, Category.assoc, ← F.map_comp, ← hh, F.map_comp,
          HomologicalComplex.homologyFunctor_map, ← hs]
        simp only [← Category.assoc, ← Functor.map_comp, h]
        rw [DerivedCategory.Q.map_comp]
        rfl }
  let c : Λ ⋙ RH ⟶ RH := Localization.liftNatTrans DerivedCategory.Q W
    ((τ ⋙ DerivedCategory.Q) ⋙ RH) (DerivedCategory.Q ⋙ RH) (Λ ⋙ RH) RH
    (Functor.whiskerRight (Functor.whiskerRight
      ((ComplexShape.embeddingUpIntLE q).ιTruncLENatTrans A) DerivedCategory.Q ≫
        (Functor.leftUnitor DerivedCategory.Q).hom) RH)
  let g : Λ ⋙ RH ⟶ DerivedCategory.homologyFunctor A q ⋙ F :=
    Localization.liftNatTrans DerivedCategory.Q W ((τ ⋙ DerivedCategory.Q) ⋙ RH)
      (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor A q ⋙ F) (Λ ⋙ RH)
      (DerivedCategory.homologyFunctor A q ⋙ F) σ
  refine ⟨Λ ⋙ RH, c, g,
    fun K ↦ RH.mapIso ((Localization.Lifting.iso DerivedCategory.Q W
      (τ ⋙ DerivedCategory.Q) Λ).app K), fun K ↦ ?_, fun K ↦ ?_⟩
  · simp [c, RH, τ]
    rfl
  · simp [g, σ, RH, τ, truncProjection, TruncationCouple.projection]

set_option linter.unusedVariables false in
/-- The canonical acyclic-heart edge is invertible and natural, including in compatible
morphisms of the derived-functor data. Compatibility is imposed only on shifted single
objects, by their degree-zero augmentation comparisons, not on the edge to be proved.
Source: Stacks Tag 0D7U, lemma-equivalence-bounded, spectral-sequence argument
(blueprint: lem-fd-acyclic-heart-edge).

Proof:
1. Build the raw type-zero exact couple of lem-sp-truncation-raw-exact. Its E term
   vanishes for p<0 by lem-sp-truncation-quadrant-vanishing, and for p>0 by the
   shift isomorphisms, H^p(RF(X[0]))=R^pF(X) and the assumed acyclicity.
2. For any type-zero couple with this E term, induction on the page shows all
   nonzero columns stay zero; both differentials at column zero then vanish, so
   the cycle-boundary recursion gives Z_r=top and B_r=bottom at every index.
3. With a lower bound a for the representative K, D^{p,q}=0 for q<a; finite
   induction on q-a through the exact pairs D^{p+1,q-1} -> D^{p,q} -> E^{p,q}
   gives D^{p,q}=0 for p>0. Hence g^{0,q} is monic and epic, so H^q(RF) of the
   projection is invertible; lem-sp-truncation-abutment-cocone makes H^q(RF) of
   the inclusion at q invertible, and the inclusion at q-1 is zero in degree q.
   This gives the two filtration-image identities.
4. Descend K |-> H^q(RF(Q(tau_le_q K))) along Q. The inclusion descends to
   c : T -> H^q RF, and the projection of theorem-pbc-injective-acyclicity with
   the single-object comparison descends to g : T -> F H^q. Every bounded-below
   object has a bounded-below representative, so c is invertible and, under
   acyclicity, so is g. The edge is c^{-1} followed by g; its normalization
   follows from the component formulas of c and g.
5. Naturality of c and g gives naturality of the edge. Uniqueness: precompose
   two normalized edges with the invertible H^q(RF(inclusion)) and the
   representing isomorphism and compare right sides.
6. For compatible tau, rho: precompose with the same isomorphism, move rho by
   its naturality to the truncation and the single object, apply the assumed
   single-object compatibility and naturality of tau, and cancel. -/
theorem exists_acyclicHeartEdge (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] :
    ∃! edge : F.AcyclicHeartEdgeFamily,
      F.IsAcyclicHeartEdge edge ∧
      (∀ (L : DerivedCategory.Plus A)
        (h : ∀ (j : ℤ) (p : ℕ), 0 < p →
          IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj L.obj)))
        (q : ℤ), IsIso (edge L h q)) ∧
      (∀ (L M : DerivedCategory.Plus A)
        (hL : ∀ (j : ℤ) (p : ℕ), 0 < p →
          IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj L.obj)))
        (hM : ∀ (j : ℤ) (p : ℕ), 0 < p →
          IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj M.obj)))
        (f : L ⟶ M) (q : ℤ),
        (DerivedCategory.homologyFunctor B q).map (F.rightDerivedFunctor.map f.hom) ≫
          edge M hM q =
        edge L hL q ≫ F.map ((DerivedCategory.homologyFunctor A q).map f.hom)) ∧
      (∀ (K : CochainComplex.Plus A)
        (hK : ∀ (j : ℤ) (p : ℕ), 0 < p →
          IsZero ((F.rightDerived p).obj (K.obj.homology j))),
        (∀ n : ℤ,
          imageSubobject ((DerivedCategory.homologyFunctor B n).map
            (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE n)))) = ⊤ ∧
          imageSubobject ((DerivedCategory.homologyFunctor B n).map
            (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE (n - 1))))) =
              ⊥) ∧
        (∀ X : BigradedExactCouple B 0, X.E = TruncationCouple.E F K →
          (∀ (r : ℕ) (p q : ℤ), 2 ≤ r → p ≠ 0 → IsZero (X.page r p q)) ∧
          (∀ (r : ℕ) (q : ℤ), X.cycleBoundaryTower.Z r 0 q = ⊤ ∧
            X.cycleBoundaryTower.B r 0 q = ⊥))) ∧
      (∀ (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]
        (τ : F ⟶ G) (ρ : F.rightDerivedFunctor ⟶ G.rightDerivedFunctor),
        (∀ (X : A) (q : ℤ),
          (DerivedCategory.homologyFunctor B q).map
              (ρ.app ((DerivedCategory.singleFunctor A q).obj X)) ≫
            (G.acyclicHeartSingleIso X q).hom =
          (F.acyclicHeartSingleIso X q).hom ≫ τ.app X) →
        ∀ (edgeG : G.AcyclicHeartEdgeFamily), G.IsAcyclicHeartEdge edgeG →
        ∀ (L : DerivedCategory.Plus A)
          (hF : ∀ (j : ℤ) (p : ℕ), 0 < p →
            IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj L.obj)))
          (hG : ∀ (j : ℤ) (p : ℕ), 0 < p →
            IsZero ((G.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj L.obj)))
          (q : ℤ),
          (DerivedCategory.homologyFunctor B q).map (ρ.app L.obj) ≫ edgeG L hG q =
            edge L hF q ≫ τ.app ((DerivedCategory.homologyFunctor A q).obj L.obj)) := by
  classical
  choose T c g e hc hg using (fun q : ℤ ↦ descent_data F q)
  have hci (L : DerivedCategory.Plus A) (q : ℤ) : IsIso ((c q).app L.obj) := by
    obtain ⟨K, ⟨a⟩⟩ := bounded_representative L
    have : IsIso ((c q).app (DerivedCategory.Q.obj K.obj)) := by
      rw [hc]
      have := inclusion_isIso F K q
      infer_instance
    have : IsIso ((T q).map a.hom ≫ (c q).app L.obj) := by
      rw [(c q).naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left ((T q).map a.hom) _
  let edge : F.AcyclicHeartEdgeFamily := fun L _ q ↦ by
    have := hci L q
    exact CategoryTheory.inv ((c q).app L.obj) ≫ (g q).app L.obj
  have hnorm : F.IsAcyclicHeartEdge edge := by
    intro L h K a q
    have := hci L q
    have := inclusion_isIso F K q
    apply (cancel_epi (e q K.obj).hom).1
    calc
      _ = (c q).app (DerivedCategory.Q.obj K.obj) ≫
          (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q).map a.hom ≫
            edge L h q := by rw [hc]; simp only [Category.assoc, Functor.comp_map]
      _ = (T q).map a.hom ≫ (g q).app L.obj := by
        rw [← (c q).naturality_assoc]
        simp [edge]
      _ = (g q).app (DerivedCategory.Q.obj K.obj) ≫
          F.map ((DerivedCategory.homologyFunctor A q).map a.hom) :=
        (g q).naturality a.hom
      _ = _ := by rw [hg]; simp only [Functor.map_comp, Category.assoc]
  have hiso (L : DerivedCategory.Plus A)
      (h : ∀ (j : ℤ) (p : ℕ), 0 < p →
        IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj L.obj)))
      (q : ℤ) : IsIso (edge L h q) := by
    obtain ⟨K, ⟨a⟩⟩ := bounded_representative L
    have hK := representative_acyclic F L h K a
    have : IsIso ((g q).app (DerivedCategory.Q.obj K.obj)) := by
      rw [hg]
      have := projection_isIso F K hK q
      infer_instance
    have : IsIso ((T q).map a.hom ≫ (g q).app L.obj) := by
      rw [(g q).naturality]
      infer_instance
    have : IsIso ((g q).app L.obj) := IsIso.of_isIso_comp_left ((T q).map a.hom) _
    have := hci L q
    dsimp [edge]
    infer_instance
  refine ⟨edge, ⟨hnorm, hiso, ?_, ?_, ?_⟩, ?_⟩
  · intro L M hL hM f q
    have := hci L q
    have := hci M q
    apply (cancel_epi ((c q).app L.obj)).1
    dsimp [edge]
    have hn := (c q).naturality f.hom
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact (g q).naturality f.hom
  · intro K hK
    refine ⟨filtration_images F K hK, ?_⟩
    intro X hE
    have hz (p q : ℤ) (hp : p ≠ 0) : IsZero (X.E p q) := by
      rw [hE]
      exact initial_column_zero F K hK p q hp
    exact ⟨fun r p q _ hp ↦ column_page_zero X hz (r - 2) p q hp,
      column_tower X hz⟩
  · intro G _ _ τ ρ hρ edgeG hG L hF hGL q
    obtain ⟨K, ⟨a⟩⟩ := bounded_representative L
    have := inclusion_isIso F K q
    let H := DerivedCategory.homologyFunctor B q
    let t := DerivedCategory.Q.map (K.obj.ιTruncLE q)
    let j : DerivedCategory.Q.obj (K.obj.truncLE q) ⟶
        (DerivedCategory.singleFunctor A q).obj (K.obj.homology q) :=
      DerivedCategory.Q.map (TruncationCouple.projection K q)
    let b := ((DerivedCategory.homologyFunctorFactors A q).app K.obj).inv ≫
      (DerivedCategory.homologyFunctor A q).map a.hom
    apply (cancel_epi (H.map (F.rightDerivedFunctor.map t) ≫
      H.map (F.rightDerivedFunctor.map a.hom))).1
    have hi : H.map (F.rightDerivedFunctor.map t) ≫
        H.map (F.rightDerivedFunctor.map a.hom) ≫ H.map (ρ.app L.obj) =
      H.map (ρ.app (DerivedCategory.Q.obj (K.obj.truncLE q))) ≫
        H.map (G.rightDerivedFunctor.map t) ≫ H.map (G.rightDerivedFunctor.map a.hom) := by
      rw [← H.map_comp, ρ.naturality, H.map_comp, ← H.map_comp_assoc,
        ρ.naturality, H.map_comp_assoc]
    have hj : H.map (ρ.app (DerivedCategory.Q.obj (K.obj.truncLE q))) ≫
        H.map (G.rightDerivedFunctor.map j) =
      H.map (F.rightDerivedFunctor.map j) ≫
        H.map (ρ.app ((DerivedCategory.singleFunctor A q).obj (K.obj.homology q))) := by
      simpa only [Functor.map_comp] using (H.congr_map (ρ.naturality j)).symm
    calc
      _ = H.map (ρ.app (DerivedCategory.Q.obj (K.obj.truncLE q))) ≫
          (H.map (G.rightDerivedFunctor.map t) ≫
            H.map (G.rightDerivedFunctor.map a.hom) ≫ edgeG L hGL q) := by
        simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ edgeG L hGL q) hi
      _ = H.map (ρ.app (DerivedCategory.Q.obj (K.obj.truncLE q))) ≫
          H.map (G.rightDerivedFunctor.map j) ≫
          (G.acyclicHeartSingleIso (K.obj.homology q) q).hom ≫ G.map b := by
        rw [hG L hGL K a q]
      _ = H.map (F.rightDerivedFunctor.map j) ≫
          (F.acyclicHeartSingleIso (K.obj.homology q) q).hom ≫
          τ.app (K.obj.homology q) ≫ G.map b := by
        rw [← Category.assoc, hj, Category.assoc]
        erw [reassoc_of% (hρ (K.obj.homology q) q)]
      _ = H.map (F.rightDerivedFunctor.map j) ≫
          (F.acyclicHeartSingleIso (K.obj.homology q) q).hom ≫
          F.map b ≫ τ.app ((DerivedCategory.homologyFunctor A q).obj L.obj) := by
        rw [← τ.naturality]
      _ = _ := by
        simpa only [H, t, j, b, Category.assoc] using
          congrArg (fun f ↦ f ≫ τ.app ((DerivedCategory.homologyFunctor A q).obj L.obj))
            (hnorm L hF K a q).symm
  · intro edge' h'
    funext L h q
    obtain ⟨K, ⟨a⟩⟩ := bounded_representative L
    have := inclusion_isIso F K q
    apply (cancel_epi
      ((DerivedCategory.homologyFunctor B q).map
          (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE q))) ≫
        (DerivedCategory.homologyFunctor B q).map (F.rightDerivedFunctor.map a.hom))).1
    simpa only [Category.assoc] using
      (h'.1 L h K a q).trans (hnorm L h K a q).symm

end CategoryTheory.Functor
