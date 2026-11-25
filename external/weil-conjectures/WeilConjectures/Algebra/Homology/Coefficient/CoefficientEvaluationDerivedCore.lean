/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

/-!
# Deriving the coefficient evaluation adjunction

Source: Zheng, Construction 4.1, p. 21; Stacks Project, Tags 06XN and 09T5.
(blueprint: lem-pur-coefficient-evaluation-derived-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w d
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  {O : Type w} [CommRing O] {ell : O}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [EssentiallySmall.{w} C] in
private theorem coefficient_hom_ext {M N : CoefficientSystem (J := J) O ell}
    (f g : M ⟶ N) (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr 1
  funext n
  exact h n

omit [EssentiallySmall.{w} C] in
private theorem coefficient_isIso_of_components
    {M N : CoefficientSystem (J := J) O ell} (f : M ⟶ N)
    (hf : ∀ n, IsIso (f.app n)) : IsIso f := by
  let := hf
  let g : N ⟶ M :=
    { app := fun n ↦ inv (f.app n)
      comm := fun n ↦ by
        apply (cancel_epi (f.app (n + 1))).1
        simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
        rw [f.comm]
        simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id]
        change _ = _ ≫ (coefficientRestriction O ell (Nat.le_succ n)).map (𝟙 _)
        rw [CategoryTheory.Functor.map_id, Category.comp_id] }
  refine ⟨g, ?_, ?_⟩
  · apply coefficient_hom_ext
    intro n
    exact IsIso.hom_inv_id _
  · apply coefficient_hom_ext
    intro n
    exact IsIso.inv_hom_id _

omit [EssentiallySmall.{w} C] in
private theorem coefficient_quasiIso_of_evaluations
    {K L : CochainComplex (CoefficientSystem (J := J) O ell) ℤ} (f : K ⟶ L)
    (hf : ∀ n, QuasiIso
      (((coefficientEvaluation (J := J) (O := O) (ell := ell) n).mapHomologicalComplex
        (.up ℤ)).map f)) : QuasiIso f := by
  constructor
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply coefficient_isIso_of_components
  intro n
  let e := coefficientEvaluation (J := J) (O := O) (ell := ell) n
  let := (coefficientEvaluation_exact (J := J) (O := O) (ell := ell) n).1
  let := (coefficientEvaluation_exact (J := J) (O := O) (ell := ell) n).2
  let := hf n
  let S := K.sc i
  let T := L.sc i
  let g := (HomologicalComplex.shortComplexFunctor _ _ i).map f
  have hh := ShortComplex.mapHomologyIso_hom_naturality g e
  have : IsIso (ShortComplex.homologyMap (e.mapShortComplex.map g)) := by
    change IsIso (HomologicalComplex.homologyMap
      ((e.mapHomologicalComplex (.up ℤ)).map f) i)
    infer_instance
  have heq : e.map (HomologicalComplex.homologyMap f i) =
      (S.mapHomologyIso e).inv ≫
        ShortComplex.homologyMap (e.mapShortComplex.map g) ≫
        (T.mapHomologyIso e).hom := by
    erw [hh, Iso.inv_hom_id_assoc]
    rfl
  change IsIso (e.map (HomologicalComplex.homologyMap f i))
  rw [heq]
  infer_instance

omit [EssentiallySmall.{w} C] in
private theorem coefficient_quasiIso_transport
    {m n : ℕ}
    (E F : coefficientLevelModules (J := J) O ell m ⥤
      coefficientLevelModules (J := J) O ell n) [E.Additive] [F.Additive] (h : E = F)
    {P Q : CochainComplex (coefficientLevelModules (J := J) O ell m) ℤ} (f : P ⟶ Q)
    (hf : QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  cases h
  exact hf

variable [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]

omit [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)] in
private theorem coefficient_extension_preserves_quasiIso
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive] (n : ℕ)
    {P Q : CochainComplex (coefficientLevelModules (J := J) O ell n) ℤ}
    (f : P ⟶ Q) (hP : P.IsKFlatIndependentCoefficients)
    (hQ : Q.IsKFlatIndependentCoefficients) (hf : QuasiIso f) :
    QuasiIso (((ordinary.extension n).mapHomologicalComplex (.up ℤ)).map f) := by
  let := hf
  apply coefficient_quasiIso_of_evaluations
  intro q
  by_cases h : q ≤ n
  · obtain ⟨E, hobj, hmap, _, hpres, _⟩ :=
      derivedChangeOfRingsIndependentCoefficients (coefficientQuotientMap (J := J) O ell h)
    have hE : E = coefficientTensor (J := J) (O := O) (ell := ell) h := by
      refine CategoryTheory.Functor.ext hobj ?_
      intro M N f
      exact hmap f
    have ht := coefficient_quasiIso_transport E
      (coefficientTensor (J := J) (O := O) (ell := ell) h) hE f (hpres f hP hQ hf)
    let b := NatIso.mapHomologicalComplex (ordinary.below h) (.up ℤ)
    have hh := b.hom.naturality f
    let e := coefficientEvaluation (J := J) (O := O) (ell := ell) q
    let ef := (e.mapHomologicalComplex (.up ℤ)).map
      (((ordinary.extension n).mapHomologicalComplex (.up ℤ)).map f)
    have heq : ef = b.hom.app P ≫
        ((coefficientTensor (J := J) (O := O) (ell := ell) h).mapHomologicalComplex
          (.up ℤ)).map f ≫ b.inv.app Q := by
      erw [← Category.assoc, ← hh, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
      rfl
    change QuasiIso ef
    rw [heq]
    infer_instance
  · have hq := Nat.lt_of_not_ge h
    let e := coefficientEvaluation (J := J) (O := O) (ell := ell) q
    let ef := (e.mapHomologicalComplex (.up ℤ)).map
      (((ordinary.extension n).mapHomologicalComplex (.up ℤ)).map f)
    have : ∀ i, IsIso (ef.f i) := fun i ↦
      (ordinary.above n q hq (P.X i)).isIso
        (ordinary.above n q hq (Q.X i)) (ef.f i)
    have := HomologicalComplex.Hom.isIso_of_components ef
    infer_instance

/-- A derived evaluation adjunction and its comparison on complex representatives.
Source: Zheng, Construction 4.1, p. 21; Stacks Tags 06XN and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-core). -/
structure CoefficientEvaluationDerivedCoreData
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive] where
  evaluation : ∀ n, DerivedCategory (CoefficientSystem (J := J) O ell) ⥤
    DerivedCategory (coefficientLevelModules (J := J) O ell n)
  evaluationFactors : ∀ n, DerivedCategory.Q ⋙ evaluation n ≅
    (coefficientEvaluation (J := J) (O := O) (ell := ell) n).mapHomologicalComplex
      (.up ℤ) ⋙ DerivedCategory.Q
  derivedExtension : ∀ n, DerivedCategory (coefficientLevelModules (J := J) O ell n) ⥤
    DerivedCategory (CoefficientSystem (J := J) O ell)
  counit : ∀ n, DerivedCategory.Q ⋙ derivedExtension n ⟶
    (ordinary.extension n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  pointwise : ∀ n,
    ((ordinary.extension n).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
      (HomologicalComplex.quasiIso (coefficientLevelModules (J := J) O ell n) (.up ℤ))
  isDerived : ∀ n, (derivedExtension n).IsLeftDerivedFunctor (counit n)
    (HomologicalComplex.quasiIso (coefficientLevelModules (J := J) O ell n) (.up ℤ))
  computes : ∀ n P, P.IsKFlatIndependentCoefficients → IsIso ((counit n).app P)
  derivedAdj : ∀ n, derivedExtension n ⊣ evaluation n
  transpose : ∀ n P K
      (f : ((ordinary.extension n).mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    (derivedAdj n).homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      ((counit n).app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map (((ordinary.adj n).mapHomologicalComplex (.up ℤ)).homEquiv
          P K f) ≫ (evaluationFactors n).inv.app K

/-- Derive the fixed strict extension adjunction using flat-term K-flat resolutions.
Source: Zheng, Construction 4.1, p. 21; Stacks Project, Tags 06XN and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-core).
Proof: exact componentwise evaluation jointly detects quasi-isomorphisms. Below the
chosen level, extension is tensor scalar change and preserves quasi-isomorphisms between
K-flat complexes; above that level, both complexes are zero. Thus extension preserves
quasi-isomorphisms on the resolving class. K-flat resolutions exist at every level.
Apply the normalized resolving-class adjunction theorem to each ordinary adjunction;
exact evaluation is its right adjoint and descends termwise. Its transpose formula is
valid on every complex representative, and its counit is invertible on K-flat complexes. -/
theorem coefficientEvaluationDerivedCore
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive] :
    Nonempty (CoefficientEvaluationDerivedCoreData ordinary) := by
  classical
  let : ∀ n, PreservesFiniteLimits
      (coefficientEvaluation (J := J) (O := O) (ell := ell) n) :=
    fun n ↦ (coefficientEvaluation_exact n).1
  let : ∀ n, PreservesFiniteColimits
      (coefficientEvaluation (J := J) (O := O) (ell := ell) n) :=
    fun n ↦ (coefficientEvaluation_exact n).2
  have hc (n : ℕ) := by
    exact CategoryTheory.Adjunction.exists_leftDerived_adjunction
      (ordinary.extension n) (coefficientEvaluation (J := J) (O := O) (ell := ell) n)
      (ordinary.adj n) CochainComplex.IsKFlatIndependentCoefficients
      (fun X ↦ by
        obtain ⟨Y, s, hY, _, hs, _⟩ :=
          CochainComplex.exists_isKFlatResolutionIndependentCoefficients X
        exact ⟨Y, s, hY, hs⟩)
      (fun f hP hQ hf ↦ coefficient_extension_preserves_quasiIso ordinary n f hP hQ hf)
  choose hpw L ε hu hcomp a ha using hc
  exact ⟨{
    evaluation := fun n ↦
      (coefficientEvaluation (J := J) (O := O) (ell := ell) n).mapDerivedCategory
    evaluationFactors := fun n ↦
      (coefficientEvaluation (J := J) (O := O) (ell := ell) n).mapDerivedCategoryFactors
    derivedExtension := L
    counit := ε
    pointwise := hpw
    isDerived := hu
    computes := hcomp
    derivedAdj := a
    transpose := ha }⟩

end SheafOfModules
