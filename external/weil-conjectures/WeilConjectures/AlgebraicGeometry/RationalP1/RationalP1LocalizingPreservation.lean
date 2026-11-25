/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.TateTwistedProjection
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import Mathlib.Algebra.CharP.Invertible
import all WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LineFromPreservation
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1PositiveLineConstructible

/-! # Rational projective-line localizing preservation

The proposition records all geometry, coefficient, intermediate-functor and exactness
checks, as well as the final preservation pair. Its auxiliary propositions only group
its clauses; the categories, operations and full-subcategory lifts are existing
constructions. In particular no new derived functor or coefficient line is chosen.

## Main definitions

- `LocalizingFunctorChecks`: preservation and exactness of the canonical restriction.
- `ProjectiveLineLocalizingObjectChecks`: unit, Tate line, tensor and twist assertions.
- `ProjectiveLineLocalizingGeometry`: all geometric domain checks.
- `ProjectiveLineLocalizingChecks`: the complete package for the projective-line diagram.

## Main statements

- `localizingPreservationChecks`: the full localizing-preservation assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.RationalP1

open DiagonalCoefficients CondensedRing

/-- Preservation and exactness on the ambient category and its full localizing subcategories.
The shifts and triangles on the subcategories are inherited; `ObjectProperty.lift` fixes the
restriction on both objects and morphisms. -/
structure LocalizingFunctorChecks
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}}
    (F : DerivedCategory (Modules Λ X) ⥤ DerivedCategory (Modules Λ S)) : Prop where
  preserves : ∀ A : DerivedCategory (Modules Λ X),
    CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ X) A →
      CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ S) (F.obj A)
  [sourceTriangulated : (CategoryTheory.localizingClosure
    (constantModelBoundedConstructible Λ X)).IsTriangulated]
  [targetTriangulated : (CategoryTheory.localizingClosure
    (constantModelBoundedConstructible Λ S)).IsTriangulated]
  exactRestriction :
    let _ : ∀ n : ℤ, (shiftFunctor (CategoryTheory.localizingClosure
        (constantModelBoundedConstructible Λ X)).FullSubcategory n).Additive :=
      fun _n ↦ inferInstance
    let _ : ∀ n : ℤ, (shiftFunctor (CategoryTheory.localizingClosure
        (constantModelBoundedConstructible Λ S)).FullSubcategory n).Additive :=
      fun _n ↦ inferInstance
    ∃ s : F.CommShift ℤ,
    (fun [_commShift : F.CommShift ℤ] ↦
      F.IsTriangulated ∧
      ((CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ S)).lift
        ((CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ X)).ι ⋙ F)
        (fun A ↦ preserves A.obj A.property)).IsTriangulated) (_commShift := s)

/-- The bounded constructible generators, tensor closure and exact positive Tate twist at
one of the three schemes. -/
structure ProjectiveLineLocalizingObjectChecks (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l)) (Z : Scheme.{u}) : Prop where
  coefficientUnit : constantModelBoundedConstructible (coefficient l c).X Z
    (unit (coefficient l c).X Z)
  positiveLine : constantModelBoundedConstructible (coefficient l c).X Z
    ((DerivedCategory.singleFunctor (Modules (coefficient l c).X Z) 0).obj (line l c Z))
  tensorClosed : ∀ A B : DerivedCategory (Modules (coefficient l c).X Z),
    CategoryTheory.localizingClosure (constantModelBoundedConstructible (coefficient l c).X Z)
      A →
    CategoryTheory.localizingClosure (constantModelBoundedConstructible (coefficient l c).X Z)
      B →
    CategoryTheory.localizingClosure (constantModelBoundedConstructible (coefficient l c).X Z)
      (((CondensedRing.derivedTensor (coefficient l c).X Z).obj A).obj B)
  twist : LocalizingFunctorChecks (coefficient l c).X
    (RationalP1.twist (coefficient l c).X Z (line l c Z))

/-- All geometric domain checks for the projective line, its self-product and the open
complement of the closed diagonal. Structural maps are the displayed composites to `Spec k`. -/
structure ProjectiveLineLocalizingGeometry (l : ℕ) {k : Type u} [Field k]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] : Prop where
  noetherianY : IsNoetherian Y
  noetherianP : IsNoetherian (ProjectiveLine Y)
  noetherianW : IsNoetherian (diagonalSurface Y)
  qcqsY : CompactSpace Y ∧ QuasiSeparatedSpace Y
  qcqsP : CompactSpace (ProjectiveLine Y) ∧ QuasiSeparatedSpace (ProjectiveLine Y)
  qcqsW : CompactSpace (diagonalSurface Y) ∧ QuasiSeparatedSpace (diagonalSurface Y)
  properQ : IsProper (ProjectiveLine Y ↘ Y)
  properFirst : IsProper (firstProjection Y)
  properSecond : IsProper (secondProjection Y)
  properDiagonal : IsProper (diagonalImmersion Y)
  closedDiagonal : IsClosedImmersion (diagonalImmersion Y)
  quasiCompactComplement : QuasiCompact (diagonalImmersion Y).openComplement.ι
  invertibleY : ∀ x : Y, IsUnit (l : Y.residueField x)
  invertibleP : ∀ x : ProjectiveLine Y, IsUnit (l : (ProjectiveLine Y).residueField x)
  invertibleW : ∀ x : diagonalSurface Y, IsUnit (l : (diagonalSurface Y).residueField x)
  invertibleComplement : ∀ x : (diagonalImmersion Y).openComplement.toScheme,
    IsUnit (l : (diagonalImmersion Y).openComplement.toScheme.residueField x)
  standingP : IsSeparated ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) ∧
    LocallyOfFiniteType ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) ∧
    QuasiCompact ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k)))
  standingW : IsSeparated (firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫
      (Y ↘ Spec (.of k))) ∧
    LocallyOfFiniteType (firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫
      (Y ↘ Spec (.of k))) ∧
    QuasiCompact (firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k)))
  standingComplement : IsSeparated ((diagonalImmersion Y).openComplement.ι ≫
      firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) ∧
    LocallyOfFiniteType ((diagonalImmersion Y).openComplement.ι ≫
      firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) ∧
    QuasiCompact ((diagonalImmersion Y).openComplement.ι ≫
      firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k)))

/-- The entire preservation package; `pushQ` and `twistedPullQ` contain the two obligations
called `localizingPreservation` in the original assembly, together with their exact
restrictions. The remaining fields retain every hypothesis check and intermediate assertion. -/
structure ProjectiveLineLocalizingChecks (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l)) {k : Type u} [Field k]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] : Prop where
  geometry : ProjectiveLineLocalizingGeometry l (k := k) Y
  objectsY : ProjectiveLineLocalizingObjectChecks l c Y
  objectsP : ProjectiveLineLocalizingObjectChecks l c (ProjectiveLine Y)
  objectsW : ProjectiveLineLocalizingObjectChecks l c (diagonalSurface Y)
  pullQ : LocalizingFunctorChecks (coefficient l c).X
    (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y))
  pushQ : LocalizingFunctorChecks (coefficient l c).X
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y))
  pullFirst : LocalizingFunctorChecks (coefficient l c).X
    (moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y))
  pushFirst : LocalizingFunctorChecks (coefficient l c).X
    (moduleObjectDerivedPushforward (coefficient l c).X (firstProjection Y))
  pullSecond : LocalizingFunctorChecks (coefficient l c).X
    (moduleObjectDerivedPullback (coefficient l c).X (secondProjection Y))
  pushSecond : LocalizingFunctorChecks (coefficient l c).X
    (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y))
  pullDiagonal : LocalizingFunctorChecks (coefficient l c).X
    (moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y))
  pushDiagonal : LocalizingFunctorChecks (coefficient l c).X
    (moduleObjectDerivedPushforward (coefficient l c).X (diagonalImmersion Y))
  twistedPullQ : LocalizingFunctorChecks (coefficient l c).X
    (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y) ⋙
      RationalP1.twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y)))

private theorem checks_of_preserves
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}}
    (F : DerivedCategory (Modules Λ X) ⥤ DerivedCategory (Modules Λ S))
    [F.CommShift ℤ] [F.IsTriangulated]
    (h : ∀ A, CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ X) A →
      CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ S) (F.obj A)) :
    LocalizingFunctorChecks Λ F := by
  have : (CategoryTheory.localizingClosure
      (constantModelBoundedConstructible Λ X)).IsTriangulated :=
    (localizingClosure_exists Λ X (constantModelBoundedConstructible Λ X)).2.2.2.1.1
  have : (CategoryTheory.localizingClosure
      (constantModelBoundedConstructible Λ S)).IsTriangulated :=
    (localizingClosure_exists Λ S (constantModelBoundedConstructible Λ S)).2.2.2.1.1
  refine { preserves := h, exactRestriction := ?_ }
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem checks_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S Z : Scheme.{u}}
    (F : DerivedCategory (Modules Λ X) ⥤ DerivedCategory (Modules Λ S))
    (G : DerivedCategory (Modules Λ S) ⥤ DerivedCategory (Modules Λ Z))
    (hF : LocalizingFunctorChecks Λ F) (hG : LocalizingFunctorChecks Λ G) :
    LocalizingFunctorChecks Λ (F ⋙ G) := by
  let := hF.sourceTriangulated
  let := hF.targetTriangulated
  let := hG.targetTriangulated
  obtain ⟨sF, hFexact, _⟩ := hF.exactRestriction
  obtain ⟨sG, hGexact, _⟩ := hG.exactRestriction
  let := sF
  let := sG
  let := hFexact
  let := hGexact
  exact checks_of_preserves Λ (F ⋙ G) (fun A hA ↦
    hG.preserves _ (hF.preserves A hA))

private theorem coefficient_closure_eq
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z] :
    localizingClosureProEtale (coefficient l c).X Z =
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (coefficient l c).X Z) := by
  apply (localizingClosure_ctf_equals_bc l Z (coefficient l c).X ?_).1.2.2.2.1
  cases c with
  | none => exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))
  | some E => exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩))

private theorem pull_checks
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] (f : X ⟶ S) [f.IsOver (Spec (.of k))] :
    LocalizingFunctorChecks (coefficient l c).X
      (moduleObjectDerivedPullback (coefficient l c).X f) := by
  unfold moduleObjectDerivedPullback
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace S := quasiSeparatedSpace_of_quasiSeparated (S ↘ Spec (.of k))
  have hu : Nonempty (UnboundedLocalizingPullback (coefficient l c).X f) := by
    have h := unboundedLocalizingPullback p l hpl k f
    cases c with
    | none => exact h.2.2.2.2
    | some E => exact (h.2.2.2.1 E).2
  obtain ⟨hu⟩ := hu
  let := unboundedLocalizingPullbackCommShift (coefficient l c).X f
  let := hu.exact
  apply checks_of_preserves (coefficient l c).X _
  intro A hA
  rw [← coefficient_closure_eq l c X]
  apply hu.localizing ⟨A, ?_⟩
  rwa [coefficient_closure_eq l c S]

private theorem push_checks
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] (f : X ⟶ S) [f.IsOver (Spec (.of k))] [IsProper f] :
    LocalizingFunctorChecks (coefficient l c).X
      (moduleObjectDerivedPushforward (coefficient l c).X f) := by
  unfold moduleObjectDerivedPushforward
  have : Fact (ringChar k).Prime := ⟨by rw [ringChar.eq k p]; exact Fact.out⟩
  have : Fact (ringChar k ≠ l) := ⟨by rw [ringChar.eq k p]; exact hpl⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace S := quasiSeparatedSpace_of_quasiSeparated (S ↘ Spec (.of k))
  let E : PadicAlgCl.FiniteIntermediateField l := c.getD ⟨⊥, inferInstance⟩
  have hm : coefficient l c ∈ [Mon.mk (Profinite.continuousMapRingObj (ZMod l)),
      Mon.mk (Profinite.continuousMapRingObj ℤ_[l]),
      Mon.mk (Profinite.padicIntegersRingObj l E.val),
      Mon.mk (Profinite.continuousMapRingObj ℚ_[l]),
      Mon.mk (Profinite.continuousMapRingObj E), Mon.mk (Profinite.padicAlgClRingObj l)] := by
    cases c <;> simp [coefficient, E]
  have ha : ∃ n : ℕ, (l ^ n : ZMod l) = 0 := ⟨1, by simp⟩
  have hh := proper_image_localizing_proper_coefficients l E (ZMod l) ha
    (coefficient l c) hm k f
  have hr := proper_image_localizing_proper l E (ZMod l) ha (coefficient l c) hm f hh
  let := hr.1
  let := hr.2.1
  obtain ⟨hm, _, _⟩ := hr.2.2
  apply checks_of_preserves (coefficient l c).X _
  intro A hA
  rw [← coefficient_closure_eq l c S]
  apply hm ⟨A, ?_⟩
  rwa [coefficient_closure_eq l c X]

attribute [-instance] internalMonoidal internalTensorCommShift in
private theorem object_checks
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Z : Scheme.{u}) [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] (hl : ∀ x : Z, IsUnit (l : Z.residueField x)) :
    ProjectiveLineLocalizingObjectChecks l c Z := by
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (Z ↘ Spec (.of k))
  have hline := positiveLine_boundedConstructible l c Z hl
  have hcoeff : (∃ E : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (Mon.mk (coefficient l c).X ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk (coefficient l c).X ≅ Mon.mk (Profinite.padicAlgClRingObj l)) := by
    cases c with
    | none => exact Or.inr ⟨Iso.refl _⟩
    | some E => exact Or.inl ⟨E, ⟨Iso.refl _⟩⟩
  have htensor := (constantModelBoundedConstructible_derivedTensor l p hpl
    (Z ↘ Spec (.of k)) (coefficient l c).X hcoeff).2
  have hloc := (localizingClosure_exists (coefficient l c).X Z
    (constantModelBoundedConstructible (coefficient l c).X Z)).2.2.2
  let := hloc.1.1
  let B := (DerivedCategory.singleFunctor (Modules (coefficient l c).X Z) 0).obj
    (line l c Z)
  let F := twist (coefficient l c).X Z (line l c Z)
  let T := (CondensedRing.derivedTensor (coefficient l c).X Z).flip.obj (B⟦(2 : ℤ)⟧)
  let : T.CommShift ℤ :=
    DerivedCategory.commShiftTensorRight (Modules (coefficient l c).X Z) (B⟦(2 : ℤ)⟧)
  let : T.IsTriangulated :=
    DerivedCategory.isTriangulated_tensorRight (Modules (coefficient l c).X Z) (B⟦(2 : ℤ)⟧)
  let e : T ≅ F := NatIso.ofComponents
    (fun A ↦ ((tensorLeft A).commShiftIso (2 : ℤ)).app B)
    (fun {A A'} f ↦
      (NatTrans.shift_app_comm ((curriedTensor _).map f) (2 : ℤ) B).symm)
  let := Functor.CommShift.ofIso e ℤ
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  have : F.IsTriangulated := Functor.isTriangulated_of_iso e
  have htw : LocalizingFunctorChecks (coefficient l c).X F := by
    apply checks_of_preserves (coefficient l c).X F
    intro A hA
    exact ObjectProperty.le_shift _ (2 : ℤ) _
      (htensor A _ hA (hloc.2.1 _ hline))
  exact { coefficientUnit := coefficientUnit_boundedConstructible (coefficient l c).X Z
          positiveLine := hline
          tensorClosed := htensor
          twist := htw }

/-- All localizing preservation and exactness assertions in the projective-line geometry.
-/
theorem localizingPreservationChecks
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] :
    ProjectiveLineLocalizingChecks l c (k := k) Y := by
  have hp : IsProper (ProjectiveLine Y ↘ Y) := inferInstance
  have hp₁ : IsProper (firstProjection Y) := by
    unfold firstProjection
    infer_instance
  have hp₂ : IsProper (secondProjection Y) := by
    unfold secondProjection
    infer_instance
  have hd : IsClosedImmersion (diagonalImmersion Y) := by
    unfold diagonalImmersion
    infer_instance
  have hny : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have hcy : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have hnp : IsLocallyNoetherian (ProjectiveLine Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine Y ↘ Y)
  have hcp : CompactSpace (ProjectiveLine Y) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine Y ↘ Y)
  have hnw : IsLocallyNoetherian (diagonalSurface Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (firstProjection Y)
  have hcw : CompactSpace (diagonalSurface Y) :=
    QuasiCompact.compactSpace_of_compactSpace (firstProjection Y)
  have hnY : IsNoetherian Y := ⟨⟩
  have hnP : IsNoetherian (ProjectiveLine Y) := ⟨⟩
  have hnW : IsNoetherian (diagonalSurface Y) := ⟨⟩
  have hcj : QuasiCompact (diagonalImmersion Y).openComplement.ι := inferInstance
  have hunit : IsUnit (l : k) := by
    apply isUnit_iff_ne_zero.mpr
    exact (CharP.cast_eq_zero_iff k p l).not.mpr (by
      intro h
      exact hpl ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h))
  have hi (Z : Scheme.{u}) (a : Z ⟶ Spec (.of k)) (x : Z) :
      IsUnit (l : Z.residueField x) := by
    have := hunit.map (a.residueFieldAlgebraMap x)
    simpa using this
  have hg : ProjectiveLineLocalizingGeometry l (k := k) Y := {
    noetherianY := hnY
    noetherianP := hnP
    noetherianW := hnW
    qcqsY := ⟨inferInstance, inferInstance⟩
    qcqsP := ⟨inferInstance, inferInstance⟩
    qcqsW := ⟨inferInstance, inferInstance⟩
    properQ := hp
    properFirst := hp₁
    properSecond := hp₂
    properDiagonal := inferInstance
    closedDiagonal := hd
    quasiCompactComplement := hcj
    invertibleY := hi Y (Y ↘ Spec (.of k))
    invertibleP := hi _ ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k)))
    invertibleW := hi _ (firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k)))
    invertibleComplement := hi _ ((diagonalImmersion Y).openComplement.ι ≫
      firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k)))
    standingP := ⟨inferInstance, inferInstance, inferInstance⟩
    standingW := ⟨inferInstance, inferInstance, inferInstance⟩
    standingComplement := ⟨inferInstance, inferInstance, inferInstance⟩ }
  let hP : (ProjectiveLine Y).Over (Spec (.of k)) :=
    ⟨(ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))⟩
  let hW : (diagonalSurface Y).Over (Spec (.of k)) :=
    ⟨firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))⟩
  have : LocallyOfFiniteType (ProjectiveLine Y ↘ Spec (.of k)) := hg.standingP.2.1
  have : QuasiCompact (ProjectiveLine Y ↘ Spec (.of k)) := hg.standingP.2.2
  have : IsSeparated (ProjectiveLine Y ↘ Spec (.of k)) := hg.standingP.1
  have : LocallyOfFiniteType (diagonalSurface Y ↘ Spec (.of k)) := hg.standingW.2.1
  have : QuasiCompact (diagonalSurface Y ↘ Spec (.of k)) := hg.standingW.2.2
  have : IsSeparated (diagonalSurface Y ↘ Spec (.of k)) := hg.standingW.1
  have hq : (ProjectiveLine Y ↘ Y).IsOver (Spec (.of k)) := ⟨rfl⟩
  have h₁ : (firstProjection Y).IsOver (Spec (.of k)) := ⟨rfl⟩
  have h₂ : (secondProjection Y).IsOver (Spec (.of k)) := by
    constructor
    exact congrArg (fun f ↦ f ≫ (Y ↘ Spec (.of k))) pullback.condition.symm
  have hdOver : (diagonalImmersion Y).IsOver (Spec (.of k)) := by
    constructor
    change diagonalImmersion Y ≫ (firstProjection Y ≫
      (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) =
        (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))
    simp [diagonalImmersion, firstProjection, ← Category.assoc]
  have hpull := pull_checks l c k p hpl (ProjectiveLine Y ↘ Y)
  have hobjP := object_checks l c k p hpl (ProjectiveLine Y) hg.invertibleP
  exact {
    geometry := hg
    objectsY := object_checks l c k p hpl Y hg.invertibleY
    objectsP := hobjP
    objectsW := object_checks l c k p hpl (diagonalSurface Y) hg.invertibleW
    pullQ := hpull
    pushQ := push_checks l c k p hpl (ProjectiveLine Y ↘ Y)
    pullFirst := pull_checks l c k p hpl (firstProjection Y)
    pushFirst := push_checks l c k p hpl (firstProjection Y)
    pullSecond := pull_checks l c k p hpl (secondProjection Y)
    pushSecond := push_checks l c k p hpl (secondProjection Y)
    pullDiagonal := pull_checks l c k p hpl (diagonalImmersion Y)
    pushDiagonal := push_checks l c k p hpl (diagonalImmersion Y)
    twistedPullQ := checks_comp (coefficient l c).X _ _ hpull hobjP.twist }

end AlgebraicGeometry.ProEtale.RationalP1
