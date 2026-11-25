/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceLimit
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystem
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1KernelContractions

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalComposition
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1DiagonalTensor
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.TateTwistedProjection
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites

/-! # Triangle identities for the rational projective line

## Implementation details

The trace family is the realization of the whole-system diagonal limit and the three
unit/Chern traces, as specified by `Reference`, not an arbitrary `Family`. The completion,
cycle-system and limit hypotheses of `rationalP1_triangle` are exactly the input of
`diagonalTower_coefficients`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] unitComponent counitComponent twistProjectionMap
attribute [local irreducible] line diagram secondLineComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Integration along the first or second projection, with its canonical source normalization.
-/
def diagonalIntegral (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L) (i : Fin 2) : unit Λ (ProjectiveLine Y) ⟶
      unit Λ (ProjectiveLine Y) :=
  if i = 0 then d.support₁.hom ≫ d.R₁.R.map d.delta ≫ d.trace₁
  else d.support₂.hom ≫ d.R₂.R.map d.delta ≫ d.trace₂

/-- Identity tensor the normalized diagonal integral, using the coefficient right unitor. -/
def diagonalIntegralAction (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L) (i : Fin 2) (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    M ⟶ M :=
  (ρ_ M).inv ≫ (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
    diagonalIntegral Λ Y L d i ≫ (singleUnitIso Λ (ProjectiveLine Y)).hom)) ≫ (ρ_ M).hom

omit [IsCommMonObj Λ] in
private theorem diagonalIntegral_eq_id (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) (i : Fin 2) :
    diagonalIntegral Λ Y L d i = 𝟙 _ := by
  unfold diagonalIntegral
  split
  · exact d.integration₁
  · exact d.integration₂

private theorem diagonalIntegralAction_eq_id (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) (i : Fin 2)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    diagonalIntegralAction Λ Y L d i M = 𝟙 M := by
  simp [diagonalIntegralAction, diagonalIntegral_eq_id]

private theorem compareRightAdjointsOnEqualSubcategories
    {C D : Type*} [Category C] [Category D]
    (P P' : ObjectProperty C) (Q Q' : ObjectProperty D)
    (hP : P = P') (hQ : Q = Q') (F : C ⥤ D)
    (hF : ∀ X : P'.FullSubcategory, Q' (F.obj X.obj))
    (H : P.FullSubcategory ⥤ Q.FullSubcategory)
    (hH : H ⋙ Q.ι ≅ P.ι ⋙ F)
    (E : Q'.FullSubcategory ⥤ P'.FullSubcategory)
    (adj : Q'.lift (P'.ι ⋙ F) hF ⊣ E)
    (G : Q.FullSubcategory ⥤ P.FullSubcategory) (adjG : H ⊣ G) :
    ∃ (eP : P.FullSubcategory ≌ P'.FullSubcategory)
      (eQ : Q.FullSubcategory ≌ Q'.FullSubcategory),
      Nonempty (eP.functor ⋙ P'.ι ≅ P.ι) ∧
      Nonempty (eQ.functor ⋙ Q'.ι ≅ Q.ι) ∧
      Nonempty (G ⋙ eP.functor ≅ eQ.functor ⋙ E) := by
  subst P'
  subst Q'
  let eH : H ≅ Q.lift (P.ι ⋙ F) hF :=
    Functor.fullyFaithfulCancelRight Q.ι hH
  let adjG' := adjG.ofNatIsoLeft eH
  exact ⟨CategoryTheory.Equivalence.refl, CategoryTheory.Equivalence.refl,
    ⟨Functor.leftUnitor _⟩, ⟨Functor.leftUnitor _⟩,
    ⟨Functor.rightUnitor G ≪≫ adjG'.rightAdjointUniq adj ≪≫
      (Functor.leftUnitor E).symm⟩⟩

private theorem coefficientLocalizingEquality (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (X : Scheme.{u}) [IsNoetherian X] :
    localizingClosureProEtale (coefficient l c).X X =
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (coefficient l c).X X) := by
  apply (localizingClosure_ctf_equals_bc l X (coefficient l c).X ?_).1.2.2.2.1
  cases c with
  | none => exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))
  | some E => exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩))

private theorem coefficientAdmissible (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l)) :
    IsLocalizingAdmissibleCoefficient l (coefficient.{u} l c).X := by
  cases c with
  | none => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))
  | some E => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))

-- The ambient derived functor comparisons need additional elaboration steps.
private theorem brownComparison
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    (adj : push l c k p hpl Y ⊣ exceptional l c k p hpl Y)
    (compactification : Compactification.BoundaryCompactification (ProjectiveLine Y ↘ Y))
    (h : ∀ A, localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y) A →
      localizingClosureProEtale (coefficient l c).X Y
        ((CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient l c).X
          compactification.obj.obj).obj A))
    (G : (localizingClosureProEtale (coefficient l c).X Y).FullSubcategory ⥤
      (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).FullSubcategory)
    (adjG : localizingLowerShriek (coefficient l c).X compactification.obj.obj h ⊣ G) :
    ∃ (eP : (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).FullSubcategory ≌
        rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y))
      (eY : (localizingClosureProEtale (coefficient l c).X Y).FullSubcategory ≌
        rationalLocalizingCategory (coefficient l c).X Y),
      Nonempty (eP.functor ⋙ rationalLocalizingInclusion (coefficient l c).X (ProjectiveLine Y) ≅
        (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).ι) ∧
      Nonempty (eY.functor ⋙ rationalLocalizingInclusion (coefficient l c).X Y ≅
        (localizingClosureProEtale (coefficient l c).X Y).ι) ∧
      Nonempty (G ⋙ eP.functor ≅ eY.functor ⋙ exceptional l c k p hpl Y) := by
  let Λ := (coefficient.{u} l c).X
  let P := localizingClosureProEtale Λ (ProjectiveLine Y)
  let Q := localizingClosureProEtale Λ Y
  let c₀ : Compactification.BoundaryCompactification (ProjectiveLine Y ↘ Y) :=
    ⟨⟨Compactification.ofIsProper (ProjectiveLine Y ↘ Y), inferInstance⟩⟩
  have : Fact (ringChar k).Prime := ⟨by rw [ringChar.eq k p]; exact Fact.out⟩
  have : Fact (ringChar k ≠ l) := ⟨by rw [ringChar.eq k p]; exact hpl⟩
  have : LocallyOfFiniteType (ProjectiveLine Y ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
  have : QuasiCompact (ProjectiveLine Y ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
  have : IsSeparated (ProjectiveLine Y ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
  have : (ProjectiveLine Y ↘ Y).IsOver (Spec (.of k)) := ⟨rfl⟩
  obtain ⟨φ, _⟩ := compactification_coherence_cocycle Λ l
    (coefficientAdmissible l c) k (ProjectiveLine Y ↘ Y)
  let e₀ : CondensedRing.rightDerivedLowerShriekOfCompactification Λ c₀.obj.obj ≅
      moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y) :=
    Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ (ProjectiveLine Y)) _ ≪≫
      Functor.leftUnitor _
  let e : localizingLowerShriek Λ compactification.obj.obj h ⋙ Q.ι ≅
      P.ι ⋙ moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y) :=
    φ compactification c₀ ≪≫ Functor.isoWhiskerLeft P.ι e₀
  exact compareRightAdjointsOnEqualSubcategories P _ Q _
    (coefficientLocalizingEquality l c (ProjectiveLine Y))
    (coefficientLocalizingEquality l c Y)
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y))
    (fun M ↦ (localizingPreservation l c k p hpl Y).1 M.obj M.property)
    (localizingLowerShriek Λ compactification.obj.obj h) e
    (exceptional l c k p hpl Y) adj G adjG

-- Normalize ambient components before assembling the adjunction.
/-- Both kernel computations and integration identities, the prescribed adjunction, and
comparison with every Brown exceptional adjoint for a chosen compactification, for the trace
family specified by `Reference`. -/
theorem rationalP1_triangle
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (_hcompletion : DiagonalCompletionSpec l (diagonalSurface Y) D)
    (_hsystem : DiagonalCycleSystemSpec l Y hY D)
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (_hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ)
    (family : Family l Y) (_reference : Reference l Y δ family) :
    (∀ M : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y),
      ((push l c k p hpl Y).map ((unitCounit l c k p hpl Y family).1.app M) ≫
        (unitCounit l c k p hpl Y family).2.app ((push l c k p hpl Y).obj M)).hom =
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (diagonalIntegralAction (coefficient l c).X Y (line l c)
          (diagram l c Y family) 0 M.obj)) ∧
    (∀ K : rationalLocalizingCategory (coefficient l c).X Y,
      ((unitCounit l c k p hpl Y family).1.app ((exceptional l c k p hpl Y).obj K) ≫
        (exceptional l c k p hpl Y).map ((unitCounit l c k p hpl Y family).2.app K)).hom =
      diagonalIntegralAction (coefficient l c).X Y (line l c) (diagram l c Y family) 1
        ((exceptional l c k p hpl Y).obj K).obj) ∧
    (∀ M : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y),
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (diagonalIntegralAction (coefficient l c).X Y (line l c)
          (diagram l c Y family) 0 M.obj) = 𝟙 _) ∧
    (∀ K : rationalLocalizingCategory (coefficient l c).X Y,
      diagonalIntegralAction (coefficient l c).X Y (line l c) (diagram l c Y family) 1
        ((exceptional l c k p hpl Y).obj K).obj = 𝟙 _) ∧
    (∃ adj : push l c k p hpl Y ⊣ exceptional l c k p hpl Y,
      adj.unit = (unitCounit l c k p hpl Y family).1 ∧
      adj.counit = (unitCounit l c k p hpl Y family).2) ∧
    (∀ (compactification : Compactification.BoundaryCompactification (ProjectiveLine Y ↘ Y))
      (h : ∀ A, localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y) A →
        localizingClosureProEtale (coefficient l c).X Y
          ((CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient l c).X
            compactification.obj.obj).obj A))
      (G : (localizingClosureProEtale (coefficient l c).X Y).FullSubcategory ⥤
        (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).FullSubcategory)
      (_adjG : localizingLowerShriek (coefficient l c).X compactification.obj.obj h ⊣ G),
      ∃ (eP : (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).FullSubcategory ≌
          rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y))
        (eY : (localizingClosureProEtale (coefficient l c).X Y).FullSubcategory ≌
          rationalLocalizingCategory (coefficient l c).X Y),
        Nonempty (eP.functor ⋙ rationalLocalizingInclusion (coefficient l c).X (ProjectiveLine Y) ≅
          (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).ι) ∧
        Nonempty (eY.functor ⋙ rationalLocalizingInclusion (coefficient l c).X Y ≅
          (localizingClosureProEtale (coefficient l c).X Y).ι) ∧
        Nonempty (G ⋙ eP.functor ≅ eY.functor ⋙ exceptional l c k p hpl Y)) := by
  have hnorm : UnitCounitNormalized l c k p hpl Y family
      (unitCounit l c k p hpl Y family) :=
    (unitCounit_existsUnique l c k p hpl Y family).exists.choose_spec
  obtain ⟨h₁, h₂⟩ := rationalP1_kernel_contractions l c k p hpl Y hY D _hcompletion
    _hsystem δ _hδ family _reference (unitCounit l c k p hpl Y family) hnorm
  have h₁' (M : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y)) :
      ((push l c k p hpl Y).map ((unitCounit l c k p hpl Y family).1.app M) ≫
        (unitCounit l c k p hpl Y family).2.app ((push l c k p hpl Y).obj M)).hom =
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (diagonalIntegralAction (coefficient l c).X Y (line l c)
          (diagram l c Y family) 0 M.obj) := by
    simpa only [diagonalIntegralAction, diagonalIntegral, ite_eq_left (rfl : (0 : Fin 2) = 0),
      ite_true, Category.assoc] using h₁ M
  have h₂' (K : rationalLocalizingCategory (coefficient l c).X Y) :
      ((unitCounit l c k p hpl Y family).1.app ((exceptional l c k p hpl Y).obj K) ≫
        (exceptional l c k p hpl Y).map ((unitCounit l c k p hpl Y family).2.app K)).hom =
      diagonalIntegralAction (coefficient l c).X Y (line l c) (diagram l c Y family) 1
        ((exceptional l c k p hpl Y).obj K).obj := by
    simpa only [diagonalIntegralAction, diagonalIntegral,
      ite_eq_right (by decide : (1 : Fin 2) ≠ 0),
      Category.assoc] using h₂ K
  have hi₁ (M : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y)) :
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (diagonalIntegralAction (coefficient l c).X Y (line l c)
          (diagram l c Y family) 0 M.obj) = 𝟙 _ := by
    rw [diagonalIntegralAction_eq_id, CategoryTheory.Functor.map_id]
  have hi₂ (K : rationalLocalizingCategory (coefficient l c).X Y) :
      diagonalIntegralAction (coefficient l c).X Y (line l c) (diagram l c Y family) 1
        ((exceptional l c k p hpl Y).obj K).obj = 𝟙 _ :=
    diagonalIntegralAction_eq_id _ _ _ _ _ _
  have ht₁ (M : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y)) :
      (push l c k p hpl Y).map ((unitCounit l c k p hpl Y family).1.app M) ≫
        (unitCounit l c k p hpl Y family).2.app ((push l c k p hpl Y).obj M) = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    exact (h₁' M).trans (hi₁ M)
  have ht₂ (K : rationalLocalizingCategory (coefficient l c).X Y) :
      (unitCounit l c k p hpl Y family).1.app ((exceptional l c k p hpl Y).obj K) ≫
        (exceptional l c k p hpl Y).map ((unitCounit l c k p hpl Y family).2.app K) = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    exact (h₂' K).trans (hi₂ K)
  let core : Adjunction.CoreUnitCounit (push l c k p hpl Y) (exceptional l c k p hpl Y) := {
    unit := (unitCounit l c k p hpl Y family).1
    counit := (unitCounit l c k p hpl Y family).2
    left_triangle := by
      apply NatTrans.ext
      funext M
      simpa using ht₁ M
    right_triangle := by
      apply NatTrans.ext
      funext K
      simpa using ht₂ K }
  let adj := Adjunction.mkOfUnitCounit core
  refine ⟨h₁', h₂', hi₁, hi₂, ⟨adj, rfl, rfl⟩, ?_⟩
  · intro compactification h G adjG
    exact brownComparison l c k p hpl Y adj compactification h G adjG

end AlgebraicGeometry.ProEtale.RationalP1
