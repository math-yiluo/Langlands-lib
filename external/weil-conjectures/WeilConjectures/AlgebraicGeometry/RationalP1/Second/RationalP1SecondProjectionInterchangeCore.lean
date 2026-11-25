/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1TensorShiftNaturality

/-! The generic strength/projection interchange used by the rational P1 calculation.

This isolates the monoidal coherence calculation from the fixed projective-line
projection maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

private theorem shiftedTail_naturality
    {C : Type u} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (A T P Q : C) (z : P ⟶ Q) :
    ((A ⊗ T) ◁ z) ≫ (α_ A T Q).hom ≫
        A ◁ (β_ T Q).hom ≫ (α_ A Q T).inv =
      (α_ A T P).hom ≫ A ◁ (β_ T P).hom ≫
        (α_ A P T).inv ≫ ((A ◁ z) ▷ T) := by
  rw [associator_naturality_right_assoc]
  rw [← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_right,
    whiskerLeft_comp_assoc]
  rw [associator_inv_naturality_middle]

private theorem conjugatedTail_naturality
    {C : Type u} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {A P Q T X Y B : C} (a : A ⊗ T ≅ X) (b : (A ⊗ Q) ⊗ T ≅ Y)
    (μ : A ⊗ P ≅ B) (z : P ⟶ Q) :
    (a.inv ▷ P) ≫ (α_ A T P).hom ≫
        A ◁ (β_ T P).hom ≫ (α_ A P T).inv ≫
        (μ.hom ▷ T) ≫ (μ.inv ▷ T) ≫ ((A ◁ z) ▷ T) ≫ b.hom =
      (X ◁ z) ≫ (a.inv ▷ Q) ≫ (α_ A T Q).hom ≫
        A ◁ (β_ T Q).hom ≫ (α_ A Q T).inv ≫ b.hom := by
  slice_lhs 5 6 => rw [← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight]
  simp only [Category.id_comp]
  rw [← reassoc_of% (shiftedTail_naturality A T P Q z)]
  rw [whisker_exchange_assoc]

attribute [local irreducible] coefficient line twist projectionMap tensorShiftIso
attribute [local irreducible] secondLineComparison twistProjectionMap
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

/-- The strength tail with an arbitrary second tensor factor. It is the
monoidal tensor/shift coherence after the first factor has been shifted. -/
@[irreducible]
def secondTraceStrengthTail
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : Modules Λ (ProjectiveLine Y))
    (K : DerivedCategory (Modules Λ Y))
    (Q : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (twist Λ (ProjectiveLine Y) L).obj
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K) ⊗ Q ⟶
      (twist Λ (ProjectiveLine Y) L).obj
        (((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K) ⊗ Q) := by
  letI := secondTraceBraided Λ Y
  let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj L)
    ⟦(2 : ℤ)⟧
  exact
    (tensorShiftIso Λ (ProjectiveLine Y) L (F.obj K)).inv ▷ Q ≫
      (α_ (F.obj K) T Q).hom ≫
      (tensorIso (Iso.refl _) (β_ T Q)).hom ≫
      (α_ (F.obj K) Q T).inv ≫
      (tensorShiftIso Λ (ProjectiveLine Y) L (F.obj K ⊗ Q)).hom

-- The expanded monoidal coherence proof needs a larger elaboration budget.
/-- Monoidal strength naturality for an arbitrary morphism in the second factor.
The statement is independent of the projective-line projection and is the
coherence calculation needed before inserting the fixed projection maps. -/
theorem secondTraceStrength_naturality
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K V : DerivedCategory (Modules (coefficient l c).X Y))
    (Q R Z : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (z : (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj V ⟶ Q)
    (q : ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K) ⊗ Q ⟶ R)
    (τ : (twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj R ⟶ Z) :
    (secondTraceStrength (coefficient l c).X Y (line l c (ProjectiveLine Y)) K V).hom ≫
        (twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).map
          ((secondTraceTensorIso (coefficient l c).X Y K V).inv ≫
            ((moduleObjectDerivedPullback (coefficient l c).X
              (ProjectiveLine Y ↘ Y)).obj K ◁ z) ≫ q) ≫ τ =
      (((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)) ◁ z) ≫
        secondTraceStrengthTail (coefficient l c).X Y (line l c (ProjectiveLine Y)) K Q ≫
        (twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).map q ≫ τ := by
  let Λ := (coefficient l c).X
  let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let H := twist Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))
  let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
    (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧
  letI := secondTracePullMonoidal Λ Y
  letI := secondTraceBraided Λ Y
  have hstrength :
      (secondTraceStrength Λ Y (line l c (ProjectiveLine Y)) K V).hom ≫
          H.map ((secondTraceTensorIso Λ Y K V).inv ≫ (F.obj K ◁ z)) =
        (H.obj (F.obj K) ◁ z) ≫
          secondTraceStrengthTail Λ Y (line l c (ProjectiveLine Y)) K Q := by
    rw [Functor.map_comp]
    simp only [secondTraceStrength, secondTraceStrengthTail, secondTraceTensorIso,
      secondTraceSwap, Iso.trans_hom, Iso.symm_hom, tensorIso, Iso.refl_hom,
      Functor.Monoidal.μIso]
    dsimp only [H, F]
    simp only [Category.assoc]
    rw [← reassoc_of% (tensorShiftIso_naturality Λ (ProjectiveLine Y)
      (line l c (ProjectiveLine Y))
      (Functor.OplaxMonoidal.δ
        (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)) K V))]
    rw [← tensorShiftIso_naturality (coefficient l c).X
      (ProjectiveLine Y)
      (line l c (ProjectiveLine Y))
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K ◁ z)]
    simp only [tensorHom_id, Category.id_comp]
    simpa only [secondTraceTensorIso, Functor.Monoidal.μIso, tensorIso,
      Iso.refl_hom, tensorHom_id, id_tensorHom] using
      conjugatedTail_naturality
      (tensorShiftIso Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K))
      (tensorShiftIso Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))
        (((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K) ⊗ Q))
      (secondTraceTensorIso Λ Y K V) z
  have hstrength' :
      (secondTraceStrength (coefficient l c).X Y (line l c (ProjectiveLine Y)) K V).hom ≫
          (twist (coefficient l c).X (ProjectiveLine Y)
            (line l c (ProjectiveLine Y))).map
            ((secondTraceTensorIso (coefficient l c).X Y K V).inv ≫
              ((moduleObjectDerivedPullback (coefficient l c).X
                (ProjectiveLine Y ↘ Y)).obj K ◁ z)) =
        (((twist (coefficient l c).X (ProjectiveLine Y)
          (line l c (ProjectiveLine Y))).obj
          ((moduleObjectDerivedPullback (coefficient l c).X
            (ProjectiveLine Y ↘ Y)).obj K)) ◁ z) ≫
          secondTraceStrengthTail (coefficient l c).X Y
            (line l c (ProjectiveLine Y)) K Q := by
    simpa only [Λ, F, H] using hstrength
  calc
    (secondTraceStrength (coefficient l c).X Y (line l c (ProjectiveLine Y)) K V).hom ≫
          (twist (coefficient l c).X (ProjectiveLine Y)
            (line l c (ProjectiveLine Y))).map
            ((secondTraceTensorIso (coefficient l c).X Y K V).inv ≫
              ((moduleObjectDerivedPullback (coefficient l c).X
                (ProjectiveLine Y ↘ Y)).obj K ◁ z) ≫ q) ≫ τ =
        ((secondTraceStrength (coefficient l c).X Y
          (line l c (ProjectiveLine Y)) K V).hom ≫
          (twist (coefficient l c).X (ProjectiveLine Y)
            (line l c (ProjectiveLine Y))).map
            ((secondTraceTensorIso (coefficient l c).X Y K V).inv ≫
              ((moduleObjectDerivedPullback (coefficient l c).X
                (ProjectiveLine Y ↘ Y)).obj K ◁ z))) ≫
          (twist (coefficient l c).X (ProjectiveLine Y)
            (line l c (ProjectiveLine Y))).map q ≫ τ := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by rw [hstrength']; simp only [Category.assoc]

end AlgebraicGeometry.ProEtale.RationalP1
