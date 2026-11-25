/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernP2HomologyCriterion
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # The two scalar unit/Chern splittings
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line diagram trace singleUnitIso
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

private theorem isIso_biprod_desc_left
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z)
    (hY : IsZero (F.obj Y)) (ha : IsIso (F.map a)) :
    IsIso (F.map (biprod.desc a b)) := by
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hinl : IsIso (biprod.inl : F.obj X ⟶ F.obj X ⊞ F.obj Y) := by
    refine ⟨⟨biprod.fst, by simp, ?_⟩⟩
    apply biprod.hom_ext'
    · simp
    · exact hY.eq_of_src _ _
  have hcomp : (F.mapBiprod X Y).inv ≫ F.map (biprod.desc a b) =
      biprod.desc (F.map a) (F.map b) := by
    apply biprod.hom_ext' <;>
      simp only [Functor.mapBiprod_inv, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
        ← Functor.map_comp, biprod.inl_desc, biprod.inr_desc]
  have hdesc : IsIso (biprod.desc (F.map a) (F.map b)) := by
    have hcomp' : IsIso (biprod.inl ≫ biprod.desc (F.map a) (F.map b)) := by
      simpa using ha
    exact IsIso.of_isIso_comp_left biprod.inl _
  have hmap : IsIso ((F.mapBiprod X Y).inv ≫ F.map (biprod.desc a b)) := by
    rw [hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.mapBiprod X Y).inv _

private theorem isIso_biprod_desc_right
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z)
    (hX : IsZero (F.obj X)) (hb : IsIso (F.map b)) :
    IsIso (F.map (biprod.desc a b)) := by
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hinr : IsIso (biprod.inr : F.obj Y ⟶ F.obj X ⊞ F.obj Y) := by
    refine ⟨⟨biprod.snd, by simp, ?_⟩⟩
    apply biprod.hom_ext'
    · exact hX.eq_of_src _ _
    · simp
  have hcomp : (F.mapBiprod X Y).inv ≫ F.map (biprod.desc a b) =
      biprod.desc (F.map a) (F.map b) := by
    apply biprod.hom_ext' <;>
      simp only [Functor.mapBiprod_inv, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
        ← Functor.map_comp, biprod.inl_desc, biprod.inr_desc]
  have hdesc : IsIso (biprod.desc (F.map a) (F.map b)) := by
    have hcomp' : IsIso (biprod.inr ≫ biprod.desc (F.map a) (F.map b)) := by
      simpa using hb
    exact IsIso.of_isIso_comp_left biprod.inr _
  have hmap : IsIso ((F.mapBiprod X Y).inv ≫ F.map (biprod.desc a b)) := by
    rw [hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.mapBiprod X Y).inv _

private theorem isIso_biprod_desc_of_homology
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {U V K : DerivedCategory C} (a : V ⟶ K) (b : U ⟶ K)
    (hU : ∀ n : ℤ, n ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor C n).obj U))
    (hV : ∀ n : ℤ, n ≠ -2 → IsZero
      ((DerivedCategory.homologyFunctor C n).obj V))
    (hK : ∀ n : ℤ, n ≠ 0 → n ≠ -2 → IsZero
      ((DerivedCategory.homologyFunctor C n).obj K))
    (hb : IsIso ((DerivedCategory.homologyFunctor C 0).map b))
    (ha : IsIso ((DerivedCategory.homologyFunctor C (-2)).map a)) :
    IsIso (biprod.desc a b) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  let H := DerivedCategory.homologyFunctor C n
  by_cases hn0 : n = 0
  · subst n
    have hV0 : IsZero ((DerivedCategory.homologyFunctor C 0).obj V) :=
      hV 0 (by norm_num)
    exact isIso_biprod_desc_right (DerivedCategory.homologyFunctor C 0) a b hV0 hb
  · by_cases hn2 : n = -2
    · subst n
      have hU2 : IsZero ((DerivedCategory.homologyFunctor C (-2)).obj U) :=
        hU (-2) (by norm_num)
      exact isIso_biprod_desc_left (DerivedCategory.homologyFunctor C (-2)) a b hU2 ha
    · have hzU := hU n hn0
      have hzV := hV n hn2
      have hzK := hK n hn0 hn2
      apply IsZero.isIso _ hzK
      let : PreservesBinaryBiproducts H :=
        preservesBinaryBiproducts_of_preservesBiproducts H
      apply IsZero.of_iso _ (H.mapBiprod V U)
      rw [IsZero.iff_id_eq_zero]
      apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
        first | exact hzU.eq_of_src _ _ | exact hzV.eq_of_src _ _

/-- The scalar second-projection unit/Chern splitting isomorphism. -/
theorem scalar_p2_chern_splitting
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧))
    (ha : CompletedChernNormalized l r.tq.toPresentation a)
    (b : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      r.t₂.Rc.R.obj ((DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧))
    (hb : CompletedChernNormalized l r.t₂.toPresentation b) :
    let Λ := (coefficient l c).X
    let L := line l c
    let T := fun X : Scheme.{u} ↦
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (L X)) ⟦(2 : ℤ)⟧
    let uq := scalarTwistedUnit Λ (ProjectiveLine Y ↘ Y) (T Y) (T (ProjectiveLine Y))
      (scalarQLineIso l c k p hpl Y)
    let u₂ := scalarTwistedUnit Λ (secondProjection Y)
      (T (ProjectiveLine Y)) (T (diagonalSurface Y)) (secondLineComparison l c k p hpl Y)
    let cq := scalarQChern l c Y r a
    let c₂ := scalarP2Chern l c Y r b
    IsIso (biprod.desc u₂ c₂) := by
  let Λ := (coefficient l c).X
  let T := fun X : Scheme.{u} ↦
    ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (line l c X)) ⟦(2 : ℤ)⟧
  let u₂ := scalarTwistedUnit Λ (secondProjection Y) (T (ProjectiveLine Y))
    (T (diagonalSurface Y)) (secondLineComparison l c k p hpl Y)
  let c₂ := scalarP2Chern l c Y r b
  obtain ⟨hU, hV, hK, hb, ha⟩ := scalar_p2_chern_homology_criterion
    l c k p hpl Y δ family r a ha b hb
  exact isIso_biprod_desc_of_homology u₂ c₂ hU hV hK hb ha

end AlgebraicGeometry.ProEtale.RationalP1
