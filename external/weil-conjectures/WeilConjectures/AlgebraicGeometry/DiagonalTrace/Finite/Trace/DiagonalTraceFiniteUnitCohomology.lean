/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels

import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceUnitArrowComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite cohomology of the projective-line coefficient unit

Source: blueprint latest, diagonal-tower trace proof (1), and projective-line
cohomology (G2). Only the coefficient unit and degrees other than two occur here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian in
section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

private theorem isIso_map_inl_of_isZero_right
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (U V : C) [HasBinaryBiproduct U V]
    (hV : IsZero (F.obj V)) : IsIso (F.map (biprod.inl : U ⟶ U ⊞ V)) := by
  have hzero : F.map (biprod.snd ≫ biprod.inr : U ⊞ V ⟶ U ⊞ V) = 0 := by
    rw [F.map_comp, hV.eq_of_src (F.map biprod.inr) 0, comp_zero]
  refine ⟨⟨F.map biprod.fst, ?_, ?_⟩⟩
  · rw [← F.map_comp, biprod.inl_fst, F.map_id]
  · have ht := congrArg F.map (biprod.total (X := U) (Y := V))
    rw [F.map_add, hzero, add_zero, F.map_id, F.map_comp] at ht
    exact ht

private theorem isIso_map_of_arrow_iso
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U V U' V' : C} {f : U ⟶ V} {g : U' ⟶ V'}
    (i : Arrow.mk f ≅ Arrow.mk g) (hf : IsIso (F.map f)) : IsIso (F.map g) := by
  let : IsIso (F.map f) := hf
  rw [Arrow.iso_w' i, F.map_comp, F.map_comp]
  infer_instance

private theorem component_cohomology
    (l : ℕ) (hl : l.Prime) (r : ℕ) (hr : 0 < r)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : ((l ^ r : ℕ) : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit ((l ^ r : ℕ) : Γ(S, ⊤)))
    {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C] [HasDerivedCategory.{w} C]
    (F : Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A) ⥤ C)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (q : ℤ) (hq : q ≠ 2) :
    IsIso ((F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor _ q).map
      ((geoP1Comparison A S).map (Etale.p1DecompositionUnit A S) ≫
        geoP1PushComparison A (ProjectiveLine S ↘ S)
          (Etale.ordinaryFiniteUnit A (ProjectiveLine S)))) := by
  let H := F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor _ q
  have hp : 0 < l ^ r := pow_pos hl.pos _
  obtain ⟨_, hd, _⟩ := geoP1Cohomology l hl r hr A hA
  have hzero : IsZero (H.obj (geoP1Twist A (l ^ r) hA S (-1) (-2))) := by
    apply F.isZero_homologyFunctor_mapDerivedCategory_obj
    apply Functor.isZero_homologyFunctor_mapDerivedCategory_obj
      (comparisonUpperStar (ModuleCat.{u + 1} A) S)
    have hge : (Etale.p1DecompositionTwist A (l ^ r) hA S (-1) (-2)).IsGE 2 :=
      DerivedCategory.TStructure.t.isGE_shift _ 0 (-2) 2 (by decide)
    have hle : (Etale.p1DecompositionTwist A (l ^ r) hA S (-1) (-2)).IsLE 2 :=
      DerivedCategory.TStructure.t.isLE_shift _ 0 (-2) 2 (by decide)
    rcases lt_or_gt_of_ne hq with hlt | hgt
    · exact DerivedCategory.isZero_of_isGE _ 2 q hlt (hX := hge)
    · exact DerivedCategory.isZero_of_isLE _ 2 q hgt (hX := hle)
  have : IsIso (H.map (biprod.inl : geoP1Unit A S ⟶
      geoP1Unit A S ⊞ geoP1Twist A (l ^ r) hA S (-1) (-2))) :=
    isIso_map_inl_of_isZero_right H _ _ hzero
  have : IsIso (geoP1DecompositionMap A (l ^ r) hp hA S hS) := (hd S hS).1
  have hcomponent : biprod.inl ≫ geoP1DecompositionMap A (l ^ r) hp hA S hS =
      (geoP1Comparison A S).map (Etale.p1DecompositionUnit A S) ≫
        geoP1PushComparison A (ProjectiveLine S ↘ S)
          (Etale.ordinaryFiniteUnit A (ProjectiveLine S)) := by
    simp only [geoP1DecompositionMap, geoP1SumComparison, biprod.inl_desc_assoc,
      ← Functor.map_comp_assoc, Etale.p1DecompositionMap, biprod.inl_desc]
  rw [← hcomponent]
  change IsIso (H.map _)
  rw [H.map_comp]
  infer_instance

/-- The evaluated coefficient unit is an isomorphism on cohomology outside degree two.

Source: `sk-prop-diagonal-tower-trace.proof.md` (1), the unit component of (G2) in
`lemma-cohomology-projective-line-trace`.
(blueprint: lem-sfb-diagonal-trace-finite-unit-cohomology).

Proof: set A to the actual quotient of the ring of integers of E by l^(n+1).
It is finite by b.finite, and coefficient_annihilates makes it an admissible
coefficient ring for (G2). The exponent is positive and invertible on S by hS.
The normalized evaluation comparison identifies the derived direct image of
the system coefficient unit with the ordinary A-coefficient direct image.
The coefficient-pullback normalization sends each constant section to itself;
thus the evaluated adjunction unit is the ordinary coefficient unit, not a
scalar multiple of it. Realize fixed-scalar sheaves as modules over the
constant ring sheaf; this is an exact equivalence, so preserves cohomology
and reflects its isomorphisms. Transport along e and he to the projective-line
projection. In (G2) the first injection is precisely this unit. Its other
summand A(-1)[-2] has cohomology only in degree two. In every degree q different
from two the first injection, followed by (G2), is therefore an isomorphism.
Transport this assertion back through the exact coefficient comparisons.
No Chern data, trace, or system splitting is used. This also covers negative
q, where both cohomology sheaves are zero, and the zero coefficient ring. -/
theorem diagonalTrace_finite_unit_cohomology
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (b : SpTowerShriek.Base l E) {f : X ⟶ S}
    (e : X ≅ ProjectiveLine S) (he : e.hom ≫ (ProjectiveLine S ↘ S) = f)
    (g : SpTowerShriek.Geometry l E b f) (c : CoefficientPullback l E b f g)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ) (q : ℤ) (hq : q ≠ 2) :
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((SpTowerShriek.Ev l E S n).map (unitArrow l E c))) := by
  let : Finite (SpTowerShriek.R l E n) := b.finite n
  let A := ULift.{u + 1} (SpTowerShriek.R l E n)
  let F := (Scheme.sfIntrinsicModuleEquivalence S (SpTowerShriek.R l E n)).functor
  have hA : ((l ^ (n + 1) : ℕ) : A) = 0 :=
    ULift.ext (coefficient_annihilates l E n)
  have hpow : IsUnit ((l ^ (n + 1) : ℕ) : Γ(S, ⊤)) := by
    simpa only [Nat.cast_pow] using hS.pow (n + 1)
  have hi : IsIso ((F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor _ q).map
      ((geoP1Comparison A S).map (Etale.p1DecompositionUnit A S) ≫
        geoP1PushComparison A (ProjectiveLine S ↘ S)
          (Etale.ordinaryFiniteUnit A (ProjectiveLine S)))) :=
    component_cohomology l (Fact.out : l.Prime) (n + 1) (Nat.zero_lt_succ n)
      A hA S hpow F q hq
  obtain ⟨i⟩ := diagonalTrace_unit_arrow_comparison l E b e he g c n
  exact isIso_map_of_arrow_iso (DerivedCategory.homologyFunctor _ q) i hi

end AlgebraicGeometry.ProEtale.DiagonalTrace

end
