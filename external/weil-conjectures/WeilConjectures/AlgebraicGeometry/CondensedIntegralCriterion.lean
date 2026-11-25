/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.List.TFAE

import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsStacksBlueprint
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLocalStructure
import WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
import WeilConjectures.AlgebraicGeometry.Integral.IntegralPointComplexHomology

/-! # The four-way condensed integral constructibility criterion

Source: current blueprint, sec-proetale-coefficients/sk-prop-integral-criterion,
statement and all four proof paragraphs (blueprint: lem-fix-condensed-integral-criterion).

All categories and tensors are ordinary unbounded internal-module derived categories.
A finite free module over the condensed integer ring on the point is a finite sum of
its regular module. Maps between these sums are matrices over its sections on the
one-point profinite set, namely the scalar ring O_E. Thus a bounded complex of such
modules is precisely the continuous scalar realization of a bounded finite free
O_E-complex. Pulling it from the point gives B_U tensor over constant O_E with that
scalar complex. The matrices are chosen before the pullback to U, excluding arbitrary
B_U-valued matrices. This uses the existing finite-free and pullback constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Canonical scalar-complex realization on a chart: pull back the finite free point
complex termwise and localize. The additive and exact structures are supplied by the
existing finite-limit and left-adjoint properties of the inverse image from the point.
Source: current blueprint proposition-integral-constructibility-criterion, condition (3)
(blueprint: lem-fix-condensed-integral-criterion). -/
noncomputable def condensedIntegralCriterionRealization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    CochainComplex
        (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          (DerivedNakayama.integerRing l E)) ℤ ⥤
      DerivedCategory (AdicCompletion.Modules l E X) := by
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    have : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
      AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
    dsimp [pointUpperStar, Functor.sheafPullbackConstruction.sheafPullback]
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  have : PreservesFiniteLimits (DerivedNakayama.pullback l E X) := by
    dsimp [DerivedNakayama.pullback]
    infer_instance
  have : (DerivedNakayama.pullback l E X).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact (DerivedNakayama.pullback l E X).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

private theorem condensedIntegralCriterionRealization_obj_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (P : CochainComplex
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (DerivedNakayama.integerRing l E)) ℤ) :
    (condensedIntegralCriterionRealization l E X).obj P =
      DerivedCategory.Q.obj
        (((CondensedRing.upperStarFromPointMod
            (DerivedNakayama.integerRing l E) X).mapHomologicalComplex (.up ℤ)).obj P) := by
  rfl

attribute [local irreducible] upperStarFromPoint DerivedCategory.Q
  CategoryTheory.Functor.mapDerivedCategory condensedIntegralCriterionRealization

-- Cohomology transport is independent of the concrete coefficient definitions.
private theorem constructible_of_stratified_point_complexes
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)))
    (h : ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a), ∀ i : U.I₀,
        ∃ (P : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R) ℤ)
          (b c : ℤ),
          P.IsStrictlyGE b ∧ P.IsStrictlyLE c ∧
          (∀ q : ℤ, Mod.IsFinitelyPresented R (P.homology q)) ∧
          Nonempty
            ((CondensedRing.upperStar R (U.f i ≫ S.immersion a)).mapDerivedCategory.obj K ≅
              DerivedCategory.Q.obj
                (((CondensedRing.upperStarFromPointMod R (U.X i)).mapHomologicalComplex
                  (.up ℤ)).obj P))) :
    ∀ q, IsConstantModelConstructible R X
      ((DerivedCategory.homologyFunctor _ q).obj K) := by
  classical
  obtain ⟨S, hS⟩ := h
  intro q
  rw [IsConstantModelConstructible, ite_eq_left
    (show CompactSpace X ∧ QuasiSeparatedSpace X from ⟨inferInstance, inferInstance⟩)]
  refine ⟨S, fun a ↦ ?_⟩
  obtain ⟨U, hU⟩ := hS a
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, b, c, hb, hc, hf, ⟨e⟩⟩ := hU i
  let T := CondensedRing.upperStar R (U.f i ≫ S.immersion a)
  let F := CondensedRing.upperStarFromPointMod R (U.X i)
  refine ⟨P.homology q, hf q, ⟨?_⟩⟩
  exact ((CondensedRing.upperStarComp R (U.f i) (S.immersion a)).app
      ((DerivedCategory.homologyFunctor _ q).obj K)).symm ≪≫
    (T.mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
    (F.mapHomologicalComplexHomologyIso (.up ℤ) q).app P

-- This isolates the homology comparison from the finite-cover index calculations.
private theorem homology_isZero_of_point_model
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (X Y : Scheme.{u}) (g : Y ⟶ X)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)))
    (P : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R) ℤ)
    (b c : ℤ) [P.IsStrictlyGE b] [P.IsStrictlyLE c]
    (e : (CondensedRing.upperStar R g).mapDerivedCategory.obj K ≅
      DerivedCategory.Q.obj
        (((CondensedRing.upperStarFromPointMod R Y).mapHomologicalComplex (.up ℤ)).obj P))
    (q : ℤ) (hq : q < b ∨ c < q) :
    IsZero ((CondensedRing.upperStar R g).obj
      ((DerivedCategory.homologyFunctor _ q).obj K)) := by
  let T := CondensedRing.upperStar R g
  let F := CondensedRing.upperStarFromPointMod R Y
  have hzP : IsZero (P.homology q) := by
    rcases hq with hq | hq
    · exact (P.exactAt_of_isGE b q hq).isZero_homology
    · exact (P.exactAt_of_isLE c q hq).isZero_homology
  exact (F.map_isZero hzP).of_iso
    ((T.mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
      (F.mapHomologicalComplexHomologyIso (.up ℤ) q).app P)

-- Keep the pullback-forget comparison separate from cover refinements.
private theorem underlying_isZero_of_factorization
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (X Y Z : Scheme.{u})
    (g : Y ⟶ X) (f : Z ⟶ Y) (h : Z ⟶ X) (eh : h = f ≫ g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (hz : IsZero ((CondensedRing.upperStar R g).obj M)) :
    IsZero ((Scheme.proEtaleSheafInverseImage h Ab.{u + 1}).obj M.X) := by
  have hzG : IsZero ((CondensedRing.upperStar R h).obj M) :=
    ((CondensedRing.upperStar R f).map_isZero hz).of_iso
      (eqToIso (congrArg (fun k ↦ (CondensedRing.upperStar R k).obj M) eh) ≪≫
        (CondensedRing.upperStarComp R f g).app M)
  exact ((Mod.forget _).map_isZero hzG).of_iso
    (CondensedRing.upperStarObjXIso R h M).symm

-- Work with an abstract family of modules, independently of its derived origin.
private theorem uniform_bounds_of_stratified_local_bounds
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (X : Scheme.{u}) [IsNoetherian X]
    (S : Scheme.Stratification X)
    (U : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))
    (M : ℤ → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (b c : ∀ a : Fin S.n, (U a).I₀ → ℤ)
    (hv : ∀ a i q, q < b a i ∨ c a i < q →
      IsZero ((CondensedRing.upperStar R ((U a).f i ≫ S.immersion a)).obj (M q)))
    (V : ∀ a : Fin S.n, Scheme.AffineCover.{u} (@WeaklyEtale) (S.domain a))
    (f : ∀ a : Fin S.n, (V a).cover ⟶ (U a).forgetQc)
    (hfin : ∀ a : Fin S.n, Finite (V a).I₀) :
    ∃ r s : ℤ, ∀ q, q < r ∨ s < q → IsZero (M q) := by
  classical
  have : ∀ a : Fin S.n, TopologicalSpace.NoetherianSpace (S.domain a) := fun a ↦
    (S.immersion a).isEmbedding.noetherianSpace
  let : ∀ a : Fin S.n, Finite (V a).I₀ := hfin
  have hqc (a : Fin S.n) : QuasiCompactCover (V a).cover.toPreZeroHypercover := by
    have (i : (V a).I₀) : QuasiCompact ((V a).cover.f i) :=
      quasiCompact_of_compactSpace _
    have : Finite (V a).cover.I₀ := hfin a
    exact QuasiCompactCover.of_finite
  let := hqc
  let C (a : Fin S.n) := Scheme.Cover.ofQuasiCompactCover (V a).cover
  obtain ⟨r, hr⟩ := (Set.finite_range
    (fun p : (a : Fin S.n) × (V a).I₀ ↦ b p.1 ((f p.1).s₀ p.2))).bddBelow
  obtain ⟨s, hs⟩ := (Set.finite_range
    (fun p : (a : Fin S.n) × (V a).I₀ ↦ c p.1 ((f p.1).s₀ p.2))).bddAbove
  refine ⟨r, s, fun q hq ↦ ?_⟩
  apply CondensedRing.isZero_of_isZero_X R
  apply Scheme.proEtale_isZero_of_stratum_cover X S C
  intro a j
  let i := (f a).s₀ j
  have hrj : r ≤ b a i :=
    hr (Set.mem_range_self (⟨a, j⟩ : (a : Fin S.n) × (V a).I₀))
  have hsj : c a i ≤ s :=
    hs (Set.mem_range_self (⟨a, j⟩ : (a : Fin S.n) × (V a).I₀))
  have hzT := hv a i q (hq.imp (fun h ↦ h.trans_le hrj) (fun h ↦ hsj.trans_lt h))
  apply underlying_isZero_of_factorization R X ((U a).X i) ((C a).X j)
    ((U a).f i ≫ S.immersion a) ((f a).h₀ j)
    ((C a).f j ≫ S.immersion a) ?_ (M q) hzT
  rw [← Category.assoc, (f a).w₀ j]
  rfl

-- The only choices here are the given chart models and finite affine refinements.
private theorem boundedConstructible_of_stratified_point_complexes
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)))
    (h : ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a), ∀ i : U.I₀,
        ∃ (P : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R) ℤ)
          (b c : ℤ),
          P.IsStrictlyGE b ∧ P.IsStrictlyLE c ∧
          (∀ q : ℤ, Mod.IsFinitelyPresented R (P.homology q)) ∧
          Nonempty
            ((CondensedRing.upperStar R (U.f i ≫ S.immersion a)).mapDerivedCategory.obj K ≅
              DerivedCategory.Q.obj
                (((CondensedRing.upperStarFromPointMod R (U.X i)).mapHomologicalComplex
                  (.up ℤ)).obj P))) :
    constantModelBoundedConstructible R X K := by
  classical
  refine ⟨?_, constructible_of_stratified_point_complexes R X K h⟩
  obtain ⟨S, hS⟩ := h
  choose U hU using hS
  choose P b c hb hc hf he using hU
  have : ∀ a : Fin S.n, TopologicalSpace.NoetherianSpace (S.domain a) := fun a ↦
    (S.immersion a).isEmbedding.noetherianSpace
  have hfinite (a : Fin S.n) :
      ∃ (V : Scheme.AffineCover.{u} (@WeaklyEtale) (S.domain a))
        (f : V.cover ⟶ (U a).forgetQc),
        Finite V.I₀ ∧ ∀ j, IsOpenImmersion (f.h₀ j) :=
    QuasiCompactCover.exists_hom (U a).forgetQc
  choose V f hfin hopen using hfinite
  have hv (a : Fin S.n) (i : (U a).I₀) (q : ℤ) (hq : q < b a i ∨ c a i < q) :
      IsZero ((CondensedRing.upperStar R ((U a).f i ≫ S.immersion a)).obj
        ((DerivedCategory.homologyFunctor _ q).obj K)) := by
    let := hb a i
    let := hc a i
    exact homology_isZero_of_point_model R X ((U a).X i)
      ((U a).f i ≫ S.immersion a) K (P a i) (b a i) (c a i)
      (Classical.choice (he a i)) q hq
  obtain ⟨r, s, hz⟩ := uniform_bounds_of_stratified_local_bounds R X S U
    (fun q ↦ (DerivedCategory.homologyFunctor _ q).obj K) b c hv V f hfin
  exact ⟨⟨r, (DerivedCategory.isGE_iff K r).mpr (fun q hq ↦ hz q (Or.inl hq))⟩,
    ⟨s, (DerivedCategory.isLE_iff K s).mpr (fun q hq ↦ hz q (Or.inr hq))⟩⟩

-- The explicit comparison types contain the concrete coefficient-category instances.
/-- The four conditions of the integral criterion are equivalent, including torsion
scalar models, without a dimension bound or invertibility of the residue characteristic.
The third entry uses a finite constructible locally closed stratification and the actual
derived restriction along the composite chart-to-stratum-to-X morphism. Its point complex
is bounded termwise finite free; its scalar matrices and bounds can depend on the chart.
Source: current blueprint proposition-integral-constructibility-criterion, conditions (1)--(4)
(blueprint: lem-fix-condensed-integral-criterion).

Proof, following the updated node:
1. The internal forward criterion gives completeness and constructible first reduction.
2. Integral local structure gives the stratification, covers and finite free point
   complexes. A reflexive comparison identifies their realization with the definition above.
3. Integral point-complex homology is finitely presented. Exact pullback, the derived
   homology comparison and homology of Q identify its chart realization with restricted
   cohomology. These models give constructibility in each degree.
4. Finite affine refinements of the stratum covers give common lower and upper bounds.
   Exact restriction and Noetherian stratum detection give global cohomological vanishing
   outside those bounds, hence boundedness. Finite ranges also handle empty index types.
5. The integral residue criterion identifies bounded constructibility with its intersection
   with finite Tor amplitude. The reverse implication is projection. Combine the five
   implications with tfae_finish. -/
theorem condensed_integral_criterion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    List.TFAE [
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K,
      IsDerivedComplete l E X K ∧
        constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
          ((AdicCompletion.derivedReduction l E X 0).obj K),
      ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
        ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a), ∀ i : U.I₀,
          ∃ (P : CochainComplex
              (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
                (DerivedNakayama.integerRing l E)) ℤ) (b c : ℤ),
            P.IsStrictlyGE b ∧ P.IsStrictlyLE c ∧
            (∀ q : ℤ, Mod.IsFree (DerivedNakayama.integerRing l E) (P.X q)) ∧
            Nonempty
              ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
                  (U.f i ≫ S.immersion a)).mapDerivedCategory.obj K ≅
                (condensedIntegralCriterionRealization l E (U.X i)).obj P),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K ∧
        DerivedCategory.finiteTorAmplitude _ K] := by
  classical
  tfae_have 1 → 2 := by
    intro h
    exact ⟨(IntegralModelsStacks.internal_integral_criterion_forward l E X K h).1,
      (IntegralModelsStacks.internal_integral_criterion_forward l E X K h).2.1⟩
  tfae_have 2 → 3 := by
    rintro ⟨hc, hr⟩
    obtain ⟨S, hS⟩ := integral_local_structure l E X K hc hr
    refine ⟨S, fun a ↦ ?_⟩
    obtain ⟨U, hU⟩ := hS a
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨P, b, c, hb, hc', hf, ⟨e⟩⟩ := hU i
    exact ⟨P, b, c, hb, hc', hf, ⟨e ≪≫
      eqToIso (condensedIntegralCriterionRealization_obj_eq l E (U.X i) P).symm⟩⟩
  tfae_have 3 → 1 := by
    intro h
    apply boundedConstructible_of_stratified_point_complexes
      (DerivedNakayama.integerRing l E) X K
    obtain ⟨S, hS⟩ := h
    refine ⟨S, fun a ↦ ?_⟩
    obtain ⟨U, hU⟩ := hS a
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨P, b, c, hb, hc, hf, ⟨e⟩⟩ := hU i
    exact ⟨P, b, c, hb, hc, integral_point_complex_homology l E P hf,
      ⟨e ≪≫ eqToIso (condensedIntegralCriterionRealization_obj_eq l E (U.X i) P)⟩⟩
  tfae_have 1 → 4 := by
    intro h
    exact (congrFun (internal_integral_residue_criterion l E X).2 K).mp h
  tfae_have 4 → 1 := by
    intro h
    exact h.1
  tfae_finish

end AlgebraicGeometry.ProEtale
