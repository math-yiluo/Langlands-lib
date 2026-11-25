/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverPullback
public import WeilConjectures.AlgebraicTopology.FiniteCofaceShortComplex
import WeilConjectures.AlgebraicGeometry.FiniteHypercoverMapExtension
/-! # Finite hypercover maps and the cohomology colimit -/
@[expose] public section
universe u' u
open CategoryTheory Limits Opposite AlgebraicTopology
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- The three section objects controlling degree-q cohomology. -/
noncomputable abbrev sectionShortComplex (F : Sheaf X.smallEtaleTopology A)
    (U : FiniteSplitEtaleHypercover X) (q : ℕ) : ShortComplex A :=
  ((alternatingCofaceMapComplex A).obj (U.simplicial.rightOp ⋙ F.obj)).sc q

/-- A finite refinement induces a map on the three relevant cochain terms. -/
noncomputable def finiteRefinementShortComplexMap (F : Sheaf X.smallEtaleTopology A)
    {U V : FiniteSplitEtaleHypercover X} (q : ℕ)
    (t : (SimplicialObject.truncation (q + 1)).obj U.simplicial ⟶
      (SimplicialObject.truncation (q + 1)).obj V.simplicial) :
    sectionShortComplex A F V q ⟶ sectionShortComplex A F U q :=
  finiteCofaceShortComplexMap q (Functor.whiskerRight t.rightOp F.obj)

/-- Finite refinement maps compose contravariantly. -/
theorem finiteRefinementShortComplexMap_comp (F : Sheaf X.smallEtaleTopology A)
    {U V W : FiniteSplitEtaleHypercover X} (q : ℕ)
    (t : (SimplicialObject.truncation (q + 1)).obj U.simplicial ⟶
      (SimplicialObject.truncation (q + 1)).obj V.simplicial)
    (s : (SimplicialObject.truncation (q + 1)).obj V.simplicial ⟶
      (SimplicialObject.truncation (q + 1)).obj W.simplicial) :
    finiteRefinementShortComplexMap A F q (t ≫ s) =
      finiteRefinementShortComplexMap A F q s ≫
        finiteRefinementShortComplexMap A F q t := by
  ext <;> simp [finiteRefinementShortComplexMap, finiteCofaceShortComplexMap,
    NatTrans.rightOp_app, ← Functor.map_comp, ← op_comp]

/-- The finite three-term construction agrees with the cohomology refinement map. -/
theorem cohomologyRefinement_eq_finite (F : Sheaf X.smallEtaleTopology A)
    {U V : FiniteSplitEtaleHypercover X} (q : ℕ) (r : U.Refinement V) :
    (cohomologyRefinement A r q).app F =
      ShortComplex.homologyMap (finiteRefinementShortComplexMap A F q
        ((SimplicialObject.truncation (q + 1)).map r)) := by
  rfl

variable [IsGrothendieckAbelian.{u + 1} A]

/-- The colimit injection respects a map defined only through degree q+1.
Source: the finite-cochain argument of blueprint étale cohomology continuity.
Extend the finite map to full refinements from one common hypercover, retaining
its source skeleton. Functoriality on the three cochain terms expresses the second
refinement map as the composite of the finite map and the first refinement map.
Apply homology and the two refinement equations for colimit injections.
(auxiliary; not a blueprint node) -/
theorem finiteRefinement_homology_comp_ι (F : Sheaf X.smallEtaleTopology A)
    (U V : FiniteSplitEtaleHypercover X) (q : ℕ)
    (t : (SimplicialObject.truncation (q + 1)).obj U.simplicial ⟶
      (SimplicialObject.truncation (q + 1)).obj V.simplicial) :
    ShortComplex.homologyMap (finiteRefinementShortComplexMap A F q t) ≫
        hypercoverCohomologyι A F q U = hypercoverCohomologyι A F q V := by
  obtain ⟨W, a, b, e, ha, hb⟩ := exists_refinement_extending_finite_map U V (q + 1) t
  have hh : (cohomologyRefinement A b q).app F =
      ShortComplex.homologyMap (finiteRefinementShortComplexMap A F q t) ≫
        (cohomologyRefinement A a q).app F := by
    rw [cohomologyRefinement_eq_finite, hb, ← ha,
      finiteRefinementShortComplexMap_comp, ShortComplex.homologyMap_comp,
      ← cohomologyRefinement_eq_finite]
  rw [← cohomologyRefinement_comp_ι A F q a, ← Category.assoc, ← hh,
    cohomologyRefinement_comp_ι]

end AlgebraicGeometry.FiniteSplitEtaleHypercover
