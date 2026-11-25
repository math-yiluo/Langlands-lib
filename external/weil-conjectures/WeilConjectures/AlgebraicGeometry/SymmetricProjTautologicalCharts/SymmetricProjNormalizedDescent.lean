/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjAffineComparisonExistence
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjSectionCompatibility

/-!
# Descent of the normalized symmetric Proj quotient

Source: Stacks Project, Constructions, Tags 01NR, 01OB, 01MS and 01N2.
(blueprint: lem-trf-symmetric-proj-normalized-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomogeneousLocalization
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.Modules.boundaryPullbackComparison
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The affine twist comparison with its chart and homogeneous-section normalizations.
Source: Stacks, Tags 01NR and 01OB
(blueprint: lem-trf-symmetric-proj-normalized-descent). -/
structure NormalizedAffineRestriction {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (U V : S.affineOpens) (h : U ≤ V) where
  comparison : (Scheme.Modules.tensorPullback
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))).obj
        (Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) 1) ≅
          Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) 1
  chart_compatibility : (Scheme.Modules.tensorPullback
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))).map
        (D.chart V).hom ≫ comparison.hom =
      (Scheme.Modules.tensorPullbackSectionComp
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V)).inv.app D.line ≫
      (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj D.line)
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor_map_relProjι
          (homOfLE h)))).hom ≫ (D.chart U).hom
  section_compatibility : ∀ (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V)
      (ha : a ∈ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V 1),
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))).map
          (Proj.unitToTwist ha) ≫ comparison.hom =
        ((Scheme.Modules.boundaryPullbackComparison
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map
              (homOfLE h))).app (Scheme.Modules.unit _) ≪≫
          Scheme.Modules.pullbackObjUnitIso
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map
              (homOfLE h))).hom ≫
        Proj.unitToTwist
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).res h |>.map_mem ha)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The normalized degree-one quotient descends from the affine symmetric Proj twists.
Its comparison on affine restriction carries every degree-one section to its image.

Source: Stacks, Tags 01NR, 01OB, 01MS and 01N2.
(blueprint: lem-trf-symmetric-proj-normalized-descent).

Proof: For each affine base open U use the actual sheaf Proj.twist A(U) 1.
On D_+(iota(m)), multiplication by iota(m) identifies this module with the
structure sheaf. The symmetric algebra is generated in degree one, so these
opens cover. Send v tensor h to h iota(v)/1; this hits the local frame and is
split surjective. On a restriction U <= V, quasi-coherence identifies the new
symmetric algebra with scalar extension. The induced map on a/e^k is
res(a)/res(e)^k. These fraction maps send the old frame e to res(e) and give
inverse trivializations on the corresponding charts. They preserve unitToTwist
for every degree-one element, since that section is a/1. Their compositions
agree on fractions. Refine nonaffine intersections by affine base opens, apply
these comparisons there, and use the sheaf axiom to check independence of the
refinement and the triple cocycle. Module-sheaf descent glues the local twists
and quotient maps, with the specified charts. Their free rank-one local frames
prove invertibility; the local splittings prove that the quotient is epi.
Pulling the glued charts back to U <= V gives the first displayed equation.
The fraction map proves the second equation. Empty or nilpotent
charts are zero localizations and impose no extra assumption. -/
theorem exists_normalized_quotient_with_affine_restriction
    (S : Scheme.{u}) (E : S.Modules) [E.IsQuasicoherent] :
    ∃ D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E,
      ∀ (U V : S.affineOpens) (h : U ≤ V),
        Nonempty (NormalizedAffineRestriction E D U V h) := by
  obtain ⟨D, hD⟩ := exists_affine_comparison_with_chart_compatibility S E
  refine ⟨D, ?_⟩
  intro U V h
  obtain ⟨c⟩ := hD U V h
  refine ⟨⟨c.comparison, c.chart_compatibility,
    section_compatibility_of_affine_comparison E D U V h c⟩⟩

end AlgebraicGeometry.SymmetricProjTautologicalCharts
