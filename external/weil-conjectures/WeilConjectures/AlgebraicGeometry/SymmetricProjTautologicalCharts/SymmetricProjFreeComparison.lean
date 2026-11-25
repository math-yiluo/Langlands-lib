/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjOrderedRelativeComparison
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjOrderedTwistGluing
import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.FreeProjectiveBundleBaseChangeSpace

/-!
# Ordered free comparisons for the normalized symmetric Proj quotient

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS.
(blueprint: lem-trf-symmetric-proj-free-comparison).
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

/-- Ordered free comparisons for the normalized symmetric Proj quotient.

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS.
(blueprint: lem-trf-symmetric-proj-free-comparison).

Proof: Fix r and the ordered isomorphism b. On each affine V the free basis and the
symmetric-algebra universal property give the graded polynomial isomorphism
beta: T_i maps to iota(b(e_i)), and constants map by algebraMap. The inverse
sends a vector to its finite coordinate linear polynomial. Both maps preserve
every graded piece and commute with restriction, as checked on scalars and
basis generators. Relative Proj functoriality glues their inverses to eRel,
and the standard polynomial Proj comparison gives eStd over S. The affine
polynomial isomorphism defining RelativeProjectiveSpace supplies gamma and eR;
their normalization on coefficients and variables proves the displayed chart
equation by the uniqueness of chart-compatible relative Proj morphisms.
On each D_+(T_i), send the standard twist frame T_i to the frame of D given
by iota(b(e_i)). These are free generators. Their overlap ratios agree by beta,
so the local isomorphisms and their inverses glue to t. The same construction
on the polynomial affine chart gives the twist isomorphism required by
AffineFreeComparison, carrying every degree-one polynomial a/1 to beta(a)/1.
The generator equation of D shows that each coordinate quotient agrees with
the corresponding pulled coordinateSection. Morphisms out of the unit sheaf
are determined by these sections, and equality glues. All structure morphism
equations follow from the relative Proj comparisons being over S. For r=0 the
single chart has ring R and frame T_0; the formulas also apply on empty charts. -/
theorem free_compatibility_of_normalized_quotient (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E) :
    ProjectiveBundleQuotientGeometry.HasFreeCompatibility D := by
  intro r b
  let eRel := orderedRelativeComparison b
  have hRel := orderedRelativeComparison_hom_π b
  have hAffine := orderedRelativeComparison_affineFreeComparison b
  obtain ⟨θ, hθ, _⟩ :=
    RelativeProjectiveSpace.existsUnique_freeProjectiveBundleBaseChangeSpace S r
  obtain ⟨t, ht⟩ := exists_ordered_twist_comparison S E D r b eRel hRel hAffine θ
    hθ.1 hθ.2.1
  refine ⟨eRel, eRel ≪≫ θ, t, hRel, ?_, ht, hAffine⟩
  change (eRel.hom ≫ θ.hom) ≫ _ = _
  rw [Category.assoc, hθ.1, hRel]

end AlgebraicGeometry.SymmetricProjTautologicalCharts
