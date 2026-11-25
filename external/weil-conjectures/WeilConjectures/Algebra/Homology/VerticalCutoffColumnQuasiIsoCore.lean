/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalTowerMaps
import WeilConjectures.Algebra.Homology.VerticalCutoffColumnQuasiIsoStrictCases
import WeilConjectures.Algebra.Homology.VerticalCutoffColumnQuasiIsoStrictPositive

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The strict endpoint case of the nested-cutoff comparison.
Source: Stacks Project, Homology, Section 12.15, tag 0118, canonical cochain
truncations (https://stacks.math.columbia.edu/tag/0118); the nested-cutoff kernel
argument is an explicit specialization.
(blueprint: lem-sp-vertical-cutoff-column-quasiiso-strict)

Proof: put E = L extended by zero to the integers. Monicity of the cutoff inclusions
identifies g with the natural inclusion of the cutoff below a into the cutoff below b.
Cokernels are degreewise. If b <= 0, the restricted cutoffs and the window are zero.
If a < 0 < b, the lower cutoff is zero and the lower projection is an isomorphism
on E, so the specified map q is an isomorphism. If a = 0 < b, the same conclusion
holds since E is strictly supported in nonnegative degrees. It remains that 0 < a < b.
The source of q is zero below a-1, is the image I of E.d (a-1) a at a-1, and agrees
with the upper cutoff at all degrees at least a. The projection equation makes q
zero at a-1, the quotient by I at a, and an isomorphism above a. For b = a+1 its
component at a is the map from cycles to homology; otherwise it is the map from E.X a
to opcycles. Both are epic with kernel I. Thus q is degreewise epic, with kernel
having I only in degrees a-1 and a, and differential the canonical identity under
these image identifications. This kernel is contractible, using the inverse of that
differential as its sole nonzero contracting-homotopy component. The homology exact
sequence of the kernel-source-window short exact sequence proves q is a
quasi-isomorphism. The restriction to naturals retains both nonzero kernel degrees
in the remaining case 0 < a, completing the proof. -/
theorem verticalCutoff_column_quasiIso_strict
    (L : CochainComplex C ℕ) (a b : ℤ) (hab : a < b)
    (g : (verticalCutoff a).obj L ⟶ (verticalCutoff b).obj L)
    (hg : g ≫ (verticalCutoffι b).app L = (verticalCutoffι a).app L)
    (q : cokernel g ⟶ (verticalWindow a b).obj L)
    (hq : cokernel.π g ≫ q = HomologicalComplex.restrictionMap
      (CochainComplex.truncLEMap
        (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
      ComplexShape.embeddingUpNat) : QuasiIso q := by
  by_cases ha : a ≤ 0
  · exact verticalCutoff_column_quasiIso_strict_nonpositive L a b hab ha g hg q hq
  · exact verticalCutoff_column_quasiIso_strict_positive L a b hab (lt_of_not_ge ha) g hg q hq

end HomologicalComplex₂
