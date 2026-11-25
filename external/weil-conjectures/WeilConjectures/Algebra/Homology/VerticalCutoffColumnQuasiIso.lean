/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalTowerMaps
import WeilConjectures.Algebra.Homology.VerticalCutoffColumnQuasiIsoCore
import WeilConjectures.Algebra.Homology.VerticalCutoffColumnQuasiIsoEqual

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical projection on a single column induces a quasi-isomorphism on the
quotient of nested smart cutoffs.
Source: Stacks Project, Homology, tag 0118, canonical cochain truncations; Mathlib's
`shortComplexTruncLEX₃ToTruncGE` for complementary truncations. The nested-cutoff
argument below is an explicit specialization.
(blueprint: lem-sp-vertical-cutoff-column-quasiiso)

Proof: extend L by zero to the integers. The smart cutoff inclusions are degreewise
monic, so the inclusion compatibility uniquely determines g. Evaluation and
restriction preserve cokernels. For a < b, the cokernel has the image of the original
boundary differential in degree a-1, the original term in degree a when a < b-1,
and the cycles in degree a when a = b-1. The specified projection to the window is
zero in degree a-1, quotient by that image in degree a, and an isomorphism above a.
It is degreewise epic. Its kernel has that image in degrees a-1 and a and the
canonical image isomorphism as differential, and is zero elsewhere. This two-term
complex is contractible; the short exact homology sequence makes q a quasi-isomorphism.
For a=b, monicity forces g to be the identity, and the quotient and window vanish.
For b<=0 both vanish after restriction. For a<0<=b the lower projection is an
isomorphism on the extended column. For a=0 the image in degree -1 is zero, so
restriction to the naturals does not discard a nonzero half of the contractible
kernel. These cases prove the assertion for every pair of integer endpoints. -/
theorem verticalCutoff_column_quasiIso
    (L : CochainComplex C ℕ) (a b : ℤ) (hab : a ≤ b)
    (g : (verticalCutoff a).obj L ⟶ (verticalCutoff b).obj L)
    (hg : g ≫ (verticalCutoffι b).app L = (verticalCutoffι a).app L)
    (q : cokernel g ⟶ (verticalWindow a b).obj L)
    (hq : cokernel.π g ≫ q = HomologicalComplex.restrictionMap
      (CochainComplex.truncLEMap
        (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
      ComplexShape.embeddingUpNat) : QuasiIso q := by
  rcases hab.lt_or_eq with hablt | rfl
  · exact verticalCutoff_column_quasiIso_strict L a b hablt g hg q hq
  · exact verticalCutoff_column_quasiIso_equal L a g hg q hq

end HomologicalComplex₂
