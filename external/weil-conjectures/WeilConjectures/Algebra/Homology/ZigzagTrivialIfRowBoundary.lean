/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ZigzagModule
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.Algebra.Homology.ZigzagZeroComponentBoundary
import WeilConjectures.Algebra.Homology.ZigzagBoundaryReduction

/-! # Exact-row zig-zags are trivial

Source: Stacks Project, Algebra, Lemma Tag 00M1, injectivity argument
(blueprint: lem-weil-pbc-double-complex-zigzag-trivial-if-row-boundary).
-/

@[expose] public section

open CategoryTheory

namespace HomologicalComplex₂

universe u v

variable {R : Type u} [CommRing R]

/-- A zig-zag whose row-cokernel component is a vertical boundary is trivial when
all rows are exact in positive degrees. The row-cokernel complex `Aʳᵗ` is
`A.opcycles 0`, formed in the abelian category of chain complexes: its degree `q` is
the cokernel of `d₁,ᵩ : A₁,ᵩ → A₀,ᵩ`, with projection `π = A.pOpcycles 0` and
differential induced by `δ`. The hypothesis `hboundary` says that `πₙ(a₀,ₙ)` lies in
the image of `δʳᵗ : Aʳᵗₙ₊₁ → Aʳᵗₙ`. Row exactness is `ShortComplex.Exact` of
`Aₚ₊₁,ᵩ → Aₚ,ᵩ → Aₚ₋₁,ᵩ` for `p ≥ 1`.

Source: Stacks Project, Algebra, Lemma Tag 00M1, injectivity argument
(blueprint: lem-weil-pbc-double-complex-zigzag-trivial-if-row-boundary).

First lift a boundary preimage `y` through the cokernel projection in degree `n+1`
to `c` in `A₀,ₙ₊₁`. Since `π` is a chain map, the difference `a₀,ₙ - δ c` has zero
image under `πₙ`. The cokernel property puts it in the image of `d : A₁,ₙ → A₀,ₙ`;
choose a preimage `e`. The total-degree `n+1` tuple supported at `(0,n+1)` and `(1,n)`
with values `c` and `e` has boundary with zeroth component `a₀,ₙ`. Subtract it. The
replacement remains a zig-zag by `lem-weil-pbc-double-complex-zigzag-module-functorial`,
using the definitions in `def-weil-pbc-double-complex-zigzag-module` and the cokernel
chain complex of `def-weil-pbc-module-chain-complex-homology`.

Inductively suppose the components with horizontal index less than `k` vanish,
where `1 ≤ k ≤ n`. The zig-zag equation gives `d aₖ,ₙ₋ₖ = 0`. Exactness of the row at
this positive index (`def-weil-pbc-exact-sequence`) supplies `f` in `Aₖ₊₁,ₙ₋ₖ` with
`d f = aₖ,ₙ₋ₖ`. Subtract the boundary supported there. It kills this component,
changes only the next component, and preserves the zig-zag property by the same
functoriality node. After `k = 1,...,n` every component is zero. All subtracted tuples
belong to the submodule of trivial zig-zags, hence so does the original `a`.
For `n = 0` the first subtraction already finishes. -/
theorem zigzag_trivial_if_row_boundary
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (hrow : ∀ (p q : ℕ), 0 < p →
      (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
        (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
          HomologicalComplex.zero_f])).Exact)
    (n : ℕ) (a : zigzagTotal A n)
    (ha : a ∈ zigzagCycles A n)
    (hboundary : ∃ y : (A.opcycles 0).X (n + 1),
      (A.opcycles 0).d (n + 1) n y = (A.pOpcycles 0).f n
        (DirectSum.component R (ZigzagIndex n)
          (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2) ⟨(0, n), by simp⟩ a)) :
    a ∈ zigzagBoundaries A n := by
  obtain ⟨b, hbz, hb0⟩ := zigzagBoundary_reduction A hrow n a ha hboundary
  have hbb := zigzag_zero_component_boundary A hrow n (a - zigzagBoundary A n b) hbz hb0
  obtain ⟨c, hc⟩ := hbb
  refine ⟨b + c, ?_⟩
  simp only [map_add]
  rw [hc]
  abel

end HomologicalComplex₂
