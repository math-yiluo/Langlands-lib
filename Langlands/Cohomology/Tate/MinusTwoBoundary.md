# Tate connecting maps in degree minus two

This internal construction applies to a representation `A` over any commutative
ring `R` and a finite group `G`, all in the stated common universe. It compares
ordinary first-homology representatives with the actual Tate complex and computes
its connecting map on the published single-chain class.

`homologyOneTateCycles` maps ordinary degree-one cycles into degree-minus-two
Tate cycles using Mathlib's negative restriction comparison.
`homologyOneToTate_π` identifies the resulting homology map with the inverse of
`TateCohomology.isoGroupHomology (-2) 1`.
`homologyOneTateCycles_iCycles` proves that this map preserves the underlying
chain vector. These are statements about the actual complexes and comparison
isomorphisms.

For trivial coefficients, `single_tate_cycle` checks that the chain represented
by `Finsupp.single g a` is a cycle. `minusTwoClass_eq_cycleClass` then identifies
the published `minusTwoClass A g a` with that actual chain's Tate class. The proof
uses naturality of the homology projection, the cycle inclusion's injectivity,
and Mathlib's explicit degree-one cycle isomorphism.

Finally, let `S` be a short exact sequence `X₁ → X₂ → X₃` of representations,
with trivial `X₃`. Suppose `b : X₂` lifts `a : X₃`, and let `c : X₁` have norm
zero and satisfy

```
S.f.hom c = X₂.ρ (g⁻¹) b - b.
```

`delta_minusTwoClass` proves

```
TateCohomology.δ hS (-2) (minusTwoClass X₃ g a)
  = minusOneClass X₁ c hc0.
```

Here `hc0` is the supplied proof that the norm of `c` is zero. The proof maps the
lifted single chain using Mathlib's degree-one chains map, computes its
differential using `groupHomology.d₁₀_single`, and applies the actual-complex
representative theorem `delta_cycleClass`. In particular, the difference uses
`g⁻¹`, in agreement with Mathlib's homology convention; no sign or inversion is
inserted by the first-homology-to-Tate representative comparison.

The provenance is internal: this module derives a low-degree representative API
from Mathlib's group homology and Tate complex and the published
`SpliceRepresentatives`, `BoundaryDiagrams`, and `LowDegree` modules. It makes
no claim about the complete cyclic double-boundary calculation or the finite
cup–Artin character comparison.
