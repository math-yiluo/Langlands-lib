# Absolute coefficient Lie algebra cohomology

This module constructs absolute Lie algebra cohomology from the published
coefficient Chevalley–Eilenberg differential and its proved square-zero
identity. All declarations are in `Langlands.Cohomology.Lie`.

Let `K : Type u` be a characteristic-zero field, `L : Type v` a `K`-Lie
algebra, and `M : Type w` an additive commutative group with `Module K M`,
`LieRingModule L M` and `LieModule K L M`. The universes `u`, `v` and `w`
are independent. Neither the Lie algebra nor the coefficient module has a
finite-dimensionality assumption. There is no topology on any of these
objects in this construction.

## Provenance

This is an internal construction from
`Langlands.Cohomology.Lie.CoefficientCochains` and
`Langlands.Cohomology.Lie.CoefficientSquareZeroProof`, using Mathlib's
`Submodule`, linear-map kernels and ranges, `Submodule.inclusion`, module
quotients, and `Submodule.mapQ`. The existing modules supply the actual
coefficient differential, its naturality under equivariant coefficient
maps, and the theorem `differential_differential`. This module takes none
of these properties as additional hypotheses. Its definitions and proofs
are the elementary kernel, image and quotient consequences of those
published constructions. No new external source identification or
resolution comparison is asserted here.

## Cycles, boundaries and the quotient

Write `C^q = Cochains K L M q` and `d_q = differential q`. The latter is the
constructed operator of the imported module, with its coefficient action
and bracket terms.

- `cycles K L M q` is the submodule `ker d_q` of `C^q`.
  `mem_cycles` says that its membership condition is exactly `d_q f = 0`.
- `boundaries K L M 0` is the zero submodule of `C^0`.
  `boundaries K L M (n+1)` is the actual range of `d_n`.
  `boundaries_zero`, `boundaries_succ`, `mem_boundaries_zero` and
  `mem_boundaries_succ` expose these definitions and the exact range
  witness: `f` is a successor-degree boundary if and only if
  `d_n g = f` for some `g : C^n`.
- `boundaries_le_cycles q` proves that the boundary submodule is contained
  in the cycle submodule. Degree zero uses the least-submodule property.
  In degree `n+1`, write the boundary as `d_n g` and apply the published
  theorem `differential_differential n g`.

The first two definitions and their membership formulas use only a field;
the proved inclusion and the subsequent quotient construction also use
`CharZero K`, as required by the imported square-zero theorem.

`boundariesInCycles K L M q` is the range of the linear inclusion

```
Submodule.inclusion (boundaries_le_cycles q) :
  boundaries K L M q →ₗ[K] cycles K L M q.
```

Thus it consists of all actual boundaries, viewed as cycles through the
proved inclusion. In particular `mem_boundariesInCycles` proves that a
cycle belongs to this submodule if and only if its underlying cochain
belongs to `boundaries K L M q`. The proof goes in one direction by taking
the boundary representative of a range element and in the other by
packaging the given underlying cochain as a boundary. Subtype extensionality
identifies the two cycle elements.

`CoefficientCohomology K L M q` is the actual module quotient

```
cycles K L M q ⧸ boundariesInCycles K L M q.
```

Its additive commutative group and `K`-module structures are the standard
Mathlib quotient structures. The definition has no supplied cohomology
carrier, chosen class representatives or differential parameter.

## Classes and vanishing

`cohomologyClass K L M q` is the linear quotient projection from cycles.
`cohomologyClass_surjective q` is Mathlib's surjectivity of this projection.
The two quotient criteria are proved from Mathlib's quotient equality
lemmas and `mem_boundariesInCycles`:

- `cohomologyClass_eq_zero f`: the class of a cycle `f` is zero if and only
  if its underlying cochain is an actual boundary.
- `cohomologyClass_eq_iff f g`: the classes of two cycles are equal if and
  only if `f.val - g.val` is a boundary.

`coboundaryToCycles q` restricts the codomain of `d_q` to `cycles (q+1)`.
Its well-definedness uses `differential_differential` directly.
`coboundaryToCycles_val` identifies its underlying cochain with `d_q f`.
`cohomologyClass_coboundary q f` proves that this cycle has zero class,
using `f` as the explicit witness in the preceding differential's range.

## Equivariant coefficient maps

Let `N : Type w'` and `P : Type w''` have the same kind of coefficient
module structures as `M`; their universes are independent as well. For an
actual Lie-module map `φ : M →ₗ⁅K,L⁆ N`, the imported `map φ q` is linear
postcomposition of cochains by `φ`.

`map_mem_cycles` proves that it preserves cycles, by rewriting with
`map_differential` and the input's zero differential. `map_mem_boundaries`
proves preservation of actual boundaries. In degree zero the input is
zero and linear postcomposition preserves zero. In degree `n+1`, if the
input is `d_n g`, then `map_differential` identifies its image with
`d_n (map φ n g)`, giving a specific boundary witness.

`mapCycles φ q` is the linear restriction to the two cycle submodules;
`mapCycles_val` identifies its underlying cochain. The membership theorem
`mapCycles_mem_boundariesInCycles` follows from the boundary membership
criterion and `map_mem_boundaries`. It supplies exactly the hypothesis of
Mathlib's `Submodule.mapQ`, producing

```
mapCohomology φ q :
  CoefficientCohomology K L M q →ₗ[K] CoefficientCohomology K L N q.
```

`mapCohomology_class` proves that the image of a cycle's class is the class
of its coefficient postcomposition. `mapCycles_id` and `mapCycles_comp`
prove preservation of identity and composition on cycles by evaluating
the underlying alternating maps. The corresponding quotient identities
are `mapCohomology_id` and `mapCohomology_comp`: every quotient element has
a cycle representative by `cohomologyClass_surjective`, so the class
formula reduces both identities to the cycle identities. In the
composition formula the order is covariant:

```
mapCohomology (ψ.comp φ) q =
  (mapCohomology ψ q).comp (mapCohomology φ q).
```

This constructs absolute algebraic coefficient cohomology and the indicated
linear maps. Relative Lie algebra cohomology, full compact-group actions,
analytic comparison, automorphic coefficient attachment and any Ext or
resolution identification require subsequent constructions and results.

Authorship: Worker 2.
