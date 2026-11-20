# Exhaustion of the complement of the big cell

This internal helper module, used in the proof of
`SplitSimplyConnectedFactorialStatement`, proves the following. Let `Z` be an
irreducible subset of `G` that is disjoint from the big cell `Ω`. Assume that
every irreducible closed subset of `G` containing `Z` and disjoint from `Ω` is
contained in `Z`. (With the disjointness of `Z` from `Ω`, this makes `Z` closed,
since its closure is such a set, and maximal among irreducible closed subsets
disjoint from `Ω`.) Then `Z` meets one of the translated charts `u_a(1) · Ω`
with `a` simple. Maximality is relative to `Ω` alone; disjointness from the
translated charts is a separate hypothesis. The assembly module applies this
to the closure of a point of a height-one prime outside all charts.

## Points through open immersions and residue fields

- `exists_eq_comp_of_range_subset`: a point whose image lies in the image of an
  open immersion `φ` (of schemes over `S`) factors through `φ`.
- `exists_residue_point`: every point `w` of a test scheme `W` is the image of
  all points of `Spec κ(w)`. The global functions of `Spec κ(w)` form a field:
  each one is `0` or a unit, and the ring is nontrivial.

## Points of the big cell

Throughout, `D : CellData k G` with enumerations `neg` and `pos`.

- `exists_comp_chart_eq`: every cell point is a point of the chart.
- `exists_negSpan_mul_chart` and `exists_torus_mul_chart`: the big cell is stable
  under left multiplication by points of the negative span and of the torus.
- `rootPoint_mul_chart_mem`: over a test scheme whose global functions form a
  field, `u_a(e) · (cell point)` (with `a` simple) is a point of `Ω` or of the
  translated chart `tchart a`. Let `y` be the `-a` coordinate. If `1 + e y` is a
  unit, use `exists_translate_cellPoint` with `e₀ = e`. If `1 + e y = 0`, then
  `1 + (e - 1) y = -y` is a unit, and
  `u_a(e) = u_a(1) u_a(e - 1)`.

## Translates avoiding the big cell

Let `Z` be disjoint from `Ω`.

- `translate_notMem_of_stable`: let `j : H ⟶ G` be a map whose points keep `Ω`
  stable under left multiplication. Then `j(h) · z ∉ Ω` whenever `z` lies in
  `Z`. Pass to the residue field of the point, factor `j(h) · z` through the
  chart, and multiply by `j(h)⁻¹`.
- `translate_notMem_of_simple`: if `Z` is also disjoint from `tchart a` for a
  simple root `a`, then `u_a(c) · z ∉ Ω` for `z` in `Z`, by the same argument
  with `rootPoint_mul_chart_mem`.

## Generation by the simple root groups

- `rootPoint_mem_of_simple`: a subgroup functor `F` of `G` containing the root
  groups of all simple roots `a` and of their opposites `-a` contains every root
  group. The proof uses induction over roots
  (`SplitIntegralPinning.induction_rootChar`): every root is simple, or is
  `s_j(α')` for a simple `j` and a root `α'` already handled. In the second case
  the root subgroup of `s_j(α')` is the conjugate of that of `α'` by the Weyl
  point `n_j = weylPoint (u j) (u (-j)) = u_{-j}(-1) u_j(1) u_{-j}(-1)`
  (`weylAction_simpleWeylPoint_rootChar` and
  `RelativeRoot.normalizer_conj_mem_iff`). Since `n_j` is a product of points of
  the root groups of `j` and `-j`, it lies in `F`. The root subgroups
  are identified with the ranges of the parametrizations via
  `IsRootParametrization.represents`.

## The final contradiction

- `ga_geometry`: `𝔾ₐ` over `k` is smooth, affine and connected.
- `comp_mem_stabilizer`: in the situation of `range_subset_of_maximal` (module
  `FactorialStabilizer`), every point of `H` maps into the stabilizer of `Z`.
- `false_of_maximal` (for `G` smooth and connected): let `Z` be irreducible.
  Assume that every irreducible closed subset containing `Z` and disjoint from
  `Ω` is contained in `Z`, that `Z` is disjoint from `Ω`, and that `Z` is
  disjoint from `tchart a` for every simple `a`. Then we get `False`.
  1. By `comp_mem_stabilizer`, the stabilizer `F` of `Z` contains:
     - the simple root groups (`translate_notMem_of_simple`);
     - their opposites (`translate_notMem_of_stable` with
       `exists_negSpan_mul_chart`);
     - the torus (`translate_notMem_of_stable` with `exists_torus_mul_chart`).

     In each case translates of points of `Z` avoid `Ω`. So the closure of the
     image of the action map avoids `Ω`. It is irreducible, closed and
     contains `Z`, so by the assumption on `Z` (relative to `Ω`) it lies in `Z`
     (`range_subset_of_maximal` with `V = Ω`).
  2. Hence `F` contains all root groups (`rootPoint_mem_of_simple`) and every
     point of `Ω`.
  3. Take a point `y₀ ∈ Z` with residue field `κ`. The base change
     `G_κ = G ×ₖ Spec κ` is irreducible, since `G` is geometrically integral
     (`smoothConnectedAffineGeometry`). Let `τ : G_κ ⟶ G` be the projection and
     `z_p` the constant point `y₀`.
  4. The opens `τ⁻¹(Ω)` and `(τ · z_p)⁻¹(Ω)` are nonempty. The second is the
     image of the first under right translation by `z_p⁻¹`. So they meet in a
     nonempty open `U`.
  5. On `U`, `τ` is a point of `Ω`, hence of `F`. So `τ · z_p` has image in `Z`.
     But on `U` it also lands in `Ω`, contradicting `Z ∩ Ω = ∅`.

Provenance: internal. This plays the role of the exhaustion step (step 6) of
the route suggested in the task context. The proof replaces the rational Bruhat
decomposition and relative Weyl generation by the stabilizer argument above.
