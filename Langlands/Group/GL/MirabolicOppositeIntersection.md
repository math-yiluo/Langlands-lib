# The binary opposite-parabolic intersection with the mirabolic group

Author: Worker 593.

This module constructs the actual binary opposite-parabolic intersection
inside the published mirabolic matrix group, together with a split diagonal
projection. Its algebra works for arbitrary `a b : ℕ`, `ha : 0 < a` and
`R : Type u` with `CommRing R`. There is no field or nontriviality assumption,
and `b = 0` is allowed. All groups and topologies are inherited from the
published actual general linear groups; no quotient group replaces them.
The imported `Mirabolic`, `Blocks` and `OppositeBlocks` pairs are unchanged.

## Binary shape and exact coordinates

`GeneralLinear.BlockShape.binary a c ha hc` is an ordered positive shape
of rank `a + c`, with exactly two blocks of sizes `a,c`, for `0 < a`
and `0 < c`. `binary_length`, `binary_size_zero` and `binary_size_one`
give those formulas. Its coordinates are proved to be the published
consecutive coordinates:

```text
(binary a c ha hc).index 0 i = Fin.castAdd c i,
(binary a c ha hc).index 1 j = Fin.natAdd a j.
```

These are `binary_index_zero` and `binary_index_one`. Their proofs expand
`BlockShape.indexEquiv`, use `finSigmaFinEquiv_apply`, and compute the
prefix sums preceding labels zero and one. No coordinate identification
is supplied as a hypothesis.

The remaining declarations are in
`Langlands.GeneralLinear.MirabolicOppositeIntersection`.
`shape a b ha` specializes `binary` to `(a,b+1)`, with the proved positivity
of `b+1`. The rank `a + (b+1)` is definitionally `a+b+1`.
`tail_last` proves
`Fin.natAdd a (Fin.last b) = Fin.last (a+b)` by equality of `Fin` values.

## Actual intersection and its entry laws

`intersection a b ha R` is exactly

```lean
((shape a b ha).oppositeParabolic R).comap
  (GeneralLinear.mirabolic (a + b) R).subtype
```

as a subgroup of `GeneralLinear.mirabolic (a+b) R`.
For an element `g` of that ambient mirabolic group,
`mem_intersection_iff` says precisely

```text
g ∈ intersection a b ha R
  ↔ ∀ i : Fin a, ∀ j : Fin (b+1),
      g.val (Fin.castAdd (b+1) i) (Fin.natAdd a j) = 0.
```

The proof specializes the published opposite-parabolic membership
characterization. Among the two block labels, zero followed by one is
the sole strictly increasing pair. The binary coordinate formulas identify
its rectangular zero block.

For `g : intersection a b ha R`, `head_tail_zero` exports these zero
entries and `last_row` retains the original ambient mirabolic certificate:

```text
g.val.val (Fin.last (a+b)) j
  = if j = Fin.last (a+b) then 1 else 0.
```

Thus, when displayed with row and column sizes `a,b,1`, the matrices have
exactly the pattern

```text
[ g1  0   0 ]
[ x   g2  y ]
[ 0   0   1 ].
```

The actual invertible factors used below are the full `a`-block and
the full `(b+1)`-block. The module does not separately extract or assert
invertibility of the displayed `b`-by-`b` submatrix `g2`.

## The split diagonal projection

`toOpposite` is a homomorphism from the intersection into
`(shape a b ha).oppositeParabolic R`. It forgets only the extra mirabolic
membership certificate; `toOpposite_val` proves that the ambient matrix
is unchanged. `diagonalProjection` is the composition of this map with
the published `oppositeLeviProjection R`.

In particular its blocks are actual invertible matrices, using the
published construction that extracts inverse blocks from the inverse
of the original matrix. No assumption of invertibility of an extracted
submatrix is added here.
`diagonalProjection_head_entry` and `diagonalProjection_tail_entry`
identify the two standard diagonal submatrices. For the tail's final row,
`tail_last` and `last_row` give the mirabolic equation.
Injectivity of `Fin.natAdd` identifies its final column, proving
`diagonalProjection_tail_mem`.

`projection a b ha R` is therefore the actual monoid homomorphism

```text
intersection a b ha R →* (GeneralLinear a R × GeneralLinear.mirabolic b R).
```

Its first component is the head block of `diagonalProjection`; its second
component is the same invertible tail block, equipped with the proved
mirabolic membership. `projection_head_entry` and `projection_tail_entry`
state the exact formulas

```text
(projection g).1 i j
  = g.val.val (Fin.castAdd (b+1) i) (Fin.castAdd (b+1) j),
(projection g).2.val i j
  = g.val.val (Fin.natAdd a i) (Fin.natAdd a j).
```

The one and multiplication laws follow by evaluating the corresponding
laws of the published invertible-block projection.

`leviLift` places the two supplied matrices from
`GeneralLinear a R × GeneralLinear.mirabolic b R` into the dependent Levi
product of `shape`, retaining the tail's original invertible matrix.
`blockDiagonal` composes it with the published common `leviEmbedding`.
The four entry laws `blockDiagonal_head_head`, `blockDiagonal_tail_tail`,
`blockDiagonal_head_tail` and `blockDiagonal_tail_head` say respectively:
the two diagonal blocks are the supplied matrices, and both cross rectangles
are zero. They specialize the published same-block and distinct-block
embedding entry laws using the binary coordinates.

`blockDiagonal_mem_mirabolic` proves membership by splitting an arbitrary
column into its head or tail coordinate. At a head column the last-row
entry vanishes and the column differs from the final coordinate.
At a tail column the last row is the supplied tail matrix's mirabolic row.
`mirabolicEmbedding` equips this same ambient embedding with that proved
membership. `diagonalSection` further restricts it into the intersection,
using the published `oppositeLeviInParabolic` membership certificate.
It is a monoid homomorphism

```text
(GeneralLinear a R × GeneralLinear.mirabolic b R) →* intersection a b ha R.
```

`diagonalSection_val` proves that its ambient value is exactly
`blockDiagonal m`. Together with the four entry laws this specifies its
entire matrix. The section introduces no new matrix in either supplied
block. `projection_diagonalSection` proves that projection after section
is the identity by specializing the published
`oppositeLeviProjection_section` identity, evaluating its two labels,
and applying subgroup extensionality for the tail component. This equality
is proved, not assumed; it also identifies the resulting mirabolic element
with the supplied one. `projection_surjective` uses this explicit section
to produce a preimage for every pair.

## Inherited topology

For `TopologicalSpace R` and `IsTopologicalRing R`,
`continuous_projection` and `continuous_diagonalSection` prove continuity.
`projectionContinuous` and `diagonalSectionContinuous` bundle exactly
the same monoid homomorphisms as continuous monoid homomorphisms.
All domain and codomain topologies are the existing subgroup, matrix-unit,
dependent-product and product topologies.

The map `toOpposite` is continuous through the two original subgroup
inclusions. The published continuous opposite Levi projection then gives
`continuous_diagonalProjection`; evaluation at the two block labels and
continuous subtype formation give the product projection.
For the section, `continuous_leviLift` checks the two coordinates, the
published continuous Levi embedding gives `continuous_blockDiagonal`,
and two applications of continuous subtype formation prove continuity
of `diagonalSection`.
`continuous_toOpposite`, `continuous_leviLift` and
`continuous_blockDiagonal` actually need only `TopologicalSpace R`;
the bundled maps retain the stated topological-ring hypotheses.

With `TopologicalSpace R` and `T2Space R`, `isClosed` proves that
`intersection` is closed in the mirabolic group: it is the continuous
preimage of the published closed opposite parabolic. Under these same
hypotheses, `locallyCompactSpace` deduces local compactness of the
intersection whenever the ambient
`GeneralLinear (a+b+1) R` is locally compact. It first uses the published
closedness/local compactness of the mirabolic subgroup and then closedness
of this intersection. These last two results need no topological-ring
hypothesis.

## Source correspondence and scope

Source: H. Jacquet, *Generic representations* (1977), Theorem 3.2,
printed pp.98–99, one-based PDF pp.104–105, especially the intersection
matrix and displayed map on printed p.99. Its row and column sizes are
`r₁,r₂-1,1`; this module sets `a=r₁`, `b=r₂-1`. The map displayed there
reads the first diagonal block and the full final mirabolic block,
as does `projection`.

Registered literature ID:
`provided-7fa6dd7a9bc39b0ef92f41d27dd4970725cdfbe795124370c63ffe3d8743b116`.
The retained file is
`literature/Jacquet (1977), Generic representations, LNM 587.pdf`,
SHA256 `073cdfbdac1db264653544249d1060ba47704cc1678a5f545b9cd0ca5df46c8a`.
Both original pages were read, the p.99 display was visually checked,
and the retained file's hash was verified. No relevant source-specific
erratum was found in the available public/source notes.

The formal construction and its structural proofs are internal derivations
from the published actual matrix geometry in `Mirabolic`, `Blocks` and
`OppositeBlocks`, with elementary finite-coordinate arguments described
above. The source's local-field picture motivates the definition; the
implemented matrix arguments generalize it to commutative rings, including
the boundary `b=0` and rings with `0=1`.

This module proves group geometry only. It gives no additive kernel model,
semidirect-product analysis, Haar or modulus formula, conull-orbit or Mackey
comparison, Hilbert completion, smooth-vector recovery, or irreducibility
theorem. In particular it does not identify an induced Hilbert representation
with normalized upper-parabolic induction and does not prove Jacquet's
Theorem 3.2 or Corollary 3.3.
