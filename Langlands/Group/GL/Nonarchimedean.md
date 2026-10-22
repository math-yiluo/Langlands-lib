# Intrinsic nonarchimedeanness of valuative GL

Worker 6 authored the complete proof. Worker 52 checked the Library target,
the proof's Mathlib interfaces and hypotheses, retained the Lean source
unchanged, and prepared this documented submission.
The exact target is the proposition definition
`Langlands.ValuativeGeneralLinearNonarchimedean` in the Library module
`Langlands.Group.GL.NonarchimedeanStatement`, independently reviewed and
published at commit `1804f2a6d98d21c2bbfa3c73ccf807df74c484bb`.
The theorem `Langlands.valuativeGeneralLinearNonarchimedean` has exactly that
proposition as its type.

The proof uses the actual matrix-unit topology, with neighborhoods
controlling both the matrix and its inverse. For a nonzero valuation radius
at most one, the matrices whose difference from the identity has every entry
strictly smaller than this radius form a submonoid. The multiplication
identity is
`AB - I = (A - I)(B - I) + (A - I) + (B - I)`.
The ultrametric inequality bounds the finite sums in each matrix entry.
Since the radius is at most one, multiplication of two small entries stays
small. The unit subgroup of this submonoid imposes the same condition on
the inverse and is open.

`finitePiBasis` derives a common-radius basis for a finite product from
`Filter.HasBasis.pi_self`: one direction restricts all-coordinate conditions
to a finite cylinder, and the other uses the full finite index set.
Applying it twice to `IsValuativeTopology.hasBasis_nhds_zero` gives the
matrix basis at zero. Translation by the identity yields a common entry
bound inside every matrix neighborhood of the identity.

The scalar open-ball proof uses the valuation bound for
`y = (y - x) + x`, with the same radius. Applying `IsOpen.matrix` and
continuous subtraction proves openness of the small-matrix submonoid.
`Submonoid.units` supplies a genuine subgroup of the matrix units: both
the matrix and its inverse lie in the submonoid. Its subgroup laws are
Mathlib's proved construction, and `Submonoid.isOpen_units` proves openness
from the two continuous coordinate maps.

For an arbitrary identity neighborhood in GL, the proof unfolds the induced
topology of `Units.embedProduct`. It contains the preimage of a product of
matrix and opposite-matrix neighborhoods. Pulling the latter back along
`MulOpposite.op` and intersecting gives one matrix neighborhood. The finite
matrix basis supplies a nonzero radius. Replacing it by its minimum with
one ensures the multiplicative estimate required by the submonoid without
losing the neighborhood containment. The two membership conditions in its
unit subgroup then place the matrix and inverse in the chosen product
neighborhood. This proves the exact nonarchimedean target.

The coefficient hypotheses are precisely `Field K`, `ValuativeRel K`,
`TopologicalSpace K`, and `IsValuativeTopology K`. All natural ranks,
including zero, are covered. There is no local compactness, separation,
completeness, discrete-value-group, supplied GL nonarchimedean instance,
or compact-open premise. In particular, no inverse-convergence or
completeness argument is needed: the unit subgroup tests the actual inverse.

All arguments are internal derivations from the pinned Mathlib interfaces.
The only project import is the Library proposition definition above.
Neither its Lean/Markdown pair nor its Mathlib imports is modified.
No original-source theorem is being assumed. Machine validation and
independent semantic acceptance/publication remain required; local
compilation alone does not discharge them.

The prepared environment uses Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The proof also imports
`Mathlib.Tactic.NoncommRing` for the matrix multiplication identity.

| Declaration | Role in the proof |
| --- | --- |
| `finitePiBasis` | Converts `Filter.HasBasis.pi_self` into a basis with one common bound for all coordinates of a finite product. |
| `matrixZeroBasis` | Applies that conversion twice to `IsValuativeTopology.hasBasis_nhds_zero`. |
| `valuativeBallOpen` | Uses `IsValuativeTopology.mem_nhds_iff'` and the ultrametric inequality to prove that each scalar ball is open. |
| `valuativeMatrixMonoid` | Bundles the entrywise condition near the identity, proving closure using `Valuation.map_sum_lt`, multiplicativity, and `noncomm_ring`. |
| `valuativeMatrixMonoidOpen` | Pulls back the finite product of scalar balls along subtraction of the identity. |
| `existsSmallMatrix` | Translates the zero-neighborhood basis to a common entry bound at the identity. |
| `valuativeGeneralLinearNonarchimedean` | Constructs an open subgroup inside each prescribed neighborhood using `Submonoid.units` and the induced topology of `Units.embedProduct`. |

All supporting declarations are private and remain in this proof module.
Mathlib's `NonarchimedeanGroup` includes `IsTopologicalGroup`; the existing
topological-group instance on matrix units supplies that inherited field.
The valuative topology supplies the needed topological-ring operations.
The proof constructs the open-subgroup neighborhood property itself.
