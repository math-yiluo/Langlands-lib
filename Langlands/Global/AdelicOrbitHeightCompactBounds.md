# Compact-factor comparison for actual primitive-vector heights

Author: Worker 83.

This derived module proves uniform two-sided comparison of the normalized
primitive-vector height under compact sets of actual adelic matrices. It also
proves the corresponding bounds for every actual finite matrix representation
of a group scheme, uniformly over the adelic point and nonzero rational vector.
No faithfulness, closed embedding, reductivity or norm-one hypothesis is needed.

## Local matrix-vector estimates

For a ring homomorphism `f : R → K` to a normed field, an invertible
`n`-by-`n` matrix `g` over `R`, and a vector `x`, the published
`MatrixInverseHeight.localMaximum f g` is the maximum of the entry norms of
`g` and its inverse. Each entry is bounded by that maximum.

`localMaximum_mulVec_le` proves that the maximum norm of `f(g x)` is at most
`n · localMaximum(f,g) · ‖f(x)‖`. For each output coordinate, the triangle
inequality bounds the norm of the sum by the sum of `n` term bounds.
`localMaximum_mulVec_le_ultra` removes the dimension factor when the local
norm is ultrametric: the norm of the sum is bounded by the maximum term.
These two estimates hold for arbitrary vectors, including zero, and do not
require `n > 0`.

## The exact normalized adelic bound

Let `F : Type u` be a number field and `n > 0`. The module uses the actual
adele-vector space `PrimitiveAdelicHeight.Vector F n`, the published normalized
primitive-vector `height`, and the actual full adelic group `AdelicGL F n`.
The finite local norm is the maximum coordinate norm. Infinite local factors
are raised to the existing multiplicities `v.mult`.

`finiteNorm_mulVec_le_matrixHeight` and `infiniteNorm_mulVec_le_matrixHeight` specialize the preceding
estimates to the actual completion projections. For every primitive vector
`x`, `height_mulVec_le_matrixHeight` proves

`height(g x) ≤ AdelicMatrixHeight.height(g) · height(x)`.

The matrix height is exactly the existing dimension-scaled normalized
matrix-and-inverse height. Its infinite local factor is
`(n · infiniteLocal(g,v)) ^ v.mult`; its finite factor is `finiteLocal(g,v)`.
There is no unspecified normalization constant.

The proof uses the published `IsPrimitive.mulVec` to preserve primitivity.
The finite local norm functions of `x`, `g x`, and the matrix have finite
multiplicative support. Thus the pointwise finite inequalities can be
multiplied using `finprod_le_finprod₀` and `finprod_mul_distrib`.
At the infinite places, raise each nonnegative inequality to `v.mult` and
multiply over the finite set of infinite places. Combining these two bounds and
reordering the factors gives the exact displayed estimate.

## Two-sided compact comparison

`IsHeightDistortionBound F n g B` is the proposition that every primitive
vector `x` satisfies both

`height(g x) ≤ B · height(x)` and `height(x) ≤ B · height(g x)`.

`isHeightDistortionBound_height` proves this with the existing matrix height
of `g`. The first inequality is the preceding theorem. Apply it to `g⁻¹`
and the primitive vector `g x` to obtain the second. The inverse matrix
undoes the vector action, and its matrix height equals that of `g`.

`exists_pos_isHeightDistortionBound_of_isCompact` proves that for every compact
set `C ⊆ AdelicGL F n`, one positive real `B` works for every `g ∈ C` and
every primitive vector. The published continuity of the full matrix height
gives an upper bound `A` on `C`; choose `B = max A 1`. The positivity of
primitive-vector heights permits increasing both factors to `B`. The compact
set may be empty and need not be closed under inversion.

For any actual group scheme `G` over `F`, actual representation
`ρ : G → GL_n`, and compact set `C ⊆ G(𝔸_F)`,
`exists_pos_orbitHeight_bounds_of_isCompact` gives `B > 0` such that every
`k ∈ C`, `g ∈ G(𝔸_F)`, and nonzero `v ∈ Fⁿ` satisfy

`orbitHeight(ρ,v,k g) ≤ B · orbitHeight(ρ,v,g)` and
`orbitHeight(ρ,v,g) ≤ B · orbitHeight(ρ,v,k g)`.

The actual adelic representation is continuous, so its image of `C` is compact.
Apply the matrix result to that image and the primitive vector
`ρ(g) · rational(v)`. The representation homomorphism law and matrix
associativity identify the vector after multiplication by `ρ(k)` with the
one defining the height at `k g`. This explains the multiplication order:
the compact factor is on the left.

## Provenance and retained obligations

The proof is derived from published actual primitive-vector heights, local
matrix-entry bounds, finite multiplicative support, the invariant matrix
height under inversion, and its proved continuity. It does not assume
continuity of the primitive-vector height, or properness or faithfulness of
the representation.

The source context is R. Godement, *Domaines fondamentaux des groupes
arithmétiques*, Séminaire Bourbaki, Exposé 257 (1963; collected 1964),
section 9.3, printed p.214 (PDF page 15). In passing from a compact-times-
parabolic expression to the parabolic factor, that passage uses uniform
two-sided comparison of the represented vector heights under the compact
factor. The original rendered page was read directly. Registered source
`godement-1963-bourbaki-257-domaines-fondamentaux`, SHA-256
`b0a531469f376c1a56a7816f0fa579cd301c4162fb1c1aa8909c886e303c722d`.
The present proof supplies this estimate over arbitrary number fields using
the existing maximum-coordinate normalization and actual adelic carriers.

The module does not compare line characters with roots, perform rank
induction, prove rank-one reduction, or establish chamber coverage.

The `_matrixHeight` suffix distinguishes these bounds for invertible matrices
from the bounds with supplied entry hypotheses in `PrimitiveAdelicGL2`.
