# Actual inducing subgroups for the two mixed mirabolic products

Author: Worker 1012. Namespace:
`Langlands.GeneralLinear.Mirabolic.MixedProduct`.

This pair constructs the actual matrix subgroups in cases (II) and (III) of
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), §4.12, printed pp.456–458 (PDF pp.17–19). Source ID:
`bernstein-zelevinsky-1977-induced-i`; SHA256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original passage was read, including visual inspection of the two diagrams
on printed p.457. A bounded search of the supplied literature and project/Library
note filenames found no BZ77-specific erratum. This is a report of that search,
not a claim that no errata exist elsewhere.

The source works over a nonarchimedean local field. The commutative-ring
constructions and topological generality below are internal extensions of the
matrix definitions, with their own proved elementary laws. They assert no
representation-theoretic theorem over arbitrary rings.

## Ranks, coordinates and the two subgroups

`R : Type u` is an arbitrary commutative ring, and `k r : ℕ` are arbitrary.
There is no positivity, field or nontriviality assumption. The published
`mirabolic r R` is the source's `P_(r+1)`, consisting of actual invertible
`(r+1) × (r+1)` matrices with final row `(0,…,0,1)`. Both ambient groups here are
`mirabolic (k+r) R`, so their actual matrix rank is `k+r+1`.

`leftIndex k r : Fin k ⊕ Fin (r+1) ≃ Fin (k+r+1)` is the consecutive
partition. `leftIndex_inl_val`, `leftIndex_inr_val` and `leftIndex_last` identify
its positions. `rightIndex k r : Fin (r+1) ⊕ Fin k ≃ Fin (k+r+1)` places the
first `r` mirabolic coordinates first, the `k` general-linear coordinates next,
and the mirabolic final coordinate last. `rightIndex_first_val`,
`rightIndex_middle_val` and `rightIndex_last` prove precisely those placements.
Both definitions display the necessary arithmetic rank casts.

| Source | Actual subgroup | Projection target | Radical coordinates |
| --- | --- | --- | --- |
| §4.12(II) | `leftSubgroup k r R` | `GeneralLinear k R × mirabolic r R` | `Matrix (Fin k) (Fin (r+1)) R` |
| §4.12(III) | `rightSubgroup k r R` | `mirabolic r R × GeneralLinear k R` | `Matrix (Fin r) (Fin k) R` |

`mem_leftSubgroup_iff_entry` imposes the zero lower-left rectangle in the
consecutive `(k,r,1)` partition. Its elements are exactly

```text
[a  X  y]
[0  d  v]
[0  0  1].
```

`mem_rightSubgroup_iff_entry` imposes the zero rectangle with rows in the
middle GL block and columns in the first-and-final mirabolic block. Its
elements are exactly, in the `(r,k,1)` partition,

```text
[d  X  v]
[0  a  0]
[0  0  1].
```

The ambient mirabolic equations supply the last row in both descriptions.
Thus case (III) includes the zero column above the final diagonal entry in the
GL rows. Its mirabolic block uses the final coordinate of the total matrix.

`leftMatrix a p Z` and `rightMatrix p a X` construct every such matrix from its
diagonal factors and unrestricted rectangle. `leftMatrix_apply` and
`rightMatrix_apply` give their literal matrix entries in the explicit index
partitions. `extendRectangle X` appends a zero final row to `X`; its
`extendRectangle_first`, `extendRectangle_last` and `extendRectangle_zero` laws
record this convention. `leftBlocks` and `rightBlocks` are actual reindexings
into the upper two-block group, with entry formulas `leftBlocks_apply` and
`rightBlocks_apply`. The corresponding `*_matrix` laws identify the constructed
blocks exactly.

## Projections, sections and kernels

`leftProjection` and `rightProjection` are monoid homomorphisms to the targets
in the table. They extract actual diagonal matrix blocks. Their unit inverses
are the corresponding blocks of the actual inverse of the original matrix;
no assumed block-invertibility certificate is supplied by the caller. The four
`leftProjection_gl_apply`, `leftProjection_mirabolic_apply`,
`rightProjection_mirabolic_apply` and `rightProjection_gl_apply` theorems give
entrywise formulas. The `*_matrix` laws recover the specified diagonal pair.

`leftSection` and `rightSection` are block diagonal homomorphisms in the stated
coordinate partitions. The laws `leftProjection_section`,
`rightProjection_section`, `leftProjection_comp_section` and
`rightProjection_comp_section` prove splitting; `leftProjection_surjective`
and `rightProjection_surjective` are consequences. The `*_Section_val` laws
identify the underlying reindexed block diagonal matrix.

`leftOffDiagonal` is the full upper-right `k × (r+1)` block;
`rightOffDiagonal` is the first `r` rows of the other upper-right block.
`leftMatrix_parts` and `rightMatrix_parts` reconstruct every subgroup element
from its diagonal blocks and these raw off-diagonal entries. The right
upper-right block has final row zero, proved from the ambient mirabolic row.
The `*_OffDiagonal_matrix` laws recover the inserted rectangles.

`leftKernel` and `rightKernel` are the actual projection kernels, with normality
instances. `leftUnipotent Z` and `rightUnipotent X` insert identity diagonal
blocks and the indicated rectangle. The `*_Projection_unipotent`,
`*_OffDiagonal_unipotent`, `leftUnipotent_add` and `rightUnipotent_add` laws
prove that these elements are in the kernel, retain their coordinates and turn
addition into multiplication. `mem_leftKernel_iff` and `mem_rightKernel_iff`
characterize every kernel element as its corresponding unipotent matrix.
`leftKernelElement` and `rightKernelElement` are the insertions valued in the
actual kernels; the `*_coordinates` inverse laws prove surjectivity.

`leftKernelEquiv` and `rightKernelEquiv` are multiplicative equivalences from
the actual kernels to `Multiplicative` of their additive rectangle spaces.
`leftKernelAddEquiv` and `rightKernelAddEquiv` spell the same maps as additive
equivalences from `Additive` of the kernels. In particular, the case (II)
rectangle includes its final column; the case (III) rectangle has only `r`
rows and no mirabolic translation-column coordinate.

## Factorization and conjugation

`leftRadicalPart g` and `rightRadicalPart g` are the actual kernel elements
`g * section(projection g)⁻¹`. `leftCoordinates` and `rightCoordinates` extract
their rectangles. These coordinates belong to a radical-first factorization;
they are generally different from the raw off-diagonal entries of `g`.

`left_factorization` and `right_factorization` prove
`g = unipotent(coordinates g) * section(projection g)`.
Their `*_iff` counterparts prove uniqueness of both the rectangle and diagonal
pair. The `*_RadicalPart_unipotent_section` and
`*_Coordinates_unipotent_section` identities compute these maps on a product.
`leftFactorizationEquiv` and `rightFactorizationEquiv` package the two inverse
maps as equivalences of sets.

`left_conjugate` proves the Levi action
`Z ↦ a.val * Z * (p.val⁻¹).val` on the full case (II) rectangle.
`right_conjugate` proves
`X ↦ (Mirabolic.projection p).val * X * (a⁻¹).val` in case (III).
Here `Mirabolic.projection p` is the `r × r` upper-left block `d` of the full
mirabolic matrix `p = [d v;0 1]`. The implemented proof multiplies `p` by a
rectangle with zero last row, so `v` contributes zero. This is the asserted
translation-independent action `d X a⁻¹`.

## Topology and boundary ranks

All topologies are inherited from the published matrix-unit and subgroup
topologies. Under only `[TopologicalSpace R]`, the following maps are continuous:
`leftBlocks`, `rightBlocks`, both projections, both sections, both raw
off-diagonal maps and `extendRectangle`. The matching certificates are named
`continuous_` followed by the map name.

Under `[TopologicalSpace R] [T2Space R]`, `leftSubgroup_isClosed` and
`rightSubgroup_isClosed` prove closedness in the ambient mirabolic. No
compatibility between ring operations and topology is used for these results.

Under `[TopologicalSpace R] [IsTopologicalRing R]`, both unipotent insertions,
both radical-part maps and both coordinate maps are continuous, with matching
`continuous_` certificates. `leftFactorizationHomeomorph` and
`rightFactorizationHomeomorph` upgrade the set factorizations to homeomorphisms.
`leftKernelHomeomorph` and `rightKernelHomeomorph` similarly identify each
actual kernel with its ordinary additive rectangle topology. Hausdorffness is
unnecessary for these homeomorphisms.

All definitions and proofs quantify over every natural `k r`, so they also
apply at `k=0`, `r=0` and `(k,r)=(0,0)`. Empty rectangles use empty finite
index types. The actual `GeneralLinear 0 R` and the published `mirabolic 0 R`
are used; no artificial source `P_0` is introduced.

## Implemented proof and dependency boundary

The internal namespace `TwoBlock` handles arbitrary two-block sizes, including
zero. `upper` is the actual subgroup of units whose matrix is block upper
triangular, using Mathlib's block-triangular multiplication and inverse laws.
`A`, `B` and `D` extract its three blocks; `C_zero` and `display` recover the
literal block shape. `A_one`, `D_one`, `A_mul` and `D_mul` prove the diagonal
homomorphism laws. `projection` uses the diagonal blocks of the actual inverse.
`matrix` supplies the explicit inverse
`[a⁻¹, -a⁻¹ x d⁻¹; 0, d⁻¹]`. `matrix_parts`, `projection_matrix`,
`sectionMap`, `projection_section`, `unipotent`, `projection_unipotent`,
`unipotent_add`, `unipotent_mul_section` and `conjugate_unipotent` provide the
block identities used above. The topology proofs use continuity of unit value
and inverse-value maps and finite matrix entries. Closedness is the preimage
of the zero block equations. These helpers are internal derivations for this
construction, not additional claims attributed verbatim to BZ77.

Both public subgroups are comaps of this concrete upper subgroup through the
inverse coordinate reindexing of the actual ambient mirabolic. Extracting its
last row proves that the required diagonal factor is itself mirabolic. The
construction of `leftMatrix`/`rightMatrix` proves ambient membership directly.
Reconstruction is matrix extensionality; factorization then uses
`g * section(projection g)⁻¹` in the actual kernel. The topology proofs use
these explicit maps and subgroup topologies throughout.

The direct project import is `Langlands.Group.GL.MirabolicProjection`; the
other direct import is `Mathlib.Algebra.Group.Equiv.TypeTags`. The complete
transitive project import closure, excluding this module, is:

- `Langlands.Group.GL.MirabolicProjection`
- `Langlands.Group.GL.MirabolicRadical`
- `Langlands.Group.GL.Mirabolic`
- `Langlands.Group.GL.UpperUnipotent`
- `Langlands.Group.GL.Basic`
- `Langlands.Group.GL.RankMaps`
- `Langlands.Group.GL.Padic`
- `Langlands.LocalField.Canonical`
- `Langlands.LocalField.Definitions`
- `Langlands.LocalField.Topology`

The 20 imported Lean/Markdown files were checked byte-for-byte against the
supplied published Library and preserved unchanged. The complete closure is
matrix and local-field infrastructure: it imports no representation,
derivative, segment, socle, classification, adjunction, duality or pairing
module. Shared lower helpers supply actual matrix maps, inherited topologies
and local-field constructions. None supplies an excluded representation
theorem or a proof-successor route. Thus it is independent of the full
classification/socle exclusion set in task
`fb4abf4e-9f24-4bb0-8ac0-2ed7bf6c6942`, revision 1.

No representation product, normalization character, Haar module, derivative
identity, filtration, exactness, admissibility or irreducibility is constructed
or proved in this pair. The later representation products still require BZ77's
normalizations; these subgroup identities alone give no derivative
compatibility. Development compilation is separate from independent semantic
acceptance and Library publication.
