# The unipotent part of a smooth connected solvable group

`Langlands.GroupScheme.solvableUnipotentPart` proves exactly
`Langlands.GroupScheme.SolvableUnipotentPartStatement.{u}` at arbitrary universe
`u`. Over every algebraically closed field `k : Type u`, a smooth connected
affine group scheme `H` satisfying `IsSolvableGroupScheme H` has a smooth
connected normal unipotent closed subgroup containing every unipotent closed
subgroup. Containment and normality hold on every test scheme, including
nonreduced test schemes. The proof introduces only the published hypotheses.

The published theorem
`solvableTriangularEmbeddingStatement : SolvableTriangularEmbeddingStatement.{u}`
from `Langlands.GroupScheme.Absolute.SolvableTriangularEmbeddingProof` supplies
the concrete Lie–Kolchin closed embedding. The published theorem
`triangularDiagonalKernelGeometry : TriangularDiagonalKernelGeometryStatement.{u}`
from `Langlands.GroupScheme.Absolute.TriangularDiagonalKernelGeometryProof`
supplies smoothness and connectedness of its actual diagonal kernel.
The published theorem
`unitriangularUnipotent : UnitriangularUnipotentStatement.{u}` from
`Langlands.GroupScheme.UnitriangularUnipotentProof` supplies
representation-theoretic unipotence of the concrete unitriangular group over
every field, including dimension zero.
The published theorem
`unipotentClosedSubgroup : UnipotentClosedSubgroupStatement.{u}` from
`Langlands.GroupScheme.UnipotentClosedSubgroupProof` supplies inheritance of
unipotence by closed subgroups over every field, without smoothness, reducedness
or connectedness assumptions on the subgroup.

Choose a closed triangular embedding `j : H ⟶ T_N` from
`solvableTriangularEmbeddingStatement` and
let `q : T_N ⟶ D_N` be the existing block diagonal map. Distinct descending
weights identify `D_N` with a split torus. The geometry theorem makes
`kernel (j ≫ q)` smooth and connected by applying
`triangularDiagonalKernelGeometry` to this same embedding.

The existing `GeneralLinear.blockUnipotentIsoKernel` identifies `U_N` with
`kernel q`. The formal comparison map `kernel (j ≫ q) ⟶ U_N` is a closed
subgroup because `j` is closed. The local adapters prove that `U_N` is affine
and locally of finite type, so `unitriangularUnipotent` and
`unipotentClosedSubgroup` make
the smaller kernel unipotent.

The formal assembly lemma takes that actual kernel and its inclusion into
`H`. Its inclusion is closed because the diagonal target is separated, its
range is normal, and every competing unipotent group maps trivially to the
split torus. This last argument applies on every test scheme, so it includes
nonreduced and disconnected competing closed subgroups.

This module is an internal composition of the published theorems above and
the included adapter and kernel-assembly lemmas. All geometric and unipotence
prerequisites are supplied by proofs. Its route follows the triangular-kernel
argument for Milne, *Algebraic Groups* (2017), Theorem 16.33(a)–(c), printed
pp.335–336 (zero-based PDF pages 350–351). The unchanged statement pair documents
the source correspondence, solvability convention and omitted quotient clauses;
the imported proof pairs document the separate structural arguments. No
quotient assertion is proved here.

Authors of this proof and its included helpers: Worker 1432 and Worker 1456.
