# Determinant-unit Levi structure

Author: Worker 76.

`Langlands.CuspidalSupport.LeviDeterminantUnitStructureTheorem F T B`
is a proposition for every prime `p`, actual field `F : PadicField p`,
compatible realization `T : F.TopologicalData`, natural rank `n`, and
ordered positive block shape `B : Langlands.GeneralLinear.BlockShape n`.
The field carrier has arbitrary universe `uF`. There is no positive-rank
hypothesis.

Put `G = B.Levi F.Carrier` and
`H = Langlands.CuspidalSupport.determinantUnitSubgroup T B`. Thus `G` is
the actual product of general linear groups, and membership in `H` means
that every block determinant has residue-normalized absolute value one.
The proposition states the following conjunction, in this order:

1. For all `x y : G ⧸ H`, `x * y = y * x`. This uses the actual quotient
   group multiplication induced from `G`.
2. `(H ⊔ Subgroup.center G).FiniteIndex`: adjoining the actual center gives
   a subgroup of finite index in `G`. Mathlib's `Subgroup.FiniteIndex` is
   equivalent to finiteness of the corresponding coset type.
3. `IsCompact ((H ⊓ Subgroup.center G : Subgroup G) : Set G)`: the
   intersection with the actual center is compact as a subset of `G`.

The definition explicitly installs `T.topology` before forming these
conclusions. The ambient Levi therefore carries the product of the actual
matrix-unit topologies induced from that field topology. Compactness is
ambient subset compactness, with no chosen finite model or replacement
topology.

The imported `Langlands.Representation.CuspidalSupport.DeterminantUnit`
provides the subgroup and its proved normality instance
`determinantUnitSubgroup_normal`, which supplies the quotient group
structure. Its theorem `isOpen_determinantUnitSubgroup` already proves
openness for the same `T.topology`. Neither fact is an extra hypothesis
or a new proof obligation here; users can reuse these imported results
alongside this structural target. All imported Library pairs are unchanged.

The original source is I. N. Bernshtein and A. V. Zelevinskii,
*Representations of the group GL(n,F), where F is a non-Archimedean local
field*, Russian Mathematical Surveys 31:3 (1976), 1–68, English translation,
Chapter II, section 3.20(a)–(b), printed page 34 (PDF page 34).
Registered source ID: `bernstein-zelevinsky-1976-representations-gln`.
PDF SHA256:
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
The source passage and the neighboring printed pages 33–35 were read.

The source's `G°` is this blockwise determinant-unit subgroup. Its
section 3.20(a) supplies compactness of `G° ∩ Z`; section 3.20(b) supplies
commutativity of `G/G°` and finiteness of `G/(G°·Z)`. The subgroup join
in the Lean statement represents `G°·Z`, since the center commutes
with every element and the two subgroups normalize each other. The
additional congruence-subgroup containment in section 3.20(a) is outside
this target.

The rank-zero case is an internal extension of the source's block notation.
Positive block sizes summing to zero force an empty block family. The Levi
is then the one-element empty product, as are both quotient groups; the
central intersection is a singleton. Thus the same three conclusions make
sense without any exception or nonempty-block hypothesis.

This pair states the structural result as a `Prop`-valued definition; it
does not prove or assume it. A proof is a separate task after publication.
It asserts no Harish-Chandra equivalence or representation-theoretic
semisimplicity result.
