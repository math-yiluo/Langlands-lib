# Split solvable groups are trigonalizable

`Langlands.GroupScheme.splitSolvableTrigonalizable` proves
`SplitSolvableTrigonalizableStatement.{u}`, the formalization of Milne,
*Algebraic Groups* (2017), Proposition 16.52 (printed p. 343). For smooth
connected affine groups, split solvability implies trigonalizability over any
field, and the converse holds over a perfect field.
[Formal statement and source comparison](SplitSolvableStatement.md)

The forward implication reindexes each matrix representation of positive
dimension to `Fin (m + 1)` and lets the group act on its projective space.
The space is proper, hence pseudo-complete, and a coordinate line supplies
the required rational point. The split-solvable fixed-point theorem gives a
rational point fixed on every relative test scheme. This point is an invertible
matrix translate of a coordinate section. Its associated vector is nonzero,
and on each test scheme the action sends its scalar extension to a unit
multiple of itself. Reindexing returns the vector in the original coordinates.

For the converse, `trigonalizableCharacterization` gives an fppf quotient by
a closed unipotent subgroup onto a diagonalizable group with finitely generated
character group. The quotient inherits smoothness and connectedness, so its
character group is free and the quotient is a split torus. The extension by
the unipotent kernel makes the original group solvable.

Over a perfect field, the geometric unipotent radical descends to the ground
field, is split unipotent and has a torus quotient. Each of the two unipotent
subgroups maps trivially to the other's torus quotient. Since both subgroups
are the full kernels of their respective quotients, their ranges coincide on
every test scheme. The split-unipotent series of the geometric radical and
the split torus quotient give the required split-solvable series.
