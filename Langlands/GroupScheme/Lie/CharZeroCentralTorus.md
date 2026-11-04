# Central semisimple tangents in characteristic zero

This internal supporting unit proves
`CharZeroSemisimpleCentralNilpotenceStatement.{u}`. Over an algebraically
closed field of characteristic zero, a smooth connected affine group is
geometrically nilpotent if every actual semisimple Lie element has full
Lie centralizer.

The proof first treats an arbitrary split-torus map over a characteristic
zero field. Full Lie centralizers for its tangent images say precisely
that their actual adjoint differentials vanish. Natural finite Lie
coordinates identify these differentials with the tangent matrices of
the actual adjoint representation. The differential of its restriction
to the torus is therefore zero. The previously proved split-source
zero-differential theorem makes this restricted group-scheme
representation trivial.

The same natural finite coordinates identify the representation action
with the actual adjoint action over every commutative coefficient algebra.
Triviality consequently makes every Lie vector an invariant of the
torus conjugation action. The published rigidity theorem for
diagonalizable actions on smooth connected affine groups then makes
the whole action trivial on every scheme test. Thus the split-torus map
is central.

Over the algebraically closed base, choose an actual maximal torus and
split it by the proved finite Galois splitting theorem. Every tangent
image of this torus is representation-semisimple, so the hypothesis
applies and the preceding centrality criterion makes this maximal torus
central. The actual quotient and central-extension theorem from
`Nilpotent.EmptyRoots` now give geometric nilpotence, using the previously
proved algebraically closed no-cocharacter criterion.

All assertions are internal deductions from the imported constructions.
The characteristic-zero restriction is essential to the vanishing step.
This unit does not assert the positive-characteristic iteration or the
arbitrary-field no-torus unipotence theorem.
