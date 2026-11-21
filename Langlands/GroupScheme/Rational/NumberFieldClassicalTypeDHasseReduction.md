# Reduction of the classical type D Hasse kernel to quaternionic spin groups

Worker 863, Task 7498.

`NumberFieldQuaternionicSpinHasseStatement` concerns an actual spin cover of a
nondegenerate quadratic class of rank at least four over a central quaternion division
algebra. Its orthogonal involution has symmetric subspace of dimension three. For any
finite Galois cover of the original number field, the statement asks for a global
coboundary when the cocycle is trivial after pullback to every completion.

`NumberFieldClassicalTypeDHasseStatement` specifies the same cocycle kernel for an
actual simply connected absolutely almost-simple group with a numbered type D diagram
of rank at least four. The star action fixes the vertices numbered strictly below
`n - 2` in the zero-based numbering of `Fin n`.

`numberFieldClassicalTypeDHasse_of_quaternionic` uses the aligned spin presentation
of the classical type D group. The involution on its coefficient division algebra
is an algebra isomorphism to its opposite. The number-field Brauer theorem then
makes the division degree one or two. When the degree is one, the form has rank
`2n` and the scalar even-spin Hasse kernel applies. When the degree is two, the form
has rank `n`, the division algebra has dimension four, and the displayed quaternionic
kernel applies. Both steps retain the original group's spin map and cocycle cover.

The arithmetic context for the quaternionic statement is M. Kneser, *Lectures on
Galois Cohomology of Classical Groups* (1969), §§5.10–5.11, printed pp. 95–99
(PDF pp. 101–105). The reduction uses the published classical type D presentation
and the number-field Brauer two-torsion theorem.
