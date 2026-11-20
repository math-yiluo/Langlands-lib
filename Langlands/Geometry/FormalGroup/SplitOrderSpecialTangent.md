# Structural scalars and special tangent characters of the division summand

`HasStructuralDivisionTangent` expresses structural scalar action
over the entire coefficient ring. The derivative of a central scalar
in the division-order factor is the structural scalar times the
division projector. This is equivalent to scalar multiplication on
the image of the projector over the base ring. The full coefficient
identity also gives the scalar equation over every test ring. Its
proof evaluates the derivative at the coordinate basis vectors,
maps the resulting coefficient equalities, and reassembles the
derivative.

`HasGeometricDivisionTangentCharacters` gives a decomposition of
the actual division tangent into one-dimensional, pairwise distinct
characters of the embedded commutative ring at each algebraically closed
field test in `Type (max w q)`, where the base ring has type `Type w`.
This universe contains a lifted algebraic closure of the residue
field at each prime of the base. The character count is the dimension
of the tested tangent summand. When the structural scalar condition
holds, the characters restrict to the structural character on the
scalar subring. Coefficient extension preserves both conditions using
a common test universe containing both base universes. Actual
order-linear formal isomorphisms preserve the conditions.

These are the structural scalar and multiplicity-one conditions
used for the special factor in Rapoport–Zink (1996), Definition 3.57
and §3.58, printed pp. 109–110 (PDF pp. 123–124), and in their split
calculation, §6.43, printed pp. 308–309 (PDF pp. 320–321).
The formalization takes the integer embeddings as parameters. It
supplies the tangent conditions needed on that factor when the
embedded ring is the unramified integer subfield of full degree.
