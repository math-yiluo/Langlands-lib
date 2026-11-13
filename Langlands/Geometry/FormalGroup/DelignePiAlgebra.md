# The graded coefficient algebra for Deligne's formal space

Drinfeld, *Coverings of p-adic symmetric regions* (1976), §2 A,
printed p.109 (PDF p.3), introduces B[Π] as the quotient of B[X] by
X^d−π. It has the cyclic grading with B in degree zero and Π in
degree one. This is the coefficient algebra for the sheaves in his
description of Deligne's formal space; the conditions on those sheaves
continue on printed p.110 (PDF p.4).

`PiAlgebra d a` is that actual polynomial quotient, implemented with
Mathlib's `AdjoinRoot`. The element `pi` satisfies Π^d=a.
For nonzero d its power basis is indexed by Z/dZ. The degree-i
component is the B-span of Π raised to the least nonnegative
representative of i. These components form an internal direct sum;
one has degree zero and multiplication adds degrees. The proof
reduces any exponent n to n modulo d, introducing the coefficient
a^(n/d). In particular Π has degree one. The construction permits the
zero coefficient ring: its basis and direct sum assertions have their
usual trivial-module meaning.

The actual quotient algebra is finite and free over B. If a is
nilpotent, Π is nilpotent, by its defining power relation. No
nilpotence exponent is chosen as extra data.

`piAlgebraMap` extends a coefficient O-algebra map to these quotients
and fixes Π. The identity and composition laws give an actual functor
on commutative O-algebras and its restriction to the previously
constructed `Nilp O π` category.

The implementation is the direct algebraic construction in the cited
paragraph, with the finite-free and functoriality lemmas proved
internally. This module does not yet construct the graded sheaves,
their admissibility conditions, Deligne's Nilp-point functor or its
projective linear action. It makes no representability or generic
fibre claim.
