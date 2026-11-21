# The conductor identity for a p-adic norm pullback

For supplied p-adic field data on a finite abelian extension, the
local norm-pullback identity holds in independent carrier universes.
It computes the sum of the principal-unit conductors of the norm-trivial
twists from the conductor of the norm pullback, the residue degree and
the different exponent. This is the rank-one character arithmetic in
Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory
of the Trace Formula* (1989), Chapter 1, equation (6.7), expressed in
conductor exponents.

The Lean proof transports the extension to the Library's universe-zero
models, where the common finite Artin presentation applies. The unit
maps carry the finite set of norm-trivial characters bijectively onto
its counterpart by norm compatibility. The two Artin sums give the
model conductor identity. Pullback along the unit equivalences
transports the twist witnesses and the norm-pullback conductor, then
reindexing the finite sum gives the identity for the original fields.
