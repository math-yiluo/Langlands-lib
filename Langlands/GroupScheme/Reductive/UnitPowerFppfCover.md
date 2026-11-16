# Fppf covers adjoining roots of units

This internal algebraic construction adjoins roots of finitely many units over an arbitrary commutative ring. For a positive natural number `n` and a unit `a`, the equation is the monic polynomial `X^n - a`. Its quotient algebra is free over the coefficient ring and finitely presented; positive degree makes it faithfully flat. The proof treats the zero ring separately. The adjoined root is a unit because its positive power is the image of a unit.

Iterating the construction gives simultaneous roots of any finite list, preserving faithful flatness and finite presentation by composition. This is elementary commutative algebra implemented using Mathlib's `AdjoinRoot` power basis and ring homomorphism composition lemmas. No characteristic or invertibility assumption on `n` is imposed. It prepares explicit fppf covers needed in the semisimple commutator proof.

For an affine test scheme, `exists_roots_test` takes the spectrum of this extension of its global sections and composes with its canonical affine identification. It provides an affine source, a surjective flat locally finitely presented morphism, and the unit roots in the source's global sections. The equations identify each power with restriction of the original unit.
