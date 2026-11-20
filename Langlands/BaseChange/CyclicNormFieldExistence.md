# Descent of the norm representative for field extensions

This file formalizes the companion matrix argument in the proof of part (i)
of Arthur–Clozel (1989), Chapter 1, Lemma 1.1, as used in Henniart–Lemaire
(2011), I.2.2. For each monic factor the columns are the coefficients of the
remainders of successive powers of `X`. Mathlib's quotient power basis
identifies the resulting matrix with multiplication by `X`. The entries
commute with change of coefficients because division with remainder by a
monic polynomial does.

Cayley–Hamilton makes the module of the norm product a torsion polynomial
module. Its ordered cyclic factors give a block companion form, with the
size of this matrix determined by the quotient power bases. The identity
`entrywiseAut_cyclicNorm`, together with `σ ^ l = 1`, conjugates the norm
product to its entrywise `σ`-image. The image has the companion form obtained
by applying `σ` to the coefficients of each factor. Conjugacy induces a
polynomial-module isomorphism, so uniqueness of ordered factors identifies
these two lists.

Every coefficient of every factor is therefore fixed by `σ`. The fixed
element clause of `IsCyclicAlgebra` lifts these coefficients to `F`, and
Mathlib's polynomial range lemma gives the lifted factors. Their block
companion matrix over `F` maps to the one over `E`. Its determinant is nonzero
because its image is conjugate to the norm product in `GL_n(E)`. This yields
the required base-field element and conjugator in `IsNormAssociated`. The
argument works for finite fields and keeps the universes of `F` and `E`
independent.
