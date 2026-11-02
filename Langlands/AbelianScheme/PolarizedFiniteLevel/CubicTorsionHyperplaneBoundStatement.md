# The actual torsion-hyperplane count for a supplied cubic embedding

`CubicTorsionHyperplaneBoundStatement` is a geometric theorem target for the
actual ordinary polarized datum, rather than a bound assumed of an abstract
configuration. It states a uniform bound on the number of its actual
`n`-torsion points in a hyperplane of a supplied cubic embedding.

The quantifiers range over the existing `Prerequisites.{u}`, every algebraically
closed field `K : Type u`, positive `g`, `d`, and `n`, with `(n : K) ≠ 0`, and
every actual `Datum P (Spec K) g d n`. The datum includes the original relative
dimension `g`, polarization of degree `d^2`, per-datum dual witnesses, and
ordered full level at every geometric fibre. No global dual-existence
hypothesis or coprimality condition on `d` and `n` is added.

For every `m`, the supplied morphism
`i : a.abelian.X.left -> ProjectiveSpace K m` must satisfy all of the following:

- it is an actual closed immersion;
- its composite with the actual projective-space structure morphism is
  `a.abelian.X.hom`;
- the actual sheaf pullback `i^*(twistOne K m)` is isomorphic to
  `a.cubicBundle.obj`;
- its image is contained in no hyperplane.

Here `ProjectiveSpace` is the existing polynomial `Proj`, and `twistOne` is its
actual degree-one twisting sheaf. The third condition concerns actual sheaves,
not a chosen vector space or an asserted numerical degree. The last condition
is expressed directly: every nonzero polynomial in the degree-one homogeneous
submodule fails to belong to the homogeneous prime of `i x` for some point
`x` of the actual abelian scheme.

For each such nonzero degree-one polynomial `f`, the conclusion is

`Nat.card {x : A[n](K) // f vanishes at i(x)} <= 6^g * d * g! * n^(2*g-2)`.

The type `A[n](K)` here is precisely
`GroupScheme.Tate.Level a.abelian.toGrp (Over.mk (identity Spec K)) n`.
Each of its elements is an actual section over `Spec K` killed by
multiplication by `n`. Its underlying section morphism is evaluated at
`IsLocalRing.closedPoint K`, followed by `i`. Vanishing means membership of
`f` in the resulting point's actual homogeneous prime ideal. Thus the count
includes all points killed by `n`, not only points of exact order `n`, and it
does not count a freely supplied configuration. The full-level basis already
identifies this torsion module with `Fin (2*g) -> ZMod n`; positive `n` makes
it finite. Consequently `Nat.card` is an ordinary finite count in this
statement. This finiteness uses the supplied level and asserts no new
unconditional torsion-rank theorem.

The source is Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, third
edition (1994), Chapter 7, Proposition 7.7 and its proof, printed pages 138-139 /
one-based PDF pages 151-152. It is registered as
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.
The supplied file is named *Chapter 6.pdf* but contains the full book.
The proof bounds the hyperplane count by `r*n^(2*g-2)`, where `r` is the
degree of the embedded image, before imposing the additional strict inequality
used for stability. The count itself therefore needs no lower bound on `n`
beyond positivity and invertibility in `K`.

This statement is an internal specialization of that geometric estimate to
the canonical cubic bundle of the published datum. Definition 7.5, printed
page 130 / PDF page 143, uses the cube of the diagonal Poincare bundle for a
polarization of degree `d^2`. The following construction, printed page 131 /
PDF page 144, gives its Hilbert polynomial `6^g*d*T^g`. The projective degree
is `g!` times the leading coefficient, namely `6^g*d*g!`. Over the field,
the possible line-bundle factor pulled back from the base in the source's
embedding formula is trivial. The explicit pullback comparison above states
the resulting cubic-bundle convention without constructing that embedding.
The source's polynomial and its hyperplane estimate were also checked in the
page images; no registered erratum for this source was found.

This module states the estimate and does not prove it. It supplies no
embedding, projective-coordinate comparison, projective group action,
automorphism faithfulness, quotient or moduli representation. In particular,
it leaves the exact `LargeLevelRepresentabilityStatement` unproved.
