# The positive-characteristic endomorphism-map input

`Langlands.GroupScheme.SimplyConnectedPositiveCharConjugationMapStatement`
is an unproved proposition for an algebraically closed field `k : Type u` of
prime characteristic `p` and an actual simply connected semisimple `k`-group
scheme `G`. Simple connectedness has the Library's algebraic meaning and
includes semisimplicity. The universe `u` is arbitrary.

For every actual finite coordinate representation `ρ` of `G` and every nonzero
vector `v` fixed on points over every test scheme, the proposition asks for a
positive integer `m`, an actual representation `σ` of `G` on `k^(Fin m)`, a
`ConjugationLinearMap ρ σ`, and a nonzero scalar `a` such that the linear matrix
at `v` is `a` times the identity. The map intertwines `ρ` with conjugation by `σ`
on section-valued vectors over every test scheme, as required by the imported
definition. Neither the representation nor its equivariance is replaced by
rational-point data.

This is an internal interface extracted from Mumford, Fogarty and Kirwan,
*Geometric Invariant Theory*, third enlarged edition (1994), Appendix to
Chapter 1, Section A, printed pp.191–192, especially the proof sketch of
Theorem A.1.0(a) implies (b) on p.192. The registered source is
`mumford-fogarty-kirwan-1994-git-3rd`, SHA-256
`25b78ea299e007fbabefb23e9dd7d30beba86c5c1eaa9718b8cc3f98f54932b2`.
That sketch reduces to the simply connected semisimple case, maps the
representation into the endomorphisms of a self-dual Steinberg module, and
sends the fixed vector to a nonzero scalar identity. The present interface
retains that conclusion. It does not specify a Steinberg module or assert the
stronger power-of-`p` dimension bound.

The source first treats suitable coordinate-ring subrepresentations. Passing
from an arbitrary supplied representation and nonzero fixed vector to that
setting, constructing the relevant modules and maps, and establishing their
scheme-theoretic equivariance are obligations of a proof of this proposition.
No such proof is supplied here. The determinant construction explains the
interface's use: the matrix at `v` has determinant `a^m`, so the positive-size
determinant yields a positive-degree invariant polynomial nonzero at `v`.
The general reductive case additionally needs structural reductions and
invariance descent. This statement asserts neither those reductions nor
Haboush's theorem, and its publication as a statement would not supply them.
