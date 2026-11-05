# The reductive identity-component locus

For a smooth affine group scheme `G` over an arbitrary scheme `S`,
`identityComponentReductiveLocus G` consists of the points `s` for which the
actual identity component of `geometricFiber G s` is connected reductive.
The geometric fibre is the actual pullback along
`Spec (AlgebraicClosure (S.residueField s)) → S`; the identity component is
the existing open and closed subgroup scheme over that field. No relative
identity-component model is supplied or assumed.

`IdentityComponentReductiveLocusOpenStatement.{u}` asserts that this set is
open, uniformly for all schemes and smooth affine group schemes in universe
`u`. The proposition has no Noetherian, integral-base, split-torus, or
connected-fibre hypothesis.

The source is Brian Conrad, *Reductive group schemes* (2014), Proposition
3.1.9(1), printed/PDF pp.85–88, with the field and relative reductivity
conventions of Definition 3.1.1 and its discussion on pp.81–82. The source's
pointwise assertion that a reductive fibre identity component remains
reductive on an open neighbourhood is expressed as openness of its locus.
Choosing one algebraic closure of each residue field matches the source's
geometric-fibre formulation. This file states the reductivity assertion;
the source's additional semisimplicity and maximal-torus assertions are
outside this proposition.

The two comparison lemmas are derived from existing Library transport
results. When the whole geometric fibre is connected, its identity-component
inclusion is an isomorphism. Transport across the inverse of this
isomorphism proves connected reductivity of the whole fibre from membership
in the locus. A connected reductive group has trivial ground-field
unipotent radical. Conversely, on the chosen algebraically closed residue
field, smoothness, affineness, connectedness and a trivial ground-field
unipotent radical give pseudo-reductivity, hence connected reductivity;
passing to the identity component gives membership in the locus. Thus the
stated equivalence concerns the actual geometric fibre's existing radical
predicate, including all its smooth connected normal unipotent closed
subgroup schemes and equality of subgroup functors on every test scheme.

The openness proposition is a structural proof obligation, not a proved
theorem in this file. The comparison lemmas do not establish openness or
generic spreading.
