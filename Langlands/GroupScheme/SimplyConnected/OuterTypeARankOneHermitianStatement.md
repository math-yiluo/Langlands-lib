# Actual Hermitian models from the rank-one outer-A index

Author: Worker 165.

`Langlands.GroupScheme.OuterTypeARankOneHermitianStatement.{u}` is an
unproved identification statement. It supplies the outer-A case needed
after the separate local enumeration of actual Tits indices. It does not
prove either the enumeration or the local rank-one classification.

Let `K : Type u` be any field. Let `G` be an affine, locally finite type
group scheme over `Spec K`, and let `d : TitsIndexData G` be actual index
data. For a natural number `n`, assume that `G` is simply connected and
absolutely almost simple, that `d.HasRankOneOuterAIndex n`, and that
`splitRank G = 1`. The statement asserts the existence of a separable
quadratic field extension `L : Type u` of `K`, an anisotropic diagonal
Hermitian form `H` for `SU3Root.fieldInvolution K L` on `Fin (n - 1)`,
unit witnesses for all its weights, and an actual group-scheme
isomorphism

```text
G ≅ HermitianRoot.SchemeModel.groupScheme K L H w hw.
```

The imported actual-index predicate requires `n = 2` or `n = 3`.
It compares every Cartan entry with `CartanMatrix.A n`, identifies
exactly the two endpoints as distinguished, and identifies the full
absolute Galois star image with the identity and chain reversal.
The extension, form and isomorphism are conclusions; none is a field
of the supplied index data or an additional presentation hypothesis.

The model has one hyperbolic plane and the anisotropic middle `H`,
so its Hermitian dimension is `(n - 1) + 2 = n + 1`: dimension 3
for `n = 2`, and dimension 4 for `n = 3`. The middle dimension is
therefore 1 or 2, as in family (ii) of
`LocalRankOneClassificationStatement`. The actual equalizer model
uses determinant-one Hermitian isometries on every test scheme,
not only on field-valued points. The unit witnesses make its
nondegenerate diagonal coefficients explicit.

The statement is over arbitrary fields. The small ranks and
distinguished endpoints are already hypotheses about the actual
index, so no local-field arithmetic is needed to restrict the
dimension in this identification step. Both fields use an arbitrary
common universe `u`. There is no restriction on characteristic,
including characteristic 2; separability is required of the quadratic
extension.

## Original source and derived formulation

The source is J. Tits, *Classification of algebraic semisimple
groups*, Proc. Sympos. Pure Math. 9 (1966), 33–62,
`tits-1966-classification-algebraic-semisimple`. The registered
proceedings PDF has SHA-256
`962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.
Table II's explanations, printed pp.54–55 / PDF pp.59–60,
and its outer-A entry, printed p.55 / PDF p.60, are the relevant
original passages. The table is over arbitrary fields; its later
special-field lines are additional restrictions.

For outer `A_n`, the table describes the group using a central
division algebra of degree `d` over a quadratic extension, an
involution of the second kind, and a nondegenerate Hermitian form
of Witt index `r`. The distinguished orbits have first pair
`(d, n + 1 - d)`. In the predicate used here the distinguished
vertices are exactly the endpoints, forming one orbit under
reversal. Thus the corresponding description has `d = 1` and
`r = 1`. The algebra is the quadratic extension field itself,
the Hermitian dimension is `n + 1`, and removing a hyperbolic
plane leaves an anisotropic middle of dimension `n - 1`.
The ranks `n = 2,3` are supplied by the actual-index hypothesis;
the local enumeration that obtains them is a separate obligation.

This is a derived formulation using the Library's actual index
and actual Hermitian group scheme. Tits explicitly describes a
representative of each strict isogeny class by its rational points.
The Lean conclusion instead identifies the original simply
connected group scheme with the determinant-one equalizer model.
A proof must justify the simply connected representative, the
separable quadratic extension, Hermitian presentation, Witt
decomposition, diagonal coordinates and scheme isomorphism.
The source's rational-point description alone is not a supplied
all-test equivalence or a Lean proof of these constructions.

## Existing constructions and remaining proof

`HermitianRoot.SchemeModel.isoOfMatrixPoints` can reconstruct the
actual group-scheme isomorphism once compatible matrix equivalences
on every test scheme have been constructed.
`HermitianRoot.SchemeModel.isometryIso` transports existing models
along a supplied Gram isometry.
`HermitianRoot.exists_anisotropic_diagonal_coordinates` supplies
diagonal coordinates for an already supplied anisotropic Hermitian
space, and `HermitianRoot.DiagonalForm.exists_unitWitnesses`
supplies its weight units. None constructs a Hermitian presentation
of an arbitrary group from its actual index.

The new declaration is a closed `Prop`-valued definition, with no
proof theorem. In particular it does not assume or prove the
classification of local fields' anisotropic groups, the admissibility
or enumeration of local indices, or the quaternionic alternatives.
Its focused proof remains necessary before it can be used without
an explicit premise in the final classification.
