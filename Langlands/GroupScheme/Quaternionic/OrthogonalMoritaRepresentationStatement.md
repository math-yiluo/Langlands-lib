# Existence of an orthogonal Morita comparison of the row representation

`OrthogonalMoritaRepresentationStatement` is an unproved proposition at every
universe `u`. It is a prerequisite for comparing the row weights in
`SpinCoverVectorWeightsStatement` with the explicit split orthogonal model.
This file states the prerequisite and proves nothing.

Let `K` be any field and `D` a finite-dimensional central division `K`-algebra.
Let `degree > 0`, `n ≥ 4`, `dim_K D = degree²`, and `m * degree = 2 * n`.
Let `σ` be an involution of the first kind satisfying
`dim_K σ.symmetricSubspace = degree * (degree + 1) / 2`.
For any nondegenerate `σ`-quadratic form `q` on `D^m`, the statement asks for
an `OrthogonalMoritaComparison σ q L degree n` over every algebraically
closed field extension `L/K` in the same universe.

The comparison is the one in `OrthogonalMoritaRepresentation`. It includes
an actual isomorphism over `Spec L` from the base change of `O(q)` to the
explicit `OrthogonalMatrix.groupScheme (Fin n)`, and an `L`-linear equivalence
from `L ⊗[K] D^m` to `degree` copies of `L^(Fin n ⊕ Fin n)`. Its canonical
extension to every commutative coefficient `L`-algebra intertwines the
actual inverse-right actions. Thus the conclusion records a comparison of
representations over all coefficient algebras, in addition to an abstract
isomorphism of groups.

There is no assumption about a spin cover, a pinning, the base field being
infinite or perfect, or its characteristic. In particular, finite base
fields and characteristic two are included. The rank restriction `n ≥ 4`
is the range required by the consuming type-D statement.

## Source and the additional representation clause

The source is J. Tits, *Formes quadratiques, groupes orthogonaux et algèbres
de Clifford*, Inventiones mathematicae 5 (1968), 19–41, source ID
`tits-1968-formes-quadratiques-clifford`. For the registered scanned copy,
PDF page number equals printed page number minus 17.

Section 2.1, printed p. 20 (PDF p. 3), calls an involution of degree `d`
type 1 when its symmetric subspace has dimension `d(d+1)/2`. It constructs
the corresponding space of bilinear forms and proves uniqueness up to
isomorphism. Section 2.2, printed p. 21 (PDF p. 4), defines quadratic forms
as `B / {b - π(b)}` with bilinearization `b + π(b)`. In even reduced degree,
nondegeneracy means that this bilinearization is nondegenerate. The
scalar-extension paragraph on printed p. 22 (PDF p. 5) identifies the
extended bilinear, symmetric, alternating and quadratic spaces.
Section 2.3 on that page identifies the matrix-algebra realization with
sesquilinear forms on its simple module.

In Section 3, printed p. 30 (PDF p. 13), Tits describes `GL(E)` by units
over every coefficient algebra and `U(q)` by the equation preserving `q`.
Over an algebraically closed field the isometry group and its standard
embedding depend only on the reduced degree and the field; Proposition 6
asserts that `U(q)` is a form of the corresponding orthogonal group.
Here the central simple algebra is `E = M_m(D)` of reduced degree `2n`.
The dimension of the fixed matrices of its conjugate-transpose involution
is

`m * degree * (degree + 1) / 2 + m * (m - 1) * degree² / 2
 = (m * degree) * (m * degree + 1) / 2`.

Thus the hypothesis on `σ` is exactly the type-1 condition in this matrix
realization. The published `QuadraticForms` is the quotient in Section 2.2,
and `IsNondegenerateQuadratic` requires its polar Gram matrix to be a unit.
The reduced degree `2n` is even, so this is the indicated source notion
of nondegeneracy in characteristic two as well.

The precise row-multiplicity and canonical-extension clauses are a derived
formulation, not a separately printed assertion of Proposition 6.
After splitting `L ⊗[K] D` as `M_degree(L)`, a row in `D^m` becomes a
`degree` by `m * degree` matrix. Its `degree` rows give `degree` copies of
the simple row module. Right multiplication acts separately on each row.
Conjugating the matrix-algebra realization and then choosing a hyperbolic
basis for the nondegenerate even-dimensional quadratic form gives the
split orthogonal comparison. The same matrix formulas extend to every
coefficient algebra. Replacing each group matrix by its inverse gives
the inverse-right convention used in the published row action. This
explains the intended representation clause; carrying out those
constructions and proving the coefficient-algebra identities is part of
the remaining proof obligation.

The existing `QuaternionicMoritaIsometryStatement` is the degree-two
group-isomorphism comparison with an ordinary quadratic form. The present
target permits arbitrary degree, specifies the hyperbolic split model,
and retains the row representation. It neither assumes that earlier
statement nor establishes the numbered vector characters or the
spin-cover weight formula.
