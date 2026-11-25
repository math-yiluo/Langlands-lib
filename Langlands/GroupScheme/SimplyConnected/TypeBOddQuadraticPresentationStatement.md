# Odd quadratic presentations of simply connected type-B groups

`Langlands.GroupScheme.TypeBOddQuadraticPresentationStatement.{u}` is an
unproved general classification prerequisite. It applies to every field
`K : Type u`, every affine locally finite type group scheme `G` over
`Spec K`, actual Tits-index data `d`, and every numbering
`e : d.Vertex ≃ Fin n` matching every actual Cartan entry to
`CartanMatrix.B n`, for `n ≥ 3`. The group is assumed simply connected
and absolutely almost simple. There is no supplied quadratic form or
group presentation and no local-field, rank-one, perfection or
characteristic assumption.

The conclusion constructs an ordinary scalar quadratic form `q` on
`K^(2*n+1)`. It uses the published quotient-valued quadratic forms for the
identity involution of `K`, so a matrix `Q` represents
`x ↦ sum i j, x_i * Q_ij * x_j` and its polar matrix is `Q + transpose Q`.
The constructed form has zero quadratic radical: a vector with zero
quadratic value and zero polar pairing against every vector is zero.
The kernel of row multiplication by its polar matrix has dimension zero
when `2 ≠ 0` in `K`, and dimension one when `2 = 0` in `K`. In particular,
the assertion retains the regular odd-dimensional characteristic-two
case with singular polar matrix.

The conclusion also gives equality of the natural quadratic Witt index,
cast to `ℕ∞`, with the actual `splitRank G`, and an actual morphism
`π : G → normOneIsometryGroup q` which is a central isogeny. The target is
the kernel of actual reduced norm restricted to the actual isometry
scheme of `q`. In this scalar matrix algebra this is the
determinant-one condition. The isogeny requires a finite flat surjective
map, local finite presentation, and centrality of its full
scheme-theoretic kernel on every test scheme. This is a scheme-level
conclusion, including nonreduced tests. No separate construction of a
Clifford algebra or identification of the kernel with `μ₂` is asserted.

The accompanying conditional theorem
`localRankOneTypeB_false_of_oddQuadraticPresentation` assumes this general
statement and proves that an actual simply connected absolutely
almost-simple group of type `B_n`, `n ≥ 3`, over any nonarchimedean local
field cannot have split rank one. The proof extracts the radical-free
form and the rank equality, hence Witt index one in dimension
`2*n+1 ≥ 7`. The published scalar quadratic-form dimension bound says a
radical-free form of Witt index one has dimension at most six, giving
the contradiction. This consequence uses neither the polar-kernel
dimension clause nor the isogeny clause. It does not discharge the
general presentation statement or the other local index cases.

## Original sources and derived formulation

J. Tits, *Classification of algebraic semisimple groups* (1966),
Table II explanations, printed pp.54–55 / proceedings PDF pp.59–60,
and the type-B entry, printed p.56 / PDF p.61, describe the group by
`SO_(2n+1)(K,q)`, with quadratic form index equal to relative rank and
defect one in characteristic two. Source ID:
`tits-1966-classification-algebraic-semisimple`; PDF SHA-256:
`962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.
The source explains that these are rational-point descriptions of
strict-isogeny representatives. Its special-field rows are not inputs
to this general statement.

J. Tits, *Formes quadratiques, groupes orthogonaux et algèbres de
Clifford* (1968), §2.2, printed p.21 / PDF p.4, defines quadratic forms
as a bilinear-form quotient and defines nondegeneracy by zero quadratic
kernel and polar defect at most one. Section 2.3, printed p.22 / PDF
p.5, specializes the construction to the scalar case. Section 3,
printed p.30 / PDF p.13, defines the actual algebraic isometry and
reduced-norm-one isometry groups by their equations; Proposition 6
identifies their geometric forms. Its Remark 2 records the defective
characteristic-two exception for the full isometry group. Theorem 1 and
Remark 3, printed p.31 / PDF p.14, give the realization by a central
simple algebra and the relation of type-B groups to the universal
cover of an odd special orthogonal group. Source ID:
`tits-1968-formes-quadratiques-clifford`; PDF SHA-256:
`f8da4ecd4aae5bd5bbb3bc48873f285d7ccb058d771a5e9be855c867e391c782`.
The cited original pages were read.

This is a derived formulation combining these descriptions with the
Library's actual index, row-vector quadratic forms, actual norm
character and full-kernel central-isogeny convention. A proof must
construct the scalar form from the given type-B group, prove its stated
regularity, construct the actual central isogeny, and compare the
actual maximal split-torus rank with the quadratic Witt index. The
source's rational-point description alone does not prove any of those
scheme-level comparisons. The conditional local consequence is an
internal application of the separately proved quadratic dimension
bound.
