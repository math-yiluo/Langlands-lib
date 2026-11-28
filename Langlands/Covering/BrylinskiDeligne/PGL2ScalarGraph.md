# Scalar graph quotient over PGL₂

Let \(R\) be a commutative ring, \(A\) an abelian group written
multiplicatively, and \(c : R^\times \to A\) a group homomorphism. In
`Langlands.Covering.BrylinskiDeligne.PGL2ScalarGraph`, `graph c` is the
range of the homomorphism \(u \mapsto (uI,c(u))\). The first coordinate
commutes with every invertible matrix by `GeneralLinearGroup.scalar_commute`,
and the second commutes with every coefficient because \(A\) is abelian.
`graph_le_center` combines the two equalities and gives the normality
instance for the quotient.

## The central extension

`Extension c` is the `QuotientGroup` by this subgroup, with surjective
quotient homomorphism `mk c`. The inclusion `inclusion c` sends \(a\)
to \([(I,a)]\). If this class is the identity, \((I,a)=(uI,c(u))\) for
some \(u\). Comparing the \((0,0)\) entries gives \(u=1\), so \(a=1\).
The inclusion has central image by commutativity of \((I,a)\) with each
pair before taking classes.

`projection c` sends \([(g,a)]\) to `Matrix.ProjGenLinGroup.mk g`.
`ProjGenLinGroup.mk_scalar` lets the first-coordinate map descend to the
quotient. Every projective class has a representative \(g\), so the
class of \((g,1)\) gives a preimage.

`mk_scalar` proves \([(uI,a)] = \iota(a\,c(u)^{-1})\), where \(\iota\)
is `inclusion c`. Indeed, right multiplication by \((uI,c(u))\) takes
\((I,a\,c(u)^{-1})\) to \((uI,a)\). Taking \(a=1\) gives `mk_scalar_one`.
In `ker_projection`, `ProjGenLinGroup.mk_eq_one` and
`GeneralLinearGroup.center_eq_range_scalar` give a representative of this
form for every class in the kernel. Every inclusion class projects to the
identity. `groupExtension` packages the two homomorphisms and their
exactness as a Mathlib `GroupExtension`, with `inclusion_le_center`
providing centrality.

## The lift with off-diagonal entries

`swapMatrix u` is the invertible matrix with rows \((0,u)\) and \((1,0)\).
Its supplied inverse has rows \((0,1)\) and \((u^{-1},0)\). Matrix
multiplication gives `swapMatrix_sq`, the identity \(w(u)^2=uI\).
`swapLift c u` is the class of \((w(u),1)\), and `projection_swapLift`
identifies its projection with the class of \(w(u)\).
`swapLift_sq` uses multiplicativity of `mk c` and `mk_scalar_one` to give
\(\operatorname{swapLift}(c,u)^2=\iota(c(u)^{-1})\).

## Restriction along a ring homomorphism

For \(f:R\to S\) and \(d:S^\times\to A\), `map f d` goes from the
extension for `d.comp (Units.map f.toMonoidHom)` to the extension for
\(d\). The entrywise matrix map takes a scalar graph pair to the graph
pair indexed by the image unit, so it descends with the coefficient
unchanged. `map_inclusion` and `projection_map` give compatibility with
the coefficient inclusion and the projective projection. `map_swapLift`
sends the lift for \(u\) to the lift for the image of \(u\).

For the inclusion of a valuation ring into its fraction field, the
source character is the restriction of the field character to the
valuation-ring units. For an integral unit \(u\), the associated projective
class over the field is the image of `ProjGenLinGroup.mk (swapMatrix u)`
over the valuation ring, by `ProjGenLinGroup.map_mk` and `map_swapMatrix`.

## Source

Gan and Gao, *The Langlands–Weissman program for Brylinski–Deligne
extensions*, Astérisque 398 (2018), §4.6, printed pp. 211–212
(one-based PDF pp. 229–230), give the point-group quotient with
\(c(u)=(\eta,u)_2\) and \(A=\mu_2\). The registered source is
`gan-gao-2018-langlands-weissman-program`, SHA-256
`fabbe056bdec2a5d57a22a0d3ad275640d0343c3f71092a7df427f7ebaebe892`.
The construction uses the same graph over a commutative ring with an
arbitrary abelian coefficient group. The square formula and the
restriction maps follow from the matrix identity and the graph relation.
