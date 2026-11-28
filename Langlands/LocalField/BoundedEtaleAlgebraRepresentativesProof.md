# Finite representatives of bounded-dimensional étale algebras

`Langlands.LocalField.boundedEtaleAlgebraRepresentatives` proves
[`BoundedEtaleAlgebraRepresentativesStatement`](BoundedEtaleAlgebraRepresentativesStatement.md).
Let \(S\) be the finite set of intermediate fields of \(\overline F/F\) of finite
degree at most \(d\). The proof uses the type `Σ m : Fin (d + 1), Fin m.val → S`
of lists of length at most \(d\). The finiteness of \(S\) makes this type finite,
so `Fintype.equivFin` enumerates it by `Fin n`. The model for a list is the
product of its fields with the pointwise \(F\)-algebra structure. The empty
list gives the empty product.

For an étale \(F\)-algebra \(A\), `Algebra.Etale.iff_exists_algEquiv_prod`
gives an \(F\)-algebra equivalence with a finite product of finite separable
field extensions. The equivalence preserves dimension, and
`Module.finrank_pi_fintype` expresses the product dimension as the sum of the
factor degrees. Each degree is positive, so the sum bounds the number of
factors. The sum also bounds each individual degree. Both bounds therefore
follow from \(\dim_F A \le d\).

After reindexing the factors by `Fin` of their number, `IsAlgClosed.lift`
embeds each factor into `AlgebraicClosure F`. The algebra equivalence with
its field range transfers its finite-dimensionality and degree bound to that
range, placing the range in \(S\). The resulting list determines a model.
The proof composes the étale product equivalence, the reindexing equivalence
and the product of the field-range equivalences to obtain the required
\(F\)-algebra equivalence with that model. The models live in the carrier
universe of \(F\), and the input algebra may have an independent carrier
universe.
