# Realization of split finite Brauer data and real unitary signatures

`Langlands.Shimura.FiniteUnitary.UnitaryLocalProfileRealizationStatement`
is the existence direction of Clozel's local compatibility criterion for
unitary pairs, specialized to the maximal-Witt pair at every finite place
outside a supplied finite set of split places. The real signature and the
Brauer class at each selected split place are arbitrary, subject to
reciprocity. The fields, quadratic map and finite places are actual inputs.

For each selected split place the input orients its two places above it by
selecting one of them. A residue `a` in `ZMod n` prescribes the invariant
`a/n` modulo the integers over the selected place and its negative over the
other place. `finiteBrauerInvariant` composes the Library's actual Brauer
comparison with the cohomological local invariant for the existing finite
completion. `HasCompletedBrauerInvariant` ties that value to the actual
completed algebra by an algebra equivalence over the completed center.
The representative lies in the center's universe so it can be used in the
current Brauer group. The original completed algebra can lie in a larger
universe.

In even rank `n = 2m`, each split residue maps to its reduction modulo two.
A real signature with `r` positive lines contributes `m + (n − r)` modulo
two, the same value as `r − m` in Clozel's convention. The maximal-Witt
pair contributes zero at the other finite places. The compatibility
condition is the vanishing of the sum of these contributions. Odd rank has
no compatibility condition. It is immaterial which place above each split
place is used to give the orientation if the coefficient changes sign with
the orientation.

The conclusion provides a degree-`n` central simple algebra over the
given CM field and an involution inducing the specified conjugation. It
carries the actual involution-preserving real signature charts and the
center- and involution-compatible maximal-Witt finite charts. At the
selected places it gives the Brauer invariants of the actual completed
algebras. The algebra is allowed to be a matrix algebra, and the
prescribed profile may be empty.

The source is Laurent Clozel, *Représentations galoisiennes associées aux
représentations automorphes autoduales de GL(n)*, IHÉS 73 (1991), §2.1,
printed pp. 102–105. Equation (2.2) gives sufficiency of the local
compatibility condition, (2.3) computes the finite contributions, and
Lemmas 2.1 and 2.2 give the odd-rank and archimedean computations. The
adjoint quasi-split unitary group used there is the group of
center-preserving automorphisms of the split reference pair, so its
localized cohomology classes describe pairs up to center- and
involution-preserving isomorphism. Registered source
`clozel-1991-selfdual-galois`, SHA256
`9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`.
