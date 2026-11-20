# Standard Levi fixed-vector support

`standardLeviFixedVectorSupport` proves
`Langlands.CuspidalSupport.StandardLeviFixedVectorSupportStatement.{uF,uV}`.
This is Renard's VI.10.6 Corollary for the standard Levi \(M=M_J\) at the
prescribed compact open level \(K\). The proof uses the target's canonical
rational-point topology and standard Bernstein family. The level on \(M\)
is the preimage of \(K\) along the subgroup inclusion. It is open by
continuity and compact by the closed embedding of \(M\).

The proof applies `nontrivial_standardLeviInduction_fixedVectors_iff` to
compare nonzero fixed vectors of a normalized induction inside \(M\) and
of its coefficient, each at the literal intersection with \(K\). That
criterion uses normalized induction in stages and the ambient fixed-vector
criterion at both standard indices. The given Iwahori hypothesis specializes
to each of those indices using `rootSet_subset`. The proof extends the
inside-Levi comparison to the target's equality `leviIndex J I = R` by
formulating it for an arbitrary `R` and substituting along the equality.

In the forward direction, the witness \(\tau\) is an irreducible subquotient
of the induction inside \(M\) of a datum \(b'\). Compact-open fixed-vector
exactness gives a nonzero fixed vector of that induction. The inside-Levi
criterion then gives a nonzero fixed vector of the coefficient of \(b'\).
The reverse implication of `standardRepresentativeFixedVectorCriterion`
provides an ambient irreducible representation with nonzero \(K\)-fixed
vectors and the inertial class of \(b'\). The target's conjugacy in \(M\)
and inertia relation also give an ambient inertia relation. The quotient
class equality identifies this support with the class of the original
datum \(b\).

In the reverse direction, the forward implication of
`standardRepresentativeFixedVectorCriterion` gives a nonzero fixed vector
of the coefficient of \(b\) at its Levi intersection. The proof takes the
finite subset `I` of the roots in `J` defined by `b.roots`. The equality
`leviIndex J I = b.roots` follows from `Finset.subtype_map_of_mem`.
The inside-Levi criterion gives nonzero fixed vectors in the induction of
\(b\) inside \(M\). `SmoothRep.hasFixedVectorConstituent_of_nontrivial`
produces an irreducible subquotient retaining a nonzero fixed vector. The
proof uses \(b\) itself as the Levi datum, with identity conjugacy and the
identity pullback isomorphism for the inertia relation.

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition of 9 July 2026, VI.10.6, printed pp. 213–215
(PDF pp. 219–221), registered as
`renard-2026-representations-groupes-reductifs-padiques`. The inside-Levi
comparison is implemented by induction in stages as described above.
