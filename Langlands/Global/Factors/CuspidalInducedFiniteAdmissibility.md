# Admissibility of the finite cuspidal induction tensor

`Langlands.Global.CuspidalInducedFiniteTensor.sourceFiniteAction` is the
restricted tensor of the canonical normalized local block inductions from
the cuspidal presentations in their original order. Its reference family
can be any family fixed by the integral groups outside the exceptional set.
`sourceTensor_isAdmissible` proves admissibility when these references are
nonzero outside that set. The result applies to the source of the
subquotient used in the isobaric realization argument.

At each finite place, `FiniteTensor.isAdmissible_external` and
`Parabolic.normalizedInductionAdmissibility` give admissibility of the local
induction. `localGL_topology_eq` identifies the canonical p-adic topology
with the actual completion topology. Outside the union of the
presentations' exceptional sets, the inducing factors have spherical
spectra. `sphericalFixedLine` gives a one-dimensional fixed space in each
factor. The tensor of nonzero vectors in these lines determines a nonzero
induced section by `exists_localBlockReference`. The evaluation at the
identity is the tensor of the original vectors, which is nonzero by testing
against the tensor of dual functionals taking value one on each vector.
`exists_smul_localBlockReference_eq` proves that this section spans the
integral-fixed space of the induction.

`FiniteAdelicGL.isAdmissible_tensorRepresentation` applies the Library's
`restrictedTensorAdmissibility` to these local conditions. The topological
group equivalence `restrictedProductEquiv` carries admissibility to the
actual finite adelic matrix group. The reference comparison is identity on
all local maps and uses equality of the prescribed and normalized references
outside the exceptional set. It transfers admissibility to the specified
carrier used in the proof.

This is an internal specialization of D. Flath's *Decomposition of
representations into tensor products* (1979), §2, Example 2, printed p. 181
(Corvallis Part I PDF p. 177). Getz and Hahn, *An Introduction to Automorphic
Representations* (2024), Theorem 10.6.3, printed p. 285 (PDF p. 297),
identifies the isobaric sum of unramified characters of the diagonal torus
with the unique unramified subquotient of their Borel induction. Here
`sphericalFixedLine`, `exists_localBlockReference` and
`exists_smul_localBlockReference_eq` give the integral fixed line of the
entire normalized induction for the given spherical block factors.
Admissibility supplies the finite level bound for the compact-projected
Eisenstein argument in Langlands,
*On the notion of an automorphic representation* (1979), Lemma 7, printed
pp. 205–206 (Corvallis Part I PDF pp. 200–201), and its use of the
finite-dimensional space on printed p. 207 (PDF p. 202).
