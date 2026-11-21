# Continuous unitary archimedean Whittaker multiplicity one

`unitaryWhittakerMultiplicityOne` proves the Library proposition
`UnitaryWhittakerMultiplicityOneStatement.{u}`. The same argument applies to
`GL_(n+1)(ℝ)` and `GL_(n+1)(ℂ)` for every `n : ℕ`, with a free universe
`u` for the complex Hilbert space. For `n = 0` the upper unipotent
group is trivial and the longest Bruhat cell is the entire group.
The proposition retains its full compact-subgroup admissibility
hypothesis. Joint continuity, unitarity and nonzero topological
irreducibility suffice for the Casimir scalar and the regularization
comparison.

Choose left Haar measure on the Borel matrix group. Unimodularity
gives right invariance. Inversion and the Weyl-conjugated transpose
preserve the measure, so their composition also preserves it.
Restriction from the ambient matrices to the open set of units
identifies matrix test functions with compact smooth kernels on the
group, with inverse extension by zero.

Each coefficient pairs one continuous smooth-vector functional with
the Riesz regularization of the other by a compact smooth kernel. The
finite word-seminorm bounds give a finite expansion of the
regularization by Gårding averages and prove continuity of the
coefficient on the actual test-function space. Equivariance and
symmetry of the quadratic real trace Casimir give scalarity on all
smooth vectors by the unitary graph argument. Differentiating the
adjoint kernel under the Gårding integral transfers the conjugate of
this scalar to the coefficient distribution. Its positive pullback
by \(x \mapsto u x v\) transforms on each side by the standard
character of \(t \mapsto \psi(-t)\). The conjugation on the right
uses that the character is unitary.

For these distributions, weighted orbit averaging on the longest
Bruhat cell proves invariance under Weyl-conjugated transpose on tests
supported in that cell. Subtracting the transpose distribution keeps
the same quadratic eigencondition and left covariance. The other
Bruhat cells have a missing simple-root direction in which covariance
forces vanishing together with the trace-Casimir equation on
transverse jets. Descending through the Bruhat filtration proves
transpose invariance on every test. Restriction transports it to all
compact smooth kernels on the group.

Apply the transpose invariance to the self-coefficient of \(\ell_0\)
and the mixed coefficient involving \(\ell_1\) and \(\ell_0\).
Conjugate transpose of adjoint convolutions reverses their two factors.
The adjoint convolution identity is the Hilbert form of the unnumbered
formula after Shalika's Proposition 3.2 on printed p. 184, with the
first test kernel conjugated to express the source's bilinear dual
pairing. The resulting transpose symmetry of Hilbert pairings
corresponds to equation (3.3). The irreducible Hilbert graph argument gives
proportionality of the two regularizations. Gårding approximation
approximates a smooth vector in every prescribed finite family of
genuine Lie-word seminorms. Thus the nonzero \(\ell_0\) has nonzero
regularization, and proportionality of regularizations determines
the original functionals on all smooth vectors.

The route formalizes the coefficient and distribution argument of
J. A. Shalika, *The multiplicity one theorem for GLn* (1974), Theorems
2.1 and 3.1, printed pp. 179–185, with an explicit real trace Casimir,
matrix Bruhat charts and Hilbert graph arguments. The real derivatives
are the existing Library Lie derivatives, with real and imaginary
matrix directions in the complex case. The inverse-character
convention agrees with the dual action in the original theorem.
The retained source is `shalika-1974-multiplicity-one`, SHA-256
`788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
