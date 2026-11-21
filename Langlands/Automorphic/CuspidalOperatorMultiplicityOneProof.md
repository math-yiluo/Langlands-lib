# Multiplicity one for actual cuspidal operator realizations

`Langlands.Automorphic.cuspidalOperatorMultiplicityOne` proves
`Langlands.Automorphic.CuspidalOperatorMultiplicityOneStatement.{u}` with
free number-field universe `u` and every `r : ℕ`. For a number field
with compact additive adele quotient, an equivalence commuting with
the finite adelic, standard compact and real Lie algebra operators
implies that the two actual cuspidal realizations are the same subspace
of automorphic functions.

The band reduction uses a common Hecke determinant twist to
make the central character unitary. The compact Sobolev estimate gives
the Whittaker band bounds on the twisted realizations. Square
integrability on the determinant band gives the inner products for
their adelic Hilbert completions. The original vectors embed as genuine
archimedean smooth vectors that are smooth under the finite adelic action.
The original equivalence extends to a bounded intertwiner of the full
adelic actions.

The Whittaker band bounds yield mixed smooth Whittaker functionals
for the same standard additive character. Their evaluations on
translated original vectors are the original Whittaker integrals.
Pulling the second functional back along the full adelic intertwiner
puts both on the first completion. Finite adelic Whittaker uniqueness
and continuous unitary Whittaker uniqueness for the real and complex
groups compare the restrictions on the place tensor slices.
Derivative density of the original fixed vectors at each compact open
finite level extends the resulting scalar comparison to the mixed
smooth space.

The same scalar therefore compares the original Whittaker functions
at every adelic group point. Fourier reconstruction gives equality of
the twisted realizations. Injectivity of the common determinant twist
gives equality of the original realizations. In Lean,
`cuspidalBandMixedWhittakerUniquenessFromLocal` applies
`Langlands.Archimedean.unitaryWhittakerMultiplicityOne` to obtain mixed
uniqueness, and `cuspidalOperatorMultiplicityOne_of_bandMixed` uses it
in the band comparison and reconstruction.

This is the local-to-global Whittaker and Fourier reconstruction
argument in J. W. Cogdell, *Analytic theory of L-functions for GL_n*
(2004), §1.2, printed pp. 201–202, and J. A. Shalika, *The multiplicity
one theorem for GL_n* (1974), Theorem 5.5, printed pp. 187–189. See also
J. R. Getz and H. Hahn, *An introduction to automorphic representations*
(2024), Theorem 11.4.3, printed p. 303. The determinant-band norm and
the three original operator actions are the formulation used by
the Library's actual automorphic realizations.
