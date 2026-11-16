# Finite test systems from actual finite-cover Čech complexes

This internal adapter packages the actual free Čech chain complexes of all
finite basis covers as the previously defined `FiniteCechSystem`. It is
conditional on three explicit inputs: finite basis refinements of covering
sieves, the full `FreeCechCoverExactnessStatement`, and finite coproduct
presentations of every presheaf Čech nerve term by the same basis.

For an arbitrary chain complex in an abelian category, a chain map to an
object in degree zero annihilates the first boundary. If that chain map is
a quasi-isomorphism, its degree-zero condition is equivalent to exactness
at the augmentation source and epimorphy of the augmentation. In positive
degrees the target is exact, so the source is exact too.

`FiniteBasisCover.presheafArrow_isLocallySurjective` applies the covering
sieve characterization to the stored finite covering family.
`FiniteBasisCover.CechPresentation` stores a finite size, a basis-object
index for every summand, and an actual isomorphism from each presheaf
nerve term to that finite coproduct. No representability or finiteness
theorem is implicit in these data. Applying the free sheaf functor and
its coproduct preservation gives the corresponding finite presentation
of every actual free Čech chain term.

The adapter uses these presentations, the assumed full augmented
exactness, and the previously proved finite-cover Čech lifting theorem
for the local lifting field. Its covers are precisely all
`FiniteBasisCover J B (B i)` for each basis object `B i`.

The site category must be locally small in the coefficient universe `w`.
The commutative ring lies in `Type w`, module sheafification is assumed,
and `J.WEqualsLocallyBijective (ModuleCat.{w} R)` is retained for coefficient
lifting. The derivation uses only quasi-isomorphism invariance of homology,
the finite-cover local-surjectivity characterization, and preservation of
coproducts by the free sheaf functor.

This module does not construct an analytic basis, prove the full cover
exactness proposition, or supply finite presheaf nerve presentations.
It also does not prove coefficient Hom acyclicity or the analytic
comparison theorem.
