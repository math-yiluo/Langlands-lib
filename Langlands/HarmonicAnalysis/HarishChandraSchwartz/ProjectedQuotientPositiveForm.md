# The actual quotient-L² form on projected left-level functions

This derived unit supplies the invariant positive form in the reverse
inclusion proof of Waldspurger (2003), Theorem VIII.4.2, printed pp.330–331
(PDF pp.96–97). It uses the Library's actual quotient-integrand machinery
and smooth evaluation on the actual projected left-level representation.

First, for any smooth representation with a specified unitary action of a
normal subgroup A, fix one smooth functional whose translated coefficients
separate vectors. If every coefficient against that functional has a
square-integrable norm on the displayed Borel quotient, then its products
are absolutely integrable by the L² product inequality. Integrating these
products defines a Hermitian form. For a nonzero vector, a detecting
translate makes its continuous nonnegative square-norm function positive
at a quotient point. Positivity of Haar measure on nonempty open sets
makes the integral strictly positive. The form is invariant when the
specified quotient Haar measure is invariant under inversion. No
irreducibility or admissibility is used in this construction.

`projectedQuotientPositiveForm` specializes this construction to the actual
projected left-level function representation. Smooth evaluation at one
has each function as its coefficient and therefore separates vectors.
The remaining L² input is precisely square integrability of the actual
projected functions' norms, not of all smooth-dual coefficients.
`projectedQuotientPositiveForm_inner` identifies the constructed form with
the literal quotient integral of `conj(f(q.out)) * g(q.out)`.

All measures remain as specified; no normalization or scalar adjustment
occurs. The absolute convergence input for projected norms and
inversion-invariance of the quotient measure remain explicit here.
Square integrability of this form's coefficients, the actual norm
estimates, and both closed Task 7440 targets are still separate obligations.
