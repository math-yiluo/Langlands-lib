# Pair Euler factors of weak induction with isobaric base change

`WeakInductionPairEulerValuesStatement` compares the pair factor of the
supplied weak induction and a second cuspidal realization with the pair
factors of the inducing cusp and each member of an upper isobaric weak
base change of the second realization. The upper factors are evaluated at
their own residue cardinalities and grouped by the finite places over the
chosen downstairs place. The identity holds for the supplied presentations
outside a finite set and retains the multiplicities in the upper
enumeration. This is the projection-formula version of the cofinite
Rankin–Selberg comparison in Henniart–Herb (1995), Lemma 8.13 and §8.16.

`weakInductionPairEulerValues` transports the weak comparison witnesses
to the supplied presentations using uniqueness of attached spectra.
It uses the finite sum of the actual upper spectra for the isobaric
datum. The pair polynomial splits over the constituent spectra since
pairing with each eigenvalue rescales the argument of the second Euler
polynomial. Applying the polynomial projection formula followed by
evaluation sends the substitution \(X \mapsto X^{f(w/v)}\) to the
spectral point at \(w\), since \(q_w=q_v^{f(w/v)}\). Inverting the
evaluated polynomials gives the factor identity.
