# The actual central projection norm on an arbitrary Haar quotient

This derived module connects the Library's central-projection square-integrability
estimate to the arbitrary quotient Haar measure used in Waldspurger VIII.4.2.
It changes neither the central Haar measure in the defining projection nor the
specified quotient Haar measure.

`centralProjectionQuotientNorm` is the literal norm of the central projection
as a function on the quotient by the displayed central subgroup. The unitary
character and central covariance make it independent of the representative.
Its value on the coset of g is exactly the norm of the original central integral
at g.

Under the published `CentralWeights` and `L2Weights` estimates, choose a
compatible quotient measure for the supplied regular two-sided ambient and
central Haar measures. The published central-projection estimate gives an
L² norm function on that left-coset space. The published compatible-measure
comparison transports it to the specified quotient group and its arbitrary
Haar measure. That comparison explicitly uses the nonzero finite Haar scalar;
no probability normalization is made. Quotient surjectivity identifies the
transported function with the literal quotient norm.

`exists_memLp_two_of_mem_schwartzCentralIntegralImage` applies this result to
an actual raw-image witness. It supplies the norm-L² input needed by the actual
projected-function positive form. This auxiliary module retains the central and
ambient weight estimates as premises; it proves no closed rational weight
estimate or closed target of Waldspurger VIII.4.2 (the cuspidal coefficient
equality and same-level coefficient lifting).
