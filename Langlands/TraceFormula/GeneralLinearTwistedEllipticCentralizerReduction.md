# Reduction of the twisted elliptic centralizer theorem

The two measure conclusions are packaged in
`TwistedCentralizerAnalyticConditions`. A compatible quotient measure is
regular, hence finite on compact sets. Compactness of the rational quotient
therefore gives its finite mass. Closedness of the twisted orbit gives
integrability by `twistedOrbitFunction_integrable_of_isClosed`. The argument
uses the left quotients, Haar measure, and Borel structures in the published
statement.

`generalLinearWeilTwistedAnalytic_of_compact_closed` applies these arguments
at a rational sigma-elliptic point. Its inputs are the compactness and
closedness propositions of `GeneralLinearWeilTwistedGeometry.lean`.

`exists_sigmaElliptic_rational_matrix_of_isRegularElliptic_localNorm`
uses the adelic coordinate comparison to identify the principal point with
a rational matrix `δ` and the ordered adelic norm with the principal image
of `cyclicNorm σ l δ`. The factorwise comparison uses the automorphism
homomorphism and the equivariance of the rational matrix embedding. The
local projection is coefficient extension to the finite completion. The
cyclic norm lemma supplies an associated matrix over `K`. Its characteristic
polynomial maps to the characteristic polynomial of the local norm.
Separability and irreducibility of that image give the same properties over
`K`.

The analytic argument concerns the per-class terms of Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), §18.5, pp. 487–488.
