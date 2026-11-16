# Integral root coefficients under reflection

This internal construction tracks integral linear combinations of a finite
family of actual roots of a root datum. It assumes neither that the selected
roots are independent nor that they form a base.

`combination P a c` is the sum of `c j` times the actual root `P.root (a j)`.
`IsRoot P a c` says that this sum equals an actual root. `reflect M i c`
subtracts from coordinate `i` the sum of `c k * M k i` and leaves the other
coordinates unchanged.

Each coordinate vector is an actual root. If `M` gives every actual Cartan
pairing of the selected roots, reflection of the coefficient vector is realized
by the actual root-datum reflection. The proof evaluates the given root
combination on the reflecting coroot and applies the integral reflection
formula. These are derived algebraic constructions using Mathlib's root-datum
interface, with no classification or external source claim.
