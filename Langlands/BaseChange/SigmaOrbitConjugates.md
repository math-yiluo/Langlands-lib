# The conjugate factors of a supercuspidal orbit product

These lemmas implement the exact-period condition in the orbit product of `CuspidalSigmaLiftExistenceStatement`. The condition is that a representation `P` of `GL_n(E)` is equivalent to its pullback by `σ^i` exactly when `s` divides `i`.

Substituting the positive cyclic degree `l` gives `s ∣ l`, hence `0 < s`, because `σ^l = 1`. For `i ≤ j`, pull back an equivalence of the two conjugates by `(σ^i)⁻¹` to obtain the period test at `j - i`. Pullback by `σ^i` reverses the argument. This shows pairwise inequivalence among indices in `Fin s`. Pullback by `σ` advances the exponent by one. At the last index, the period equivalence identifies exponent `s` with exponent zero, giving the rotation `finRotate`.

`isSupercuspidal_comp_entrywiseAut` applies the transport of Jacquet vanishing and admissibility through a homeomorphic field isomorphism. Continuity of both field maps follows from their linearity for the supplied module topology on `E`.
