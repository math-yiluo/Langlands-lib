# Triangular integration of a complex principal-series vector

`exists_complexPrincipalSeries_matrixIntegral_triangular` expands the integral of
`Φ(g) f(g) |det g|_ℂ^(s+r/2)` on `GL_(r+1)(ℂ)` when this kernel is integrable.
The multiplicative Haar measure on the matrix group comes from the additive
matrix measure. The smooth vector `f` belongs to the normalized upper principal
series of the characters `χ`. The diagonal, upper-entry and unitary measures are
specified as separate inputs. A single positive constant compares these Haar
normalizations and is independent of `Φ`, `f`, the characters and `s`.

The proof pulls the integral back by `(d,u,k) ↦ diag(d) u k` and applies Fubini.
In the unipotent integral, covariance replaces `f(diag(d) u k)` by
`principalSeriesCharacter χ d * f(k)`, and the determinant power depends
only on `d`. Rescaling each strict upper entry by its row diagonal entry
turns `diag(d) u` into a matrix with diagonal `d` and additive upper
entries. The corresponding Jacobian cancels the modular and determinant
shifts, leaving `∏ᵢ χᵢ(dᵢ) |dᵢ|_ℂ^s`. The inner test is the integral of
`Φ(T k)` over the additive strict upper entries of the triangular matrix `T`.

This calculation is the upper-Borel coordinate reduction for the matrix
zeta integrals used by Jacquet, *Archimedean Rankin–Selberg Integrals* (2009),
§4.7 and §8. It is an identity on the domain of absolute convergence.
