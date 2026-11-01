# Row Fourier changes for the adjacent-rank model-star identity

This internal helper is derived from the published scalar Haar scaling and
row and rectangular Fourier change-of-variables theorems. It uses a canonical
p-adic field, its canonical topology and Borel structure, the supplied unitary
additive character `ψ`, additive Haar measure `ν`, and certificate
`hself : IsSelfDual ψ ν`. No representation coefficient is changed.

Left row pullback sends `φ(m)` to `φ(h m)` and commutes with right translation.
The inverse-character last-column Fourier map sends this pullback to the
partial transform evaluated at `[h x, iota(h) y]`, multiplied by `|det h|^-1`.
The proof rewrites the last-column integral as an inverse-character row Fourier
integral and applies the published row change-of-variables theorem to the
transpose of `h`.

The full plus Fourier map sends the same pullback to the full transform at
`iota(h) m`, multiplied by `|det h|^-(n+1)`. The proof applies the actual
left-right Fourier substitution and the p-adic rectangular Haar scaling law.
Both scalars use the canonical normalized absolute value. These results include
all dimensions; subsequent orbit specializations use `n = r+1`.


For `n = r+1`, the inverse transpose of an upper unipotent matrix fixes the
last basis column `ε`. Consequently the kernel on a right orbit is
`K(h u) = [h u, iota(h) ε]`. The first exported orbit adapter rewrites
`rho0(a) Φ (K(h u))` as `|det h|` times the partial transform of
`R_a L_h T.symm(Φ)` evaluated at `[u, ε]`; it permits every ambient `a`.

The second adapter evaluates `H(T(L_h T.symm(Φ)))` at `[w u, w ε]` as
`|det h|^-(r+1)` times `H Φ (K((iota(h) w) u))`. Its proof commutes the
published chosen full and partial Fourier maps, applies the full row change
as an equality of Schwartz functions, then applies the partial row change at
`iota(h)`. The exponents add as `-(r+2)+1=-(r+1)`. The matrix argument follows
from the inverse-transpose group law and `iota(w)=w`.

These are derived Fourier and matrix adapters for the fixed-character model
identity. They assert no model-integral equality and require no representation,
nonzero functional, irreducibility or positive `r` premise. In particular the
orbit adapters include `r=0`. Their provenance is internal: they specialize
published change-of-variables, commutation, and actual kernel constructions.
