# Separated Fourier tests and the model-star restriction

This derived prerequisite proves the actual scalar test calculation used in
JPSS Section 6.3, printed pp.436–437, after the published fixed-character
model-star identity of Section 6.2. It contains no factor or multiplicativity
certificate.

`adjacentRankFourierSplit` is the measurable square-block/last-column split.
`adjacentRankFourierSplit_measurePreserving` proves that it carries the nested
rectangular product measure to the product of the square measure and the row
measure, all constructed from the same supplied scalar Haar measure. The proof
splits each row at its last entry and regroups the product coordinates.

The rectangular pairing splits as the sum of the square pairing and the row
pairing. `adjacentRankSeparatedTest_fourier` then factors the full plus Fourier
integral of a separated test into the square transform and the supplied actual
row Fourier transform, by the exact measure-preserving split and the product
integral formula. Scalar self-duality supplies sigma finiteness. No comparison
scalar or replacement Haar measure is used.

`adjacentRankSeparatedTest_fourier_eq` promotes the evaluation identity to an
equality of whole Schwartz tests. The supplied row pair is in the plus-sign
Fourier convention, as is the full rectangular transform. The square transform
uses the pairing `Tr(A * transpose X)` and the actual square product measure.
The statements apply to arbitrary ranks, including an empty square block in
the measure-splitting lemma. In the separated-test theorems, the square block
has size `r+1` and is therefore positive.

`adjacentRankZeta_eq_rankInclusion` identifies the actual model-star sign
matrix `zeta = diag(-I_(r+1), 1)` with the standard rank inclusion of the negative
scalar matrix. The proof checks the four blocks of its entries.

For `n = r+1`, let `c = -I_n`, let `g,h` belong to `GL_n`, and write `iota` for
inverse transpose. With the same supplied character `psi` and self-dual scalar
Haar `mu`, put

```text
PhiHat = full plus square Fourier transform of Phi,
k = zeta * diag(g,1),
J_g(h) = PhiHat(h*c*g) * phiHat(lastRow(h^-1))
         * W(w_n*iota(h^-1)) * chi^-1(det h) * |det h|^(r/2).
```

`Padic.adjacentRankModelStar_separated_rankInclusion` proves convergence of
the original model integral at `w_(n+1)*iota(diag(g,1))`, integrability of
`J_g` for the unchanged `generalLinearHaar`, and the equality

```text
M_(chi,Phi⊗phi⊗W)(w_(n+1)*iota(diag(g,1)))
  = chi^-1(det k) * |det k|^(n/2) * integral J_g(h) dh.
```

Here the tensor's rectangular factor is the published separated test. `W`
belongs to the actual coefficient image of the specified standard Whittaker
functional of the original representation `sigma`. The representation has
full Whittaker type, possibly reducible; the functional itself may be zero.
The original carrier has no topology and retains its independent universe.
The canonical p-adic field structures, normalized absolute value, every
natural `r` including zero, and the supplied character and measures are retained.

The proof applies the published closed model-star theorem. It replaces the
full Fourier test by the established separated square/row transform,
identifies `k` with `diag(c*g,1)`, and uses the published covariance of the
partial-Fourier transported action at that rank inclusion. This gives exactly
the displayed integrand. Transporting both integrability and integral equality
along that function identity proves the result. The Fourier action remains
`rho0_psi` throughout; the transformed coefficient is evaluated literally at
`w_n*iota(h^-1)`. No unproved change of coefficient image or additive character
is used.

This is the diagonal scalar-integral step leading to the display on printed
p.437 of Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg Convolutions*
(1983), Section 6.3. The registered source is `jpss-1983-rankin-selberg`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The source's subsequent dual coefficient separation, finite zeta-product
formula (14), functional-equation comparison and gamma/L factor conclusions
are separate obligations. This module does not claim those conclusions, an
induced-model realization, or existence of matrix rational-value witnesses.
