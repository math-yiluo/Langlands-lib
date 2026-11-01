# Rectangular unipotent Fourier identity in JPSS Section 6.2

This module defines
`Langlands.HarmonicAnalysis.AdjacentRankUnipotentFourierStatement.{uF}`.
It is an unproved, source-derived closed proposition. Worker 486 authored
the initial Lean and Markdown draft; Worker 1198 checked the original
source and published APIs and prepared this statement for submission.

The proposition quantifies over every prime `p`, every
`F : PadicField.{uF} p` with its canonical topological and local-field
data and Borel measurable structure, every supplied nontrivial continuous
unitary additive character `psi`, every supplied scalar additive Haar
`nu` and certificate `IsSelfDual psi nu`, and every natural `r`.
Set `n = r+1` and `t = r+2`.
Every rectangular Schwartz-Bruhat function `Phi` on `n` by `t` matrices
is included, without any factorization assumption. Write `T` for the
published inverse-character last-column partial Fourier equivalence and
`H` for the published full plus-character rectangular Fourier equivalence.
Let `w_n` and `w_t` be the actual antidiagonal Weyl matrices,
`epsilon = (0,...,0,1)` the length-n column, and
`zeta = diag(-1,...,-1,1)` the actual size-t sign matrix.
For `v` in the actual upper-unipotent subgroup of GL_n, the two functions are

```text
L(v) = T(rectangularTranslate(w_t*zeta) Phi)([v,epsilon]) theta(v)^(-1)
R(v) = H(T(Phi))([w_n*v,w_n*epsilon]) theta(v).
```

Here `theta` is precisely `Whittaker.standardCharacter psi r`,
its inverse is `Whittaker.inverseStandardCharacter psi r`, and
`[x,y]` is `rectangularJoin x y`. Thus
`theta(v) = psi(sum_i v_(i,i+1))`. The products `w_n*v` and
`w_n*epsilon` use the underlying actual matrices and matrix-vector
multiplication. The assertion includes `MeasureTheory.Integrable`
for both functions and equality of their complex Bochner integrals
for the same shared `RankinSelberg.unipotentHaar F.Carrier r`.
That Haar is normalized on integral unipotent points. It is not
identified with the coordinate product of `nu`; no such identification
is asserted. All additive Fourier factors use the published products
of the supplied scalar `nu`. No normalization is chosen afresh.

The source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg
Convolutions* (1983), registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The exact identity is Section 6.2, Lemma (2), printed 431; its proof
reduces to Fourier-inversion identity (3) on printed 431-432.
Section 6.1, printed 427, defines the ordinary right action and the
inverse-character last-column transform; printed 428, formula (6),
defines the full plus-character transform and also specifies `epsilon`.
These are one-based PDF pages 62-63 and 66-67. Both authors visually
read these original pages. The source works over a non-archimedean
local field; this proposition uses the Library's canonical p-adic
field interface and therefore covers finite extensions of `Q_p`.
No source-specific errata file was found under the project notes,
current Library notes or literature in the checks for this submission.

The equality reproduces formula (2) using the existing actual
constructors. Both integrability conjuncts explicitly strengthen the
displayed source identity. The transformed functions are Schwartz-Bruhat;
the maps `v -> [v,epsilon]` and
`v -> [w_n*v,w_n*epsilon]` are closed affine embeddings of the
unipotent matrix group. Restricting a compactly supported continuous
function along either embedding preserves these properties. Multiplication
by the continuous unitary character also preserves them, so integration
against the actual locally finite group Haar is the intended convergence
justification. This explains the derived scope; the module supplies no
Lean proof of either integrability assertion or of the identity.

The ordinary action is `(g Phi)(m) = Phi(m*g)`.
The left function is the partial transform of that ordinary action by
`w_t*zeta`. Replacing it by `rectangularRho0(w_t*zeta) Phi` would change
the input unless `Phi` had already been partially transformed.
The right function is full Fourier applied to partial Fourier, exactly
as displayed; no commutation lemma is used in this definition.
For `r=0`, GL_n is GL_1, its unipotent subgroup and character are
trivial, and the proposition still asserts the same identity.

This scalar proposition has no representation, model coefficient,
Whittaker-type, quasicharacter, growth or large-twist premise.
It asserts neither the neighboring model-star proposition nor any
adjacent-rank gamma or L factor conclusion. In particular it does not
resolve the printed neighboring proposition's distinction between
the action character and coefficient character.
The related published square affine identity
`Langlands.HarmonicAnalysis.unipotentHaar_transpose_fourier_duality`
may be useful to a later proof, but this module does not claim a proved
adapter from that identity to this rectangular assertion.
