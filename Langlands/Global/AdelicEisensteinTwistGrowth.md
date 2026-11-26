# Derivative bounds for the height-twisted inducing function

`parameterTwistSlice` equips the usual height twist of an inducing function with its smooth
archimedean slices. `exists_parameterTwist_derivative_bound` bounds every derivative of a twisted
slice by a constant times the fixed power of the normalized matrix height for the inducing
derivatives, multiplied by the absolute value of the height power at that point.

For a fixed parameter `λ`, write `h(g) = exp ⟨λ, H_P(g)⟩`. At `g = p(q) k`, the function of the
infinite right displacement `y` given by `h(g y)` equals the character power of `q` times
`h(k y)`. The finite component of `k` is in the compact and drops out by right invariance.
Enveloping derivatives commute with left pullback on the archimedean slices. Smoothness and
compactness therefore bound the derivatives of `h(k y)` at the identity uniformly in `k`.
The absolute value of the character power of `q` is `|h(g)|`.

The real Leibniz rule preserves the linear span of products of one derivative of the inducing
function and one derivative of the height power. Since real directions generate the complex
enveloping algebra, this span contains all derivatives of the product. Each product has the
same growth weight by the two separate estimates, and finite linear combinations preserve
that weight.

The estimate is derived for the twist in Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series* (2024), §2.2 and (2.1), p. 191. The journal PDF
`Bernstein-Lapid--On the meromorphic continuation of Eisenstein series--2024.pdf` is registered
under `bernstein-lapid-2024-meromorphic-continuation-eisenstein` with SHA-256
`6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.
