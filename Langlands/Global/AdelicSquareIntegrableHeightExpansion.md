# Orthogonality of finite square-integrable expansions on height slices

The predicate `HasSquareIntegrableHeightExpansion` on a function `ψ` on `G(𝔸)` asks for a finite
sum `ψ(g) = ∑ᵢ cᵢ(H_P(g)) vᵢ(g)` with each `vᵢ` in the Library's `A²_P`, for the same Iwasawa
compact `K` that defines `H_P`. The coefficient functions `cᵢ` may be arbitrary functions on the
real logarithmic parameter space. This includes the expansions by exponential polynomials in the
proof of Delorme's Lemma 3.10. The application only uses their values at one height at a time.
`isIwasawaCompact_of_bot` uses parabolic inclusion to carry Iwasawa coverage by the minimal
parabolic to coverage by any standard parabolic for the same `K`.

## Pointwise vanishing

`eq_zero_of_squareIntegrableHeightExpansion_of_orthogonal` proves `ψ = 0` when the orthogonality
predicate of Delorme's (3.7) holds. Fix a positive split-component point `x`. On the slice
`x M(𝔸)^1 K`, the height is `H_P(x)` because the Levi and compact factors contribute zero.
The form `φ = ∑ᵢ cᵢ(H_P(x)) vᵢ` is in `A²_P` by the square-integrable induced submodule theorem,
and equals `ψ` on the slice. The pairing integrand is consequently the squared norm of the
restriction of `φ` to the slice.

The `A²_P` equivariance under the positive split centre makes the slice restriction a constant
multiple of the restriction at `x = 1`. Its left `M(F)` invariance therefore descends to the
norm-one rational quotient. The product of compact Haar probability and norm-one quotient Haar
measure charges every nonempty open set. The restriction is continuous, so a zero integral of
its nonnegative squared norm forces its value to vanish at every point. This proves vanishing on
each height slice. Iwasawa coverage and the actual radical-Levi and split-centre–norm-one
decompositions cover `G(𝔸)` by left radical translates of those slices. Both the height and the
terms `vᵢ` are invariant under these left translations, giving pointwise vanishing on `G(𝔸)`.

The proof uses the supplied Iwasawa coverage for `K` and its compactness.

Source. P. Delorme, *On the spectral theorem of Langlands*, published PDF in the registered
`delorme-2023-spectral-theorem-langlands` collection, SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`. See (3.7) on p.15 and the
end of the proof of Lemma 3.10 (ii) on p.16.
