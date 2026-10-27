# Scalar Jacquet covariance under exchanged unipotent diagonal blocks

This is an internal prerequisite for the two-block JPSS construction. Its
provenance is the literal published `Shahidi.Geometry` block Weyl and rectangular
radical, the scalar kernel and integrand in `Shahidi.Characters` and
`Shahidi.JacquetIntegral`, and rectangular Haar scaling in
`Shahidi.IntertwiningCovariance`. It is a proposition definition, not a proof or
an assertion of the complete extension theorem.

Let the original positive block ranks be `m+1,n+1`. For actual upper-unipotent
matrices `u₁,u₂` of these ranks, put
`e(x) = u₂⁻¹ x u₁`. The right translating group element is
`swapRank (m+1) (n+1) (blockSum (u₂,u₁))`; `swapRank` preserves entries and only
changes the arithmetic expression for total rank. It does not permute the
matrix entries.

The closed statement quantifies over every p-adic field, every one of its
published topological realizations, and every Borel additive Haar measure on the
rectangular coordinate space. The scalar field measurable space is its Borel
space. It asserts that `e` preserves the supplied measure, with no measure
normalization chosen.

For an arbitrary coefficient module, algebraic linear functional `ℓ`, group
function `f`, and scalar `z`, assume the explicit scalar left-covariance law
`ℓ(f(diag(u₁,u₂) g)) = z ℓ(f(g))`. The conclusion identifies the actual Jacquet
integrand of the right translate with `z` times its original integrand composed
with `e`. If the original scalar integrand is integrable, the translated
integrand is integrable and its ordinary Bochner integral equals `z` times the
original integral. No topology on the coefficient module is required.

The expected kernel invariance uses the first column of `u₁` and the last row of
`u₂⁻¹`, while Haar preservation uses their determinant-one identities. The
left-covariance hypothesis is explicit: deriving its scalar `z` from the
inducing representations and their Whittaker functionals is a separate step.
This statement does not assert convergence for arbitrary `f`, full
upper-unipotent covariance, existence of cell sections, or the final JPSS
Whittaker coefficient formula. The field and coefficient universes are
independent.
