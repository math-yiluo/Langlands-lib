# Completed restriction, scalar twist and inverse-transported forms

This internal construction unit uses the actual uniform Hilbert completion in
`Langlands.Representation.Unitary.Completion`, the unchanged positive core of
`InvariantPositiveForm.comp` and `InvariantPositiveForm.twist`, and the published
form-preserving completion transport. The groups `G`, `H` and algebraic complex
carriers `V`, `W` have independent universes. No group topology is required.

For a supplied positive invariant form `b`, restriction along a group
homomorphism `φ : H →* G` retains exactly the same normed carrier, completion,
norm, inner product and canonical embedding. `comp_toHilbert` records the
definitional equality of embeddings. `comp_completedOperator` proves

`(b.comp φ).completedOperator h x = b.completedOperator (φ h) x`.

The proof compares two continuous operators on the unchanged completion. Their
equality set is closed and contains the dense canonical image by the existing
operator extension formulas. `comp_completedRepresentation` proves the
corresponding equality of representations by extensionality.

For a supplied unit-valued character `χ` with `∀ g, ‖(χ g : ℂ)‖ = 1`, twisting
retains that exact positive core and embedding. `twist_toHilbert` records the
embedding equality. `twist_completedOperator` proves

`(b.twist χ hχ).completedOperator g x = (χ g : ℂ) • b.completedOperator g x`.

Equality again extends from the dense canonical image by closedness; on that
image it follows from the extension formula and complex linearity of the
embedding. `twist_completedRepresentation` gives equality with the existing
`Langlands.twist` of the completed representation. The character appears with
its displayed positive exponent.

For an algebraic representation equivalence `e : ρ.Equiv σ`, set
`c = b.ofEquiv e.symm`. Its inner product is exactly
`c.inner w w' = b.inner (e.symm w) (e.symm w')`.
`ofEquiv_inner_apply` proves preservation of the chosen form using the two
inverse identities of `e`. `completedOfEquiv` applies the existing
`completedEquiv` to this form, the original intertwiner, that preservation proof
and surjectivity of the original equivalence. It constructs a complex-linear
isometric equivalence

`E : b.HilbertCompletion ≃ₗᵢ[ℂ] c.HilbertCompletion`.

`completedOfEquiv_toHilbert` gives `E (b.toHilbert v) = c.toHilbert (e v)`.
`completedOfEquiv_symm_toHilbert` gives the inverse formula
`E.symm (c.toHilbert w) = b.toHilbert (e.symm w)` by injectivity of `E` and
the original inverse identity. `completedOfEquiv_completedOperator` inherits
intertwining of the completed group operators from the published isometric
extension. Surjectivity, norm preservation and inner-product preservation are
part of the returned linear isometric equivalence.

`completedOfEquiv_covariant` handles additional algebraic operators `a`, `d`
and supplied continuous linear extensions `A`, `D` with their prescribed values
on the canonical images. If `e (a v) = d (e v)`, it proves
`E (A x) = D (E x)` by the existing dense-image covariance theorem.
`completedOfEquiv_scalar_covariant` instead assumes
`d (e v) = z • e (a v)` for a supplied complex scalar `z`. It applies that
theorem to `z • a` and `z • A`, using linearity of both embeddings and `e`,
and then linearity of `E` to obtain `D (E x) = z • E (A x)`.
No norm condition on this additional scalar is needed.

Two intrinsic specializations retain the original source completion.
`comp_completedOfEquiv_completedOperator`, for `e : (ρ.comp φ).Equiv σ`,
combines the restriction identity with completed intertwining to give

`E (b.completedOperator (φ h) x) = c.completedOperator h (E x)`.

Here `E = (b.comp φ).completedOfEquiv e` and
`c = (b.comp φ).ofEquiv e.symm`.
`twist_completedOfEquiv_completedOperator`, for
`e : (Langlands.twist χ ρ).Equiv σ`, combines the twist identity with completed
intertwining and linearity of `E` to give

`c.completedOperator g (E x) = (χ g : ℂ) • E (b.completedOperator g x)`.

Here `E = (b.twist χ hχ).completedOfEquiv e` and
`c = (b.twist χ hχ).ofEquiv e.symm`.

All constructions are derived from existing positive forms, original
representation equivalences and actual completion operations. There is no new
literature identification. Existence of a positive form, joint group-action
continuity and extension of unbounded infinitesimal operators remain separate
obligations.
