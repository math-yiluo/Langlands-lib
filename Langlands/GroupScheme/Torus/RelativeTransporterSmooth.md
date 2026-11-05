# Actual smooth fixed schemes and diagonalizable transporters

Let `G` be an affine group scheme over `Spec R`, with `R` any
commutative ring. Let a diagonalizable group `D_R(M)` act on the
underlying scheme of `G` by an actual `PointwiseSchemeAction`.
Preservation of the group law of `G` is not required.

`CharacterAction.schemeActionFixedScheme` is the actual spectrum of
the existing affine coordinate algebra modulo the existing full
`schemeActionFixedIdeal`. The morphism `schemeActionFixedHom` is the
spectrum of the quotient map followed by the actual coordinate-scheme
isomorphism into `G`. It is a closed immersion and a monomorphism.

The inclusion itself is fixed after every scheme refinement. This
uses the existing `schemeActionFixedIdeal_le_ker_iff` applied to the
quotient map. Fixedness is preserved by precomposing the test scheme,
as recorded by `PointwiseSchemeAction.IsFixed.comp`. Conversely,
every fixed point on an affine test `Spec C` factors through the
inclusion. Its coordinate algebra map kills the full fixed ideal,
so `Ideal.Quotient.liftₐ` gives the factor. Composition with the
quotient recovers the original point exactly. The theorem
`exists_schemeActionFixed_factor_iff` proves this equivalence for
every affine test, using all-refinement fixedness on its right side.
The file does not assert the converse factorization on arbitrary
nonaffine test schemes.

For smooth `G`, the quotient is smooth over `R`. Its formal
smoothness is the existing actual-scheme-action fixed-quotient
theorem. Its finite presentation is the finite-equation result
in `FixedQuotientFinitePresentation`, with no noetherian assumption.
The spectrum of that same quotient is therefore smooth over the base.

For two actual homomorphisms `i₁, i₂ : D_R(M) → G`,
`PointwiseSchemeAction.relativeTransporterScheme` specializes the
construction to the published left-right action
`t · g = i₁(t) g i₂(t)⁻¹`. Its closed inclusion satisfies the
existing all-refinement `IsTransporter i₁ i₂` relation. Every
affine-test point satisfying that relation factors through the
scheme, with its original point recovered by composition.
The transporter scheme is smooth when `G` is smooth; it may
have empty fibres. No immersion hypothesis is imposed on `i₁`
or `i₂`.

The provenance is internal: the construction combines the published
coordinate action for actual scheme actions, full fixed ideal,
left-right transporter action, and formal-smoothness result with
the finite-equation lemma and the elementary spectrum of an ideal
quotient. It provides a smooth scheme on which a specified
field-valued transporter can be used as input to a pointed smooth
local-section theorem. That local section, its compatibility with
base change and fibre identity components, and the resulting
reductivity-locus argument are separate obligations.
