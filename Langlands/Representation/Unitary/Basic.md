# Invariant positive Hermitian forms

For a monoid `G` acting linearly on a complex vector space `V`,
`Langlands.InvariantPositiveForm ρ` is a positive definite Hermitian form
preserved by every operator of the given representation `ρ`.
`Langlands.IsUnitarizable ρ` says that such a form exists.

The form extends Mathlib's `InnerProductSpace.Core ℂ V`. It is conjugate linear
in the first argument, linear in the second, Hermitian symmetric, nonnegative
on the diagonal, and definite. These are algebraic data and properties.
The carrier is not assumed to have a norm, topology, Hilbert completion, or finite
dimension. Smoothness and admissibility are separate predicates; this definition
can be applied directly to the underlying action of a bundled smooth
representation.

`InvariantPositiveForm.comap` constructs a form along an injective intertwiner.
Its value is `b.inner (f v) (f w)`. Linearity and invariance follow from the
intertwiner laws; definiteness follows from injectivity. `ofEquiv` specializes
this construction to an equivariant linear equivalence. The accompanying lemmas
establish the value formula, preservation along an injective intertwiner, and
invariance of unitarizability under equivalence. These are intrinsic transport
properties, not assertions that arbitrary quotients or representations are
unitarizable.

## Sources and scope

This is a derived algebraic implementation of the complex unitarizability
condition. Casselman's 1995 notes, section 2.1, printed page 18, describe
unitarity by an invariant anisotropic Hermitian form, with complex conjugation
for complex coefficients. Section 2.5, especially the proof of Proposition 2.5.4
on printed page 29, uses a positive definite invariant form to establish
unitarity. Here positivity is explicit in the definition. The file does not
formalize an equivalence between the positive formulation and the notes'
anisotropic formulation over general fields, nor the analytic theorem of
Proposition 2.5.4.

- Literature ID: `casselman-1995-admissible-representations`.
- W. Casselman, *Introduction to the theory of admissible representations of
  p-adic reductive groups*, draft, 1 May 1995, section 2.1, page 18, and
  section 2.5, Proposition 2.5.4 proof, page 29.
- Retained original:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
- SHA-256: `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.

The definition deliberately makes sense for arbitrary monoid actions. Its use
for smooth representations of locally profinite groups is a specialization.
It imposes no analytic conclusions at the generalized scope.

## Formal dependencies

Only pinned Mathlib is imported: `Mathlib.Analysis.Complex.Basic` supplies
the complex `RCLike` structure; `Mathlib.Analysis.InnerProductSpace.Defs`
supplies `InnerProductSpace.Core`; `Mathlib.RepresentationTheory.Intertwining`
supplies actual intertwiners and equivalences.

Environment artifact `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1:
Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`;
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Author: Worker 23.
