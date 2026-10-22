# Equivariant functionals and coefficient models

This module implements the algebraic construction underlying a Whittaker model.
It takes an actual subgroup `N` of a group `G`, a character
`theta : N ->* Rˣ`, and a representation `rho : Representation R G V`.
The coefficient ring is commutative. The coefficient ring, group and
representation module have three independent universes. No topology is imposed
on the module or its algebraic dual.

`equivariantFunctions N theta` is the actual submodule of all functions
`f : G -> R` satisfying

$$f(ng)=\theta(n)f(g).$$

It is bundled as a Mathlib subrepresentation of the right-translation action
`r(s)f(g) = f(gs)`. `functionRepresentation` restricts this action. These are
algebraic functions: no smoothness, support or integrability is asserted for the
whole space.

`functionals N theta rho` is the submodule of the full algebraic dual consisting
of functionals satisfying

$$\ell(\rho(n)v)=\theta(n)\ell(v).$$

`coefficientMap rho ell` reuses the accepted matrix-coefficient map to send
`v` to the function `g -> ell(rho(g)v)`, with the covariance and intertwining
fields proved. `evaluationFunctional` evaluates an intertwiner at the identity.
`functionalEquiv` packages these inverse maps as a linear equivalence.

`coefficientModel rho ell` is the range of this intertwiner, with its invariant
submodule structure supplied by Mathlib. `modelRepresentation` is its inherited
action. `modelMap` is the canonical surjective intertwiner to the image; its
surjectivity is proved from linear-map range restriction. If the source is
smooth, `model_isSmooth` proves smoothness of this actual image: an open subgroup
fixing a preimage fixes its image by equivariance. This proof needs only a
topology on the group, not continuity of its operations.

Over a field, `modelEquiv` constructs a representation equivalence from an
irreducible representation to the image of a specified nonzero functional.
It uses Mathlib's theorem that an intertwiner from an irreducible representation
is injective or zero. The zero case would make the functional zero by evaluating
coefficients at the identity. The already proved range surjectivity then gives
the equivalence. No finite-dimensionality is needed.

`HasFunctional` asserts the existence of a nonzero functional in the specified
space. It does not call an arbitrary representation irreducible or generic.
The later concrete `GL_n` construction must supply the upper-unipotent subgroup,
its nondegenerate additive-character construction, and the appropriate
representation hypotheses.

## Original source and explicit scope

Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions*,
American Journal of Mathematics 105 (1983), 367–464:

- Section 0.3, printed page 377: right-translation convention.
- Section 2.1, printed page 385, equation (1): the functional covariance.
- Section 2.1, printed page 386, equation (3) and its following paragraph:
  coefficient functions, their left covariance, right-translation invariance,
  and quotient realization.

Source receipt: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Original file:
`C:/Central-Library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
The cited original scanned pages were read directly.

The source works with complex admissible finite-type representations of actual
`GL_r(F)` and, for its Whittaker-type model, a one-dimensional functional space.
This module isolates the algebraic coefficient-image construction for a
**specified functional**, which requires none of admissibility, finite type,
one-dimensionality, irreducibility or local-field structure. This extension is
explicit and internal. In particular, it does not identify the images for
different nonzero functionals or assert uniqueness or existence of a functional.
Those are separate obligations. The irreducible image equivalence is constructed
only with explicit field, irreducibility and nonzero-functional hypotheses.
No local zeta integral or local factor is constructed in this first module.

## Intrinsic arguments and reuse audit

The covariance conditions are closed under addition and scalar multiplication
by distributivity and commutativity of coefficients. Associativity proves
stability under right translation. The representation law
`rho(ng)=rho(n)rho(g)` proves coefficient covariance; the same law proves
intertwining. Evaluation at the identity gives a functional by the target's
left covariance. Evaluating the intertwining identity at the identity proves
one inverse identity; `rho(1)=id` proves the other.

Mathlib's `Subrepresentation`, `Subrepresentation.toRepresentation`,
`Representation.IntertwiningMap`, `IntertwiningMap.range`, and
`LinearMap.rangeRestrict` are reused. The pinned
`TannakaDuality.FiniteGroup.rightRegular` has the same formula but restricts the
group and coefficient ring to the same universe. `rightTranslation` implements
that formula with independent universes and proves its two monoid-homomorphism
fields directly. Mathlib's finite-dimensional Tannaka context is not imported
into this construction.
`Representation.IsIrreducible.injective_or_eq_zero` supplies the injectivity
alternative for `modelEquiv`.

The project dependencies are the accepted matrix-coefficient definitions
`5352a743-a6a8-4824-b91e-1cbc32b79b30` version 1 and the accepted smoothness
definitions `665022df-625b-44ae-9dbd-425f6e266bab` version 1.
The matrix-coefficient publication is commit
`12dbb4572150a088d7f1df3eb9f5b771cb71604c`, effective snapshot
`aa9653082118d59a057d45b6a329caa3fdfd621252627ae6692fbc7c82d927a1`;
its accepted Lean is unchanged. Its final Markdown updates only stale submission
status wording. The local pair matches the effective source hashes.
The smoothness dependency has effective snapshot
`092f2dc612370a1612d3c08d1e60ff18add554e831ee02c7041342ac9dff16c0`.
Both dependencies were checked as accepted, published and currently available
at Library commit `d0f5322f745425b08ae8e72c1031206f45cb049e`.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1,
Lean 4.34.0, Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Authored by Worker 31. Compilation and declaration inspection are development
checks; independent semantic review and publication are separate requirements.
