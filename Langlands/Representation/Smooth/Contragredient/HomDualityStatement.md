# Linear duality of intertwiner spaces

For a topological group whose compact open subgroups are cofinal among open
subgroups, a smooth complex representation `rho` and an admissible complex
representation `sigma`, smooth contragredient pullback is the forward map of a
complex-linear equivalence

`Hom_G(rho, sigma) ≃ Hom_G(sigma^vee, rho^vee)`.

The equality specifying the forward map is part of the proposition, so this
does not merely assert that the two spaces happen to be isomorphic.
The source need not be admissible or finite-dimensional. Admissibility of the
target includes its smoothness. The group and both module carriers have
independent universes. The topological-group instance, compact-open cofinality,
smoothness and admissibility hypotheses are all quantified inside the target.
There is no topology on the representation spaces.

The contragredient is the smooth part of the algebraic, complex-linear dual.
It uses the inverse-group-element action and ordinary linear pullback, not a
Hermitian or conjugate-linear dual. Compact-open cofinality is an explicit
premise; this statement does not establish it for a concrete group.

## Original source and scope

Casselman, *Introduction to representations of p-adic groups*, Chapter II,
June 16, 2019, Section 3, Proposition II.3.4 on page 7 gives this Hom-space
isomorphism for a smooth source and an admissible target, both free over the
coefficient ring. The definition of freeness used there is freeness of the
fixed-vector spaces. Over the complex numbers all these spaces are vector
spaces, so the freeness hypothesis is automatic.
Lemma II.3.2 on page 6 supplies the target's canonical bidual identification.
The original proof dualizes an intertwiner between contragredients, then
composes with the source's bidual map and the inverse of the target's bidual
map. The paired proof `HomDualityProof` follows this construction directly.

Registered source: `casselman-2019-smooth-representations`, SHA256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
The exact original pages 6 and 7 were read, and the file hash was verified.
The explicit compact-open premise replaces the source's locally profinite
ambient setting from page 1; no separate countability or Hausdorff assumption
is needed in the implemented proof.

## Dependencies and status

The statement imports only the smooth contragredient construction
`Langlands.Representation.Smooth.Contragredient.Definitions` and its construction
closure: algebraic dual maps (`Langlands.Representation.Dual.Definitions`),
smooth parts (`Langlands.Representation.Smooth.SmoothPart.Definitions`) and smooth
definitions (`Langlands.Representation.Smooth.Definitions`), in the pinned
environment.
Their eight source files were verified unchanged at
Library `9db46907db3181b0c1dfd287b8ab2f1f02054cab`.
Mathlib supplies complex numbers and linear equivalences.

The adjacent proof `HomDualityProof` uses the admissible-duality result
`SmoothAdmissibleDualityStatement` (`AdmissibleDualityStatement`, proved in
`AdmissibleDualityProof`). Neither is a dependency of this statement.
