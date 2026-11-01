# Actual natural and conjugate splitting of the relative Lie sheaf

This module specializes the constructed imaginary quadratic sheaf splitting to
an actual abelian scheme with a rational algebra action. Its central characters
are the natural and conjugate characters in Harris–Taylor, *The Geometry and
Cohomology of Some Simple Shimura Varieties* (2001), III.1, printed pp.89–90 /
PDF pp.97–98. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
This is a derived eigensheaf splitting prerequisite for the source's tensor
factor description, whose identification remains a separate obligation.

The source's imaginary quadratic field is `L`, its CM field is `K`, and its
central algebra is `A`. Lean calls the abelian scheme `B`. The inputs are an
imaginary quadratic CM number field `L`, a number field `K` containing it,
a rational algebra `A` with central `K`-algebra structure, an actual scheme
`s : S → Spec K`, an abelian scheme `B/S`, and an algebra homomorphism
`i : A →ₐ[ℚ] End0 B`. The construction uses neither faithfulness nor the
division-algebra condition, a prescribed dimension or signature, a totally
real subfield, or a noetherian, reduced or nonempty base. The original
Harris data specialize these parameters.

Every global scalar structure is constructed from the given map `s`: the
`K`-algebra structure is the one induced by `secHom s ⊤`, and the rational
structure is its composition with the rational embedding into `K`. The
required scalar tower follows from equality of these algebra maps. None of
these scalar structures is an extra arbitrary input.
`sheafFactorCharacter_eq_imaginaryLieCharacter` identifies the generic
natural and conjugate characters with the actual structure characters by
the two Boolean cases. This equality itself needs no quadratic-degree or
number-field hypothesis on `K`.

`lieEigenProjection` applies the constructed eigenprojection to the actual
differentiated imaginary-field action and identifies its target with the
existing full Lie eigensubsheaf. `lieEigenIso` specializes the actual
sheaf-category product isomorphism. Its forward map pairs the two projections,
and its inverse adds the two included sections, in natural then conjugate
order; the two displayed formula lemmas hold by definition. Both inverse
laws are supplied by the constructed generic splitting, without an assumed
Lie decomposition or output isomorphism.

`lieEigenProjection_intertwines` proves equivariance for the full actual
rational `A` action. Centrality already proves that action commutes with
the imaginary-field action, so generic eigenprojection naturality applies.
In each Boolean case its restricted morphism is exactly the existing
`lieEigensheafAction`. The two projection equations prove
`lieEigenIso_intertwines`, with the product of the two restricted action
endomorphisms on its target.

For an actual rational homomorphism `f : B → B'` intertwining the two
`A` actions, `lieEigenProjection_naturality` specializes generic naturality
using its proved imaginary-field Lie intertwining equation. The induced
morphism is the existing `lieEigensheafMap`, with its actual rational
Lie differential. The two component comparisons prove
`lieEigenIso_naturality`, so the splitting is natural for these rational
homomorphisms, including equivariant rational isomorphisms.

The source defines `Lie⁺` and `Lie⁻` by tensor factors over `O_S ⊗_ℚ L`.
This module constructs the product splitting into full eigencondition
subsheaves, without yet identifying them with those tensor factors. Local
freeness, prescribed ranks, the two totally real field action comparison,
compatibility and trace equivalences, and arbitrary scheme base change
remain separate obligations. No representability or coefficient descent
is asserted here.
