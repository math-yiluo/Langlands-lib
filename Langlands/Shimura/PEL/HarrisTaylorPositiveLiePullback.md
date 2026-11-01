# Actual positive Lie pullback for Harris–Taylor

This file constructs actual base change isomorphisms for both Lie factors
and proves preservation of the positive rank and central scalar condition.
It is derived infrastructure for Harris–Taylor (2001), III.1, printed
pp.89–90 / PDF pp.97–98, in the registered source
`harris-taylor-2001-geometry-cohomology-simple-shimura` (SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`).
The source defines Lie± using the Lie-first tensor over the imaginary
quadratic coefficient algebra; compatibility means positive rank n and
agreement of the two actions of the totally real central field. The
present pullback comparison is a derived construction, rather than a
separately numbered assertion of the source.

Here K is a number field, L is an imaginary quadratic number field with
an algebra map to K, and S and T are arbitrary schemes over K. The map
b : T → S is arbitrary. A is a rational algebra with a K-algebra
structure; i : A →ₐ[ℚ] End⁰(B) is an actual action on an abelian scheme B/S.
The field E has an algebra map to K and selects the central scalars used
by the positive condition. Neither injectivity of i nor total reality of
E is required for the pullback argument. Those additional conditions
remain part of the intended moduli application. No reducedness,
Noetherian, flatness, or geometric-point hypothesis is imposed here.

`structureSectionPullbackAlgHom` is the actual ring map on global
sections, with K-algebra structures induced by the given scheme
structure morphisms. Its compatibility with K follows from composition
of the structural section maps. The helper
`structureSection_pullback_top` states this compatibility elementwise.

`imaginaryLieAction_pullback` specializes the proved canonical Lie base
change naturality theorem to each imaginary-field element. No naturality
hypothesis is left to the caller. `lieEigensheafPullbackIso` applies the
generic imaginary quadratic eigensheaf pullback construction to the
actual canonical `lieBaseChangeIso`. It identifies the pullback of the
full natural or conjugate simultaneous eigensubsheaf with the actual
target eigensubsheaf. Its forward map is the pulled-back inclusion,
followed by the canonical Lie comparison and the target eigenprojection;
`lieEigensheafPullbackIso_hom` records this formula. Its inverse and
inverse equations come from the generic split-projector construction.
`lieEigensheafPullbackIso_intertwines` proves compatibility with every
actual A-action endomorphism, using full rational Lie naturality.

`lieTensorPullbackIso` is the actual comparison for the original-order
Lie tensor factors. It is the pullback of the source tensor/eigensheaf
comparison, followed by the eigensheaf pullback comparison, followed by
the inverse target tensor/eigensheaf comparison.
`lieTensorPullbackIso_intertwines` proves compatibility with every
A-action by transporting the eigensheaf intertwining identity through
these actual isomorphisms.

`positiveLieScalarCondition_pullback` proves equality of the two central
E-actions on the target positive tensor sheaf. The proof pulls back the
source scalar endomorphism, uses semilinearity for global scalars and
structural section compatibility, and cancels the actual comparison
isomorphism. `lieCompatibility_pullback` also preserves the specified
rank n: the proved finite local basis pullback theorem preserves the
actual bases and their indexing types, and the tensor comparison
transports them to the target tensor sheaf.
`eigenLieCompatibility_pullback` gives the equivalent assertion for the
full positive eigensubsheaf using the proved tensor/eigensheaf equivalence.

This file proves pullback preservation of the actual positive Lie
condition directly. The trace-character equivalence of III.1.2,
representability of the moduli functor, and construction of its schemes
and level morphisms are separate obligations.
