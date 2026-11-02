# Localization of finitely presented modules of finite projective dimension

This internal prerequisite replaces Noetherianity in the published
`FiniteProjectiveDimensionLocalization` argument by an explicit condition on
finite submodules of finite free modules. It does not prove the arbitrary
valuation-ring two-axis extension statement.

`FiniteFreeSubmoduleCoherent R` is the proposition that, for every natural
number `d` and every finitely generated submodule `K` of `Fin d → R`, the
module `K` is finitely presented over `R`. This file uses precisely this
finite-free-submodule formulation of coherence; it does not introduce a
separate coherent-ring typeclass or prove equivalence with other definitions.
`finiteFreeSubmoduleCoherent_of_isNoetherianRing` proves the condition for
Noetherian commutative rings, using finite generation and Mathlib's
finite-presentation theorem over Noetherian rings.

For a commutative local ring `R`, assume `FiniteFreeSubmoduleCoherent R`.
Let `M` be a finitely presented `R`-module, let `n` bound its projective
dimension in Mathlib's module category, and let `S` be any multiplicative
submonoid of `R`. If the localization of `M` is projective over
`Localization S`, then it is stably free. The bundled version is
`moduleCat_localizedModule_isStablyFree_of_finitePresentation`.
The ring and original module belong to the same arbitrary universe `u`.

`isStablyFree_of_isLocalizedModule_of_finitePresentation` permits any model
`N` of the localization, supplied with an `R`-linear localization map from
`M`, a `Localization S`-module structure and the scalar-tower compatibility.
The model `N` may belong to a different universe `v`.
`localizedModule_isStablyFree_of_finitePresentation` specializes to the
canonical localized module. The final theorem,
`localizedModule_free_of_invertible_of_finitePresentation`, concludes
freeness when this canonical localization is invertible.

The implementation adapts the induction already implemented in the published
`FiniteProjectiveDimensionLocalization` module. At projective dimension zero,
the finitely generated projective module over a local ring is free, and so
is its localization. In the successor step choose a surjection
`(Fin d → R) → M`. Finite presentation of `M` makes its kernel finitely
generated. The explicit coherence condition then makes the kernel finitely
presented, which is the extra input required for the induction hypothesis.
Dimension shifting decreases the projective-dimension bound.

Localization preserves the short exact sequence. The projective localized
quotient splits it, identifying the finite free middle module with the
product of the localized kernel and the localized quotient. The kernel is
therefore projective, and the induction hypothesis makes it stably free.
The private product-permutation lemma then supplies a finite free complement
for the quotient. The arbitrary-model wrapper transports the conclusion
along the canonical linear equivalence of localized modules. Invertibility
plus stable freeness implies freeness by Mathlib's
`Module.free_of_isStablyFree_of_invertible`.

This is an internal algebraic derivation from the imported Library argument
and Mathlib's finite-presentation, short-exact-sequence and localization APIs.
No additional literature assertion is used. In particular, this file does
not establish coherence or finite projective dimension for smooth algebras
over valuation rings; those remain separate obligations. It also does not
descend finitely presented modules from a localization, prove Picard
vanishing there, or construct an extended line bundle on a scheme.
