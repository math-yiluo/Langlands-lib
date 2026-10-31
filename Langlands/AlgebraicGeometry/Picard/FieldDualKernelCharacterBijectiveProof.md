# Bijectivity of the actual dual-kernel character over a field

Author: Worker 129.

`Langlands.AbelianScheme.fieldDualKernelCharacterBijective` proves exactly
`Langlands.AbelianScheme.FieldDualKernelCharacterBijectiveStatement` from
`Langlands.AlgebraicGeometry.Picard.FieldDualKernelCharacterBijectiveStatement`.
For an isogeny `f : A → B` of actual abelian schemes over an arbitrary field,
the existing `dualKernelPointCharacter ... T` is bijective for every test
scheme `T` over that field.

The theorem retains the target's exact dual-constructor inputs: the chosen
`HasDualScheme` witnesses, the seven tensor and Picard-zero propositions,
and the inverse Poincaré line bundles with their evaluation isomorphisms.
Its domain is the points of the existing scheme-theoretic kernel of
`dualCommGroupSchemeMapFromEvaluation`; its codomain is the existing
`Cartier.characters` functor of the primal kernel. The only condition on
`f` is the target's `IsIsogeny f`, namely finiteness, flatness and
surjectivity of its underlying morphism.

## Implemented proof

Fix all the constructor inputs, the field, the isogeny and the test scheme.
The proof applies the published assembly lemma
`dualKernelPointCharacter_bijective_of_classification` from
`DualKernelClassComparison`. Its two premises are supplied by the published
theorems `fieldTrivialPullbackPicardZero` and
`fieldTrivialPullbackCharacterBijective`, at precisely this field,
isogeny and test scheme.

The first theorem says that a rigidified family whose underlying bundle has
trivial `f_T` pullback satisfies `IsPicardZeroFamily`. The comparison lemma
uses this to represent every trivial-pullback bundle class by an actual
dual-kernel point. It rigidifies a bundle using a pullback trivialization
and the identity section, applies the chosen dual's universal property,
and lifts the resulting origin equation into the scheme-theoretic kernel.
Equality of underlying Poincaré bundle classes determines the dual point:
an underlying isomorphism can be adjusted to respect rigidifications.
The monomorphic kernel inclusion then determines the kernel point.
These constructions give the actual comparison equivalence
`dualKernelPointPullbackClassEquiv`.

The second theorem proves bijectivity of
`trivialHomPullbackClassCharacter f (universalGlobalFunctions A)` on
actual line-bundle isomorphism classes with trivial pullback.
Its published proof uses faithfully flat descent: equal characters give
isomorphic descended bundles, and a character gives a unit cocycle that
descends to a bundle with that character.

The existing `dualKernelPointCharacter` is definitionally this class
character composed with the comparison map. The assembly lemma composes
their proved bijectivity. Consequently the result concerns the exact
normalized transported-action character in the target, with its existing
orientation. Both premises are discharged by theorems; neither is an
additional input of `fieldDualKernelCharacterBijective`.

The argument keeps `T` arbitrary throughout, including nonreduced test
schemes and test schemes over inseparable field extensions. It adds no
separability, reducedness, characteristic or invertible-degree condition.

## Provenance and scope

This module is a derived assembly of published Library results. The
mathematical source motivating the target and its comparison is Edixhoven,
van der Geer and Moonen, *Abelian Varieties*, preliminary draft built
2012-02-08, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VII, Proposition (7.4), printed pp.99–100 / PDF pp.103–104,
classifies trivial-pullback bundles by characters; Theorem (7.5),
printed p.100 / PDF p.104, uses this description to identify the dual
isogeny's kernel with the Cartier dual of the primal kernel.

The Lean implementation uses the existing rigidified Picard-zero universal
property and the independently proved descent and geometric-fibre
results. It establishes the target's all-test-scheme bijectivity component.
Naturality, additivity, dual existence, geometry of the dual morphism,
kernel duality over an arbitrary base and finite Weil pairing consequences
are separate results.
