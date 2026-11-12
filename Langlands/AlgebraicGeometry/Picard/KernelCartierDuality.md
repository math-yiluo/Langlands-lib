# Actual kernel Cartier duality as group-valued functors

Author: Worker 195.

This internal assembly combines the published naturality, additivity and
all-test-scheme bijectivity of the normalized Poincare kernel character.
It upgrades that particular map to an isomorphism of abelian-group
presheaves over a field. No replacement pairing or unspecified duality
isomorphism is input.

Let `f : A → B` be an actual abelian-scheme homomorphism. Retain the existing
`HasDualScheme` witnesses, inverse Poincare line bundles and evaluation
isomorphisms for `A` and `B`, and the seven named tensor/Picard propositions
of their dual-group constructors. The morphism `df` below is the exact
`dualCommGroupSchemeMapFromEvaluation` with these inputs. Both kernels
are the existing scheme-theoretic kernels.

`GroupScheme.additivePoints G` is the usual presheaf of points of an actual
commutative group scheme, with the group law written additively. Its map
on a test morphism is precomposition. Its identity and composition proofs
are the category laws; preservation of addition and zero is given by the
existing group-object composition laws.

`dualKernelCharacterAddNatTrans` has source the additive points of
`kernel df` and target `Cartier.characters (kernelCommGroupScheme f)`.
Its component is exactly `dualKernelPointCharacterAddHom`, and naturality
is the existing `dualKernelPointCharacter_restrict`. This transformation
is constructed over any base, without claiming bijectivity there.

Over `Spec k` for an arbitrary field `k`, assume the existing `IsIsogeny f`
condition (finite, flat and surjective). `fieldDualKernelCharacterEquiv`
uses the published theorem `fieldDualKernelCharacterBijective` and
`AddEquiv.ofBijective`. `fieldDualKernelCartierIso` assembles these
component equivalences using the same naturality theorem. Its forward
natural transformation is proved equal to the one just constructed by
component extensionality. Thus it retains the normalized map, with the
transported translation action divided by the trivial action.

`fieldDualKernelCharacterHomIso` composes with the existing
`Cartier.characterHomNatIso`. Its target at `T` is the group of actual
homomorphisms from the base-changed primal kernel to the multiplicative
group over `T`. Its restriction maps are the existing pullback maps with
their canonical base-change comparisons. Finally,
`fieldDualKernelCharacter_existsUnique` expresses unique recovery of an
actual dual-kernel point from any character. Its proof uses surjectivity
of the equivalence and injectivity of the published normalized character.

Every test scheme over `k` is quantified, including nonreduced tests and
inseparable field extensions. No algebraic closedness, separability,
characteristic-zero or invertible-degree hypothesis is imposed. The
result identifies the character functor represented by the actual dual
kernel as a group-valued functor; it does not construct a second
Cartier-dual scheme. Relative bijectivity over arbitrary base schemes,
existence and geometry of dual abelian schemes, and the assertion that the
dual morphism is itself an isogeny are outside this unit. No polarization,
chosen roots of unity or integral perfectness for nonprincipal
polarizations is asserted.

The original source is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft built 2012-02-08, Chapter VII,
Proposition (7.4), printed pp.99–100 / PDF pp.103–104, and Theorem (7.5),
printed p.100 / PDF p.104. Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
These pages were read directly. Proposition (7.4) supplies the normalized
character convention and its compatibility with arbitrary test-scheme
base change; Theorem (7.5) applies it to kernels of dual isogenies over a
field. The new Lean construction packages already published proofs of
these components; the source does not display the exact Lean presheaf
formulation. No source-specific errata note was found in the project or
Library `notes/errata` paths.
