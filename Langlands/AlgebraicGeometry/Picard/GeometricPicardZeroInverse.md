# A supplied tensor inverse preserves geometric Picard zero

This module proves that an actual tensor inverse of a translation-invariant
line bundle is translation invariant. It applies this result on every
geometric fibre, constructs the corresponding rigidified Picard-zero
inverse class, and proves its tensor inverse equation in that subset.

## Source and provenance

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter VI, paragraph
(6.2), printed p.88 (PDF p.92), gives the tensor law and compatible
isomorphisms of rigidified line bundles. Chapter VII, Corollary (7.22),
printed p.106 (PDF p.110), identifies `Pic⁰` over a field with the kernel
of the homomorphism associated to a line bundle. The existing Library
geometric Picard-zero predicate uses translation invariance on every
geometric fibre.

The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The construction and proofs here are internal categorical consequences
of the existing actual tensor, translation, pullback and rigidification
conventions. They do not reprove the source's identity-component
characterization or rely on a cube theorem.

## Inputs and limits

The module consumes a supplied ordinary line bundle `M` and an actual
evaluation `L ⊗ M ≅ O`, together with translation-invariance or
geometric Picard-zero membership of `L` as appropriate.
The only theorem hypothesis is the published
`pullbackTensorComparisonIsIsoStatement`.
Ordinary inverse existence is not asserted, and no arbitrary
inverse-existence field is introduced.

The underlying fixed tensor unitors, symmetry and associator already
exist as isomorphisms of sheaves. The comparison construction below uses
them only to compose an isomorphism. It needs no additional pullback
associativity, unit, or symmetry coherence proposition.

## Comparing supplied inverses

`Langlands.Scheme.Modules.tensorInverseComparisonIso` takes module sheaves
`L`, `M`, `N` and evaluations `L ⊗ M ≅ O` and `L ⊗ N ≅ O`. It constructs
an actual isomorphism `M ≅ N` through

`M → O ⊗ M → (N ⊗ L) ⊗ M → N ⊗ (L ⊗ M) → N ⊗ O → N`.

The first and last maps are unitors. The second uses the inverse of the
evaluation for `N`, preceded in the forward direction by symmetry.
The middle map is the fixed associator. The fourth tensors the evaluation
for `M` with the identity on `N`.
This proves existence of a comparison; it does not assert uniqueness
of an isomorphism witness.
`LineBundle.tensorInverseComparisonIso` lifts that same module isomorphism
to the full subcategory of locally free rank-one sheaves.

`pullbackTensorEvaluation` constructs the evaluation for `f*L` and `f*M`
by composing the inverse fixed tensor comparison, the pullback of the
given evaluation, and the fixed pullback-unit isomorphism.

## Translation and geometric fibres

For every section `x` of a group scheme, translation invariance of `L`
provides an actual isomorphism `t_x*L ≅ L`.
Pulling back the supplied evaluation and using the inverse of this
isomorphism in the first tensor factor gives
`L ⊗ t_x*M ≅ O`.
The comparison between supplied inverses then gives `t_x*M ≅ M`.
This is the implemented proof of
`GroupScheme.isTranslationInvariant_tensorInverse`.
It works for an arbitrary group scheme and its sections.

`isGeometricallyPicardZero_tensorInverse` pulls back the given evaluation
to every geometric fibre of the abelian scheme and applies the preceding
translation-invariance result there.
`isPicardZeroFamily_rigidifyInverse` additionally pulls evaluation through
the existing relative-product symmetry to the conventional product order.
It proves membership for the inverse family equipped with the actual
rigidification constructed in `RigidifiedInverse`.

## The inverse class

`picardZeroInverseClass` is the compatible-isomorphism class of this
rigidified supplied inverse, with membership supplied by the preceding
proof. `picardZeroClassesTensor_inverseClass` proves that tensoring the
original Picard-zero class with this inverse class gives
`trivialPicardZeroClass`. Subtype extensionality reduces the equation
to the previously proved rigidified inverse-class equation.

This is a construction from a representative and a supplied ordinary
evaluation. It is not yet an inverse function on all quotient classes
or a complete group structure.
