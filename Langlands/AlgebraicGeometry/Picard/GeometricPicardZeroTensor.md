# Tensor preserves translation invariance and geometric Picard zero

This module restricts the fixed canonical pullback tensor comparison to actual
line bundles and proves closure of translation invariance and the geometric
Picard-zero condition under tensor product. Schemes and fields use universe `u`.
Every construction retains the explicit hypothesis
`preservation : Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement`.
This proposition says that the specified canonical comparison is invertible for
every scheme morphism; this module does not prove that proposition or choose an
unrelated comparison.

## Line-bundle isomorphisms

`LineBundle.tensorIso preservation e d` tensors two actual line-bundle
isomorphisms. The proof maps their product under the existing tensor bifunctor,
after identifying its object function with `LineBundle.tensor`.

For `f : X → Y` and line bundles `L, M` on `Y`,
`LineBundle.pullbackTensorObjIso preservation f L M` has type

`f* (L ⊗ M) ≅ f* L ⊗ f* M`.

It is exactly the component at the underlying pair of module sheaves of
`asIso (pullbackTensorComparison f)`, lifted to the full subcategory of locally
free rank-one sheaves. Local rank one of the objects is supplied by the existing
pullback and tensor constructions. The result is an objectwise isomorphism;
this module does not package it as a natural isomorphism of bifunctors.

## Closure proofs

For any group scheme `G/S`, `GroupScheme.isTranslationInvariant_tensor` says
that the tensor of two line bundles invariant under every section translation
is invariant under every section translation. For a section `x`, its proof
chooses witnesses `t_x* L ≅ L` and `t_x* M ≅ M`, then composes

`t_x* (L ⊗ M) ≅ t_x* L ⊗ t_x* M ≅ L ⊗ M`.

The first arrow is the preceding canonical comparison and the second is
`tensorIso` applied to the two witnesses. No commutativity of `G` is needed.
The predicate tests sections over the current base and does not assert a
coherent chosen family of isomorphisms.

For an abelian scheme `A/S`,
`AbelianScheme.isGeometricallyPicardZero_tensor` proves closure of the existing
geometric-fibre predicate. For each algebraically closed field `K : Type u`
and `s : Spec K → S`, the two hypotheses give translation-invariant line
bundles on the actual fibre `A_K`. The previous lemma tensors those bundles.
The inverse of `pullbackTensorObjIso` for the projection `A_K → A` then
transports translation invariance to the restriction of `L ⊗ M`. This is the
required geometric-fibre condition. There is no noetherian or projectivity
hypothesis on `S`.

## Provenance and scope

This is a derived closure argument for the predicate constructed in
`GeometricPicardZero`. Its source convention is Edixhoven, van der Geer and
Moonen, *Abelian Varieties*, preliminary draft, literature ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Printed p.95 (PDF p.99) gives `φ_L(x) = [t_x* L ⊗ L⁻¹]`;
Corollary (7.22), printed p.106 (PDF p.110), identifies the kernel of this
assignment with `Pic⁰` over a field. The parent task explicitly chooses the
translation-invariance criterion on algebraically closed geometric fibres.
The elementary closure proof implemented here uses tensor functoriality and
the fixed pullback comparison; it does not invoke or prove that kernel theorem.

This contribution supplies tensor closure of the chosen condition. Group
axioms, inverses, a group law on relative classes, and representability remain
separate constructions. All conclusions here retain the stated canonical
comparison-invertibility hypothesis.
