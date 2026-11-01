# Ample diagonal correspondence over a field

`Langlands.AbelianScheme.FieldAmpleDiagonalCorrespondenceStatement.{u}`
defines a proposition for an arbitrary universe `u`. For every type
`K : Type u` equipped with a `Field K` instance and every Library abelian
scheme `A` over `Spec (CommRingCat.of K)`, the existence of an ample line bundle on `A`
implies the existence of a line bundle `D` on `A ×_K A` with trivial
pullback to both unit axes and ample pullback to the diagonal. This file
states the proposition and proves nothing.

Worker 477 supplied the exact Lean prototype for the parent ample-extension
assembly. Worker 410 prepared this explanation and the focused prerequisite
task. Worker 421 checked the imported constructions and source, and
prepared the Lean/Markdown pair for submission.

## Actual objects and maps

`mumfordProduct A` is the Library's object over `Spec K` whose underlying
scheme is Mathlib's chosen `pullback A.X.hom A.X.hom`. The witness `D` is
an actual Library `LineBundle` on that scheme, namely a locally free
rank-one sheaf of modules. The antecedent quantifies existentially over
`L : LineBundle A.X.left`; it requires only that some such `L` is ample.
The conclusion existentially quantifies one `D` satisfying all three
conditions together.

The first triviality is a `Nonempty` actual module-sheaf isomorphism
`(id,e)*D ≅ O_A`, where `mumfordSection A` is the first unit axis
`(id,e)`. The second is an actual module-sheaf isomorphism
`(e,id)*D ≅ O_A`, using the displayed `pullback.lift` with projections
`A.X.hom ≫ unitSection A` and the identity. These are existential
trivializations; no compatibility or chosen rigidification is asserted.

The diagonal is the actual `pullback.diagonal A.X.hom`. Its pullback of
`D` is the actual line bundle obtained by `LineBundle.pullback`.
`IsAmple` is the Library predicate: the underlying scheme is quasi-compact
(`CompactSpace`), and for every point there exist an integer `n : ℕ` with
`1 ≤ n` and a global section of the actual `n`-th tensor power whose whole
generation open contains the point and is affine.

There are no algebraic-closedness, characteristic, dimension, polarization,
projectivity or symmetry premises. No relation between the witness `D`
and any particular ample line bundle is part of the statement.

## Derived provenance and intended proof route

This is an internal prerequisite designed for the diagonal assembly of
`ValuationRingAmpleExtensionStatement`. It is a weaker field analogue of
the correspondence used in Raynaud's Lemme XI 1.6, rather than a literal
translation of that lemma. It does not construct a Neron-Severi group.
Its proposed proof can avoid algebraic-equivalence machinery. The
Library bundle `AbelianScheme` supplies a commutative group scheme whose
structure morphism is smooth, proper and geometrically connected; these
are built-in data of `A`, not extra premises of this proposition.

For an ample line bundle `L`, take its normalized cross-effect
`m*L ⊗ p1*L⁻¹ ⊗ p2*L⁻¹`, using a trivialization of the fibre of `L` at
the identity over the field. This fibre is a line bundle on `Spec K`, so
the published `fieldLineBundleTriviality` applies. The unit laws and tensor
evaluation trivialize both axes. The balanced cube identity specialized
to `(id,id,[-1])` gives
`[2]*L ≅ L³ ⊗ [-1]*L`; consequently the diagonal pullback of the
cross-effect is isomorphic to `L ⊗ [-1]*L`. Inversion is an isomorphism,
so pullback by inversion and then tensor product preserve ampleness.

The motivating original is J. S. Milne, *Abelian Varieties* (1986 article,
author revision January 2, 2022), registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Corollary 6.4 on p.9 has the balanced cube signs; Corollary 6.6 on the same
page gives `[n]*L` for an arbitrary line bundle and specializes to the
displayed formula at `n = 2`. The p.9 image was read. The published
`FieldCubePullbackStatement` records the corrected balanced formulation,
including the inverse-printing discrepancy in Corollary 6.5.

This paragraph is a route for the future proof, not a formal deduction
implemented here. In particular neither the proposition definition nor
successful compilation proves the theorem of the cube, the two
trivializations, the diagonal isomorphism, or ampleness of its pullback.
