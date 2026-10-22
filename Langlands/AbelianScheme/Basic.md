# Abelian schemes with explicit commutativity

Author: Worker 129.

`GroupScheme.IsAbelian` is smoothness, properness and geometric connectedness
of the actual structure morphism. This is Lan, 2008 thesis, Definition1.3.1.1,
printed p.103, over an arbitrary scheme. `AbelianScheme` also requires explicit
commutativity, as permitted by the parent contract. Equivalence with the source
definition requires the separate `SourceDefinitionEquivalence` proposition and
a proof task;
no such theorem is assumed here. Lan Corollary1.3.1.7, printed p.108, derives
commutativity by applying rigidity to inversion, citing GIT Corollary6.5,
printed p.117. GIT Chapter6 restricts to locally noetherian schemes and its
Definition6.1, printed p.115, states a noetherian base; Lan's Theorem1.3.1.3
and Corollary1.3.1.6 explain the arbitrary-base reduction.

The Hom abelian groups and endomorphism ring are inherited from the actual
commutative group scheme. Pullback transports the group structure and uses
Mathlib's stability-under-base-change results for each geometric property.
Relative dimension g is the actual Mathlib smooth-relative-dimension predicate;
it is not an arbitrary field in a record or an unjustified global constant on
disconnected bases. Its base-change law is Mathlib's pullback stability.

Sources read: registered Lan thesis `lan-2008-arithmetic-compactifications-pel-thesis`,
SHA256 c3086d5140bab887e31a508cf4bf8804f092326a35882fc003a3422c4ab65bdd,
PDF143–149 (printed103–109); registered GIT source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
SHA256 3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16,
PDF128 and130 (printed115 and117). No source errata notes present in project.

The category has precisely the Hom types of its underlying commutative group
schemes; `commHom`, `groupHom`, and `hom` successively expose those morphisms,
the morphisms of group objects, and the morphisms of schemes. Composition and
identity are inherited. Bilinearity is inherited from the commutative
category's `Preadditive` structure; no geometric assumptions are needed for
these algebraic laws. `End A` is `CategoryTheory.End A`: multiplication
`f * g` is `g ≫ f`, with the identity as unit. `points A` is the represented
group-valued functor of points of the underlying group scheme.

`isAbelian` proves only the forward forgetful direction: every bundled object
satisfies the source's three geometric conditions. The converse is not a
constructor and is not silently available as an instance. In particular,
`AbelianScheme` is not asserted here to cover every `GroupScheme.IsAbelian`
object. The explicit-commutativity convention is justified by the cited
mathematical corollaries and awaits a formal proof of the separate equivalence.

`HasRelativeDimension A g` is `SmoothOfRelativeDimension g A.X.hom`, Mathlib's
actual chart-based predicate. It records that around every source point there
are affine source and target neighborhoods whose ring map is standard smooth
of relative dimension `g`. It does not assert existence of a uniform `g`.
The accessor and its pullback lemma are internal derived interface choices,
not separate claims quoted from Lan. The base-change functor preserves this
specified property by Mathlib's morphism-property pullback stability. No Lie
module or local-freeness theorem is asserted in this module.
