# Smooth scheme atlases of the actual coherent-family stack over a field

`FieldCoherentStackAtlasStatement.{u}` is a proposition without a proof in this
module. For every field `k : Type u` and every scheme
`X : Over (Spec (CommRingCat.of k))`, its sole hypothesis is `IsProper X.hom`.
Its conclusion is `Stacks.HasLocallyFiniteTypeSmoothSchemeAtlas` for the
published `FamilyGroupoid.pseudofunctor X.hom`, with its morphism universe
explicitly lifted to `u + 1`.

Write `S = Spec k` and `f = X.hom`. The assertion requires an actual scheme
`U` over `S` and an actual flat locally finitely presented module family
on `U ×_S X.left`, with `U → S` locally of finite type. For every scheme
`T` over `S` and every actual family on `T ×_S X.left`, the full point-fibre
presheaf must be naturally represented by a scheme `P` over `T.left`,
with `P → T.left` smooth and surjective.

At every `Z → T.left`, a point consists of a map over `S` to `U` and an
actual isomorphism between the two ordinarily pulled-back module families.
The isomorphism is retained as data. Restrictions use the published coherent
pullback comparisons. Representation includes all objects and maps of
`Over T.left`; tests can be empty, nonreduced, nonnoetherian or
non-quasi-compact. The explicit morphism-universe lift changes neither
the underlying families nor the isomorphisms. The published
`PseudofunctorHomLift.presheafIso` identifies its point fibres naturally
with the corresponding universe lifts of the original point fibres.

## Source and derivation

This is a derived field specialization of the following original Stacks
Project assertions. The cited HTML files are retained publication snapshots;
their text companions are reading aids.

- `08KA.html`, Situation 99.5.1 and Lemma 99.5.2, in
  `stacks-coherent-sheaf-stack-08ka-2026-11-01` (folder SHA-256
  `4ac7cc2a6a797cd51c3a793bbf7684229a8f43b69031e852a0681c219ab99078`),
  specifies finitely presented quasi-coherent modules flat over the test
  base with proper support, actual module isomorphisms, and ordinary
  pullback. The published `FamilyGroupoid` uses these actual modules.
  Its finite-presentation condition implies quasi-coherence.
  `FamilyGroupoid.hasProperSupport` and `properSupportExists` prove
  scheme-theoretic proper support after every base change of proper `f`.
  Thus a separate support witness in each object is unnecessary.
  Inverting fibre isomorphisms reconciles the source's arrow convention
  with the forward core arrows.
- `08KA.html`, Theorem 99.5.12, in the same source, gives algebraicity
  for a separated, flat morphism of finite presentation. A proper
  morphism to a field spectrum is separated and of finite type. The base
  is noetherian, so the morphism is of finite presentation, and every
  scheme over the field is flat over it. These field reductions remain
  obligations of the eventual Lean proof.
- `026O.html`, Definition 94.12.1, third condition, in
  `stacks-picard-stack-algebraicity-2026-11-01` (folder SHA-256
  `f152eeac350ef0fb061c6651f63b2a7cdeb5d175ad92aacbf99e5e9f6eb0b0e0`),
  provides a smooth surjective scheme atlas of an algebraic stack.
  Its morphism to this actual family stack corresponds to a family over
  the atlas scheme.
- `0DLY.html`, Lemma 108.4.1, in the same retained source, gives the
  coherent-stack diagonal affine of finite presentation over the base.
  Consequently the fibre of `U` and `T` over the stack is affine over
  the scheme `U ×_S T`, and is itself a scheme. Smoothness and
  surjectivity over `T` follow by base change of the atlas.
  This fibre represents the entire actual isomorphism-bearing point-fibre
  presheaf above. More explicitly, `08K7.html`, Proposition 99.4.3, in
  `stacks-isom-functor-08k7-2026-11-02` (folder SHA-256
  `a05b61ba562e7e65dd2b64446e779a6bb67af1846c0a00f4a656d64a2b2c27b5`),
  makes the Isom functor affine of finite presentation for finitely
  presented relatively flat modules with proper support.
- `0DLZ.html`, Lemma 108.4.2, in
  `stacks-picard-stack-algebraicity-2026-11-01`, gives local finite
  presentation of the coherent stack over its base. Its proof uses
  `08KA.html`, Lemma 99.5.6, on preservation of filtered limits.
  The composition of a smooth atlas with this structure map is locally
  of finite presentation, hence locally of finite type over `S`.

The retrieved `08K7`, `026O`, `0DLY` and `0DLZ` pages have no comments
changing these assertions. The comments on `08KA` concern a possible
vector-bundle corollary and do not change the cited results. No source
errata note is present in the project collection at the time of writing.

## Scope and proof boundary

The statement retains arbitrary `u`, arbitrary fields, and every proper
scheme over them. It assumes no projectivity, smoothness, reducedness,
connectedness, rational point, section or condition on global functions.
The full groupoid consists of all flat locally finitely presented module
families; it is not restricted to line bundles.

This module supplies a statement only. Its proof must construct the
atlas and all represented fibres for the actual published pseudofunctor,
including the coherent restrictions and universe lift. Algebraic-space
fibres alone do not meet its scheme-representation requirement. This
statement does not prove the Picard-stack atlas, an open-substack
restriction, a Picard-sheaf representability theorem or a universal
line bundle on such a sheaf.
