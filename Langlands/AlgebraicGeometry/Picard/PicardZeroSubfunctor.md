# The geometric Picard-zero subfunctor

For any abelian scheme `A/S`, this module restricts the existing presheaf of
rigidified line-bundle classes to the geometric-fibre Picard-zero subsets.
Schemes have universe `u`, and the presheaves take values in `Type (u + 1)`.
The construction has two explicit proof parameters:

- `stability : AbelianScheme.PicardZeroPullbackStatement`, asserting preservation
  of the geometric-fibre condition by the actual relative rigidified pullback;
- `coherence : SchemeModule.RigidifiedModule.PullbackCoherenceStatement`,
  asserting the rigidification compatibility needed for the identity and
  composition comparisons of pullback.

The module does not prove either proposition. Their separate proof obligations
are retained in the types of the constructions that use them.

## Class preservation and restricted pullback

`isPicardZeroClass_pullback` uses quotient induction on a rigidified
isomorphism class. On a representative `L`, the class predicate and the
quotient pullback reduce to `IsPicardZeroFamily A L` and the actual relative
pullback of `L`. The required implication is exactly the supplied `stability`
proof. This lemma does not use `coherence`.

`picardZeroClassesPullback` pairs the existing `classesPullback` with this
preservation proof. Its domain and codomain are the existing
`PicardZeroClasses A U` and `PicardZeroClasses A T`; no new quotient or
equivalence relation is introduced.

## Subfunctor, presheaf and inclusion

`picardZeroSubfunctor` is a Mathlib `CategoryTheory.Subfunctor` of
`RigidifiedLineBundle.classPresheaf` specialized to the unit section of `A`.
Its subset at `T` is exactly `IsPicardZeroClass A` on the ambient classes
over `T.unop`, and its map-closure proof is the preceding quotient-induction
lemma. The ambient presheaf uses `coherence` for its functor laws.

`picardZeroPresheaf` is this subfunctor's `toFunctor`. Its objects are the
existing subtypes, and its maps restrict the ambient class pullback. Mathlib's
construction proves the functor laws by subtype equality from the ambient
laws. `picardZeroPresheaf_map` identifies each restriction with
`picardZeroClassesPullback` by reflexivity.

`picardZeroInclusion` is the subfunctor's canonical natural transformation
into the ambient presheaf. Its component forgets only the membership proof;
`picardZeroInclusion_app` proves this by reflexivity. Its `Mono` instance is
Mathlib's instance for the subfunctor inclusion, whose cancellation follows
from injectivity of subtype inclusion.

## Provenance and scope

This is derived categorical infrastructure for the geometric-fibre criterion
chosen in parent-task item 3. The registered original source is Edixhoven,
van der Geer and Moonen, *Abelian Varieties*, preliminary draft, literature ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VI §1, paragraph (6.2), printed p.88 (PDF p.92), describes rigidified
classes and their actual pullback. Printed p.95 (PDF p.99) gives the point
formula for `φ_L`, and Corollary (7.22), printed p.106 (PDF p.110), identifies
the field Picard-zero kernel. These motivate the existing predicates imported
here. The restriction to a subfunctor is the general categorical construction
implemented above, conditional on the stated compatibility proofs.

No projectivity or noetherian hypothesis is imposed on `S`. The module
constructs a set-valued presheaf and its monomorphic inclusion; it does not
yet supply the tensor-product group law, identify this presheaf with an
identity component of a Picard scheme, prove it is a sheaf, or establish
representability or existence of a dual abelian scheme.
