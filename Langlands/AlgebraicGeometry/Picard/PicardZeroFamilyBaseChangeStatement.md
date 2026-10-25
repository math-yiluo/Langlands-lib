# Geometric Picard zero under ground base change

`Langlands.AbelianScheme.PicardZeroFamilyBaseChangeStatement.{u}` states
preservation and reflection of the existing geometric Picard-zero condition
by the actual ground-base pullback of rigidified families. For arbitrary
schemes `S, S' : Scheme.{u}`, a morphism `b : S' → S`, an abelian scheme
`A/S`, a parameter scheme `T/S'`, and
`L : RigidifiedFamily A ((Over.map b).obj T)`, it states

`IsPicardZeroFamily A L ↔ IsPicardZeroFamily ((baseChange b).obj A) ((familyBaseChange b A T).obj L)`.

Here `Over.map b` regards the same parameter scheme as an `S`-scheme.
The forward implication preserves the condition; the reverse implication
reflects it. The statement imposes no reducedness, noetherian, field,
projectivity, or additional coherence hypothesis on the schemes or families.

Both predicates are the published `IsPicardZeroFamily`, unchanged. This
predicate forgets the rigidification, moves the line bundle from `T ×_S A`
to `A ×_S T` by the inverse relative-space symmetry, and asks for translation
invariance on every algebraically closed fibre. Explicitly it tests every
algebraically closed field `K : Type u` and every map `Spec K → T.left`.
Translation invariance means that pullback along translation by every
`K`-point is isomorphic to the restricted line bundle, with no chosen
coherent system of isomorphisms.

The new family is exactly the object supplied by the published
`familyBaseChange b A T`. Its underlying line bundle is the actual pullback
along `familyBaseChangeSpaceMap b A T`, the canonical map
`T ×_{S'} A_{S'} → T ×_S A`. The functor retains the rigidification using
the existing comparison of the relative unit sections.

## Derived provenance and remaining proof obligations

This is an internal consequence proposed for the published constructions in
`FamilyBaseChange`, `RelativePicardZero`, and `GeometricPicardZero`.
It is not attributed to a new literature theorem. The source motivation
and comparison boundaries of the existing geometric predicate remain those
described in the paired Markdown of the latter two modules. This statement
does not assert its equivalence with a literature definition of algebraic
equivalence or of a Picard identity component.

For each algebraically closed `K` and map `s : Spec K → T.left`, the
canonical composition isomorphisms for group-scheme base change should
identify the two iterated fibres over `Spec K`. Both arise from the same
map `Spec K → T.left → S' → S`. A proof must compare the fibre projections,
the relative-space symmetries used in `familyLineBundle`, and
`familyBaseChangeSpaceMap`. Actual line-bundle pullback composition
isomorphisms must then identify the two restricted bundles. Translation
invariance should transport along the group-scheme isomorphism in both
directions, using the published
`Langlands.GroupScheme.isTranslationInvariant_pullback` and invariance
under line-bundle isomorphism. The inverse comparison is needed for
reflection; preservation alone does not prove this statement.

This module defines the theorem obligation as a proposition and proves
neither implication. It asserts no existence of a dual scheme, universal
family, or representing object. Equivalence of rigidified-family categories,
compatibility with parameter pullback, and transport of unique classification
belong to the separate universal base-change work.
