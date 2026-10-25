# Geometric-point detection for actual rigidified Picard-zero families

`Langlands.AbelianScheme.PicardZeroGeometricDetectionStatement.{u}` is a
Prop-valued definition. For every `S : Scheme.{u}`, `A : AbelianScheme S`,
`T : Over S`, and actual rigidified family `L : RigidifiedFamily A T`, it
states that `IsPicardZeroFamily A L` holds if and only if the same predicate
holds for every actual relative rigidified pullback of `L` to a geometric
point of `T.left`.

Precisely, the right side quantifies over every `K : Type u` with `Field K`
and `IsAlgClosed K`, and every scheme morphism
`s : Spec (CommRingCat.of K) ⟶ T.left`. Its source in the slice over `S` is
`Over.mk (s ≫ T.hom)`, and the pullback morphism is exactly
`(Over.homMk s rfl : Over.mk (s ≫ T.hom) ⟶ T)`. The family in the conclusion
is the image of `L` under
`RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
(unitSection_comp A)` at that slice morphism. Thus the statement retains
the actual underlying bundle and its canonical pulled-back rigidification.
It does not replace the family by an isomorphism class.

The definition uses only the published `RelativePicardZero` interface and
its imported constructions. In that interface, the rigidified family has
total space `T ×_S A`; `familyLineBundle` pulls its underlying bundle across
the inverse canonical symmetry to `A ×_S T`.
`IsPicardZeroFamily` then tests translation invariance on every geometric
fibre of that abelian scheme over `T.left`. The same predicate on the right
side still makes all of its own geometric-fibre tests over `Spec K`.
All schemes and fields in these tests use universe `u`.

The base `S` is arbitrary and `T` may be nonreduced. There are no additional
projectivity, noetherian, representability, or openness hypotheses, no
assumed dual scheme, and no assumed geometric-detection or transport
result. This target asserts geometric detection only; it asserts no open
locus or comparison with an identity component. It concerns relative
pullback inside `Over S`, whereas `PicardZeroFamilyBaseChangeStatement`
concerns the separate ground-base-change construction `familyBaseChange`.

## Provenance and proof obligation

This is an internal compatibility target for the existing definitions,
prepared from Worker 390's unaccepted design. Worker 390 is a coauthor of
the statement. The design's previous compilation is not mathematical
acceptance or a proof.

The source motivating the existing definitions is Edixhoven, van der Geer
and Moonen, *Abelian Varieties*, preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VI, (6.2), printed p.88 (PDF p.92), describes rigidification and
actual relative pullback. The point formula on printed p.95 (PDF p.99)
and Corollary (7.22), printed p.106 (PDF p.110), motivate the existing
translation-invariance criterion. These passages do not state this exact
compatibility target. Their additional hypotheses for other Picard-functor
claims are not imported into this proposition.

The forward implication follows by specializing the published theorem
`Langlands.AbelianScheme.picardZeroPullback` to the displayed slice
morphism. For the reverse implication, fix a field `K` and point `s` from
the original geometric-fibre test. The hypothesis gives the geometric
Picard-zero condition on the actual pulled-back family over `Spec K`.
Testing that condition at the identity map of `Spec K` gives translation
invariance on an iterated base change. A proof must compare this group
scheme with the original fibre of `A_T` at `s`, identify the actual
restricted line bundles using the relative-space symmetries and pullback
composition isomorphisms, and justify transport of translations and their
invariant-bundle isomorphisms through the group-scheme comparison. Those
comparisons are proof obligations, not hypotheses or definitional
equalities asserted by this module.

The module defines the proposition without proving it. Its proof belongs
to a separate task after independent statement acceptance and publication.
