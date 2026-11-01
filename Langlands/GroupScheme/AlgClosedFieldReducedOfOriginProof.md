# Reducedness of a group scheme from its identity stalk

This module proves the published proposition
`Langlands.GroupScheme.AlgClosedFieldReducedOfOriginStatement.{u}`:

```lean
theorem Langlands.GroupScheme.algClosedFieldReducedOfOrigin :
    Langlands.GroupScheme.AlgClosedFieldReducedOfOriginStatement.{u}
```

For every algebraically closed field `k : Type u` and actual group object
`P : Over (Spec (CommRingCat.of k))`, local finite type of `P.hom` and
ring-theoretic reducedness of its identity stalk imply scheme-theoretic
reducedness of `P.left`. The theorem has no additional hypotheses and works
for arbitrary universe `u`. It uses the published statement unchanged.
In particular, no commutativity, connectedness, quasi-compactness,
properness or smoothness is assumed.

The two private helpers first prove that a Jacobson scheme is reduced if
all its closed-point stalks are reduced.

- `reduced_affine_of_closed_stalks` considers an affine open immersion
  `f : Spec R ⟶ X`. A maximal ideal of `R` gives a closed point of `Spec R`
  by `PrimeSpectrum.isClosed_singleton_iff_isMaximal`. Its image is closed
  in the Jacobson space `X`, using the open-embedding identity
  `f.isOpenEmbedding.preimage_closedPoints`. The stalk map of the open
  immersion is an isomorphism, so its inverse embeds the affine stalk into
  the reduced stalk of `X`. `Spec.stalkIso` then identifies the affine stalk
  with the corresponding localization of `R`. Reducedness descends along
  these injective ring maps by `isReduced_of_injective`.
  `isReduced_ofLocalizationMaximal` gives reducedness of `R`, and
  `affine_isReduced_iff` gives reducedness of `Spec R`.
- `reduced_of_closed_stalks` applies the preceding helper to every member
  of `X.affineCover` and then uses
  `AlgebraicGeometry.IsReduced.iff_of_openCover`.

The main theorem sets `e` to the actual identity point
`(η[P]).left (IsLocalRing.closedPoint k)`. Local finite type over the field
gives `JacobsonSpace P.left` by `LocallyOfFiniteType.jacobsonSpace`.
For each closed point `x`, `pointOfClosedPoint` supplies an actual
`k`-rational section `x'` of `P`, with value `x` at the unique field point.
The actual group-object isomorphism `α = GrpObj.mulRight x'` satisfies
`η[P] ≫ α.hom = x'` by the unit law
`CategoryTheory.MonObj.lift_comp_one_left`. Evaluation gives `α.hom.left e = x`.
Its stalk map at `e` is therefore an injective ring map from the stalk at
`x` to the reduced stalk at `e`. This proves reducedness of every
closed-point stalk, and the private helper gives reducedness of `P.left`.

The imports are the published statement,
`Mathlib.RingTheory.LocalProperties.Reduced` for detection by maximal
localizations, and `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` for
group-object translations. The three backward elaboration options change
only elaboration. Inspection of the theorem reports only `propext`,
`Classical.choice` and `Quot.sound`.

The mathematical provenance of the target is the algebraically closed
translation argument in Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, Proposition (3.17)(ii), printed pp.38–39
(PDF pp.42–43), as explained in the statement's Markdown. The registered
source is `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
This proof implements the propagation directly with Mathlib rational
points, translations, stalk maps and maximal localizations. It uses no
Picard, tangent, cohomology, ample-bundle or finite-stabilizer result.

Worker 453 authored the proof and this explanation, first shared as
revision 1 of this task's public draft. Worker 1173 rechecked the pair in
the pinned environment and submitted it unchanged except for this
paragraph. Development compilation does not establish independent
acceptance or publication.
