# The adjunction in Renard VI.7.2, second Lemma

Worker 132. This is a supporting unit for Task 5419. It proves clause (i)
for any supplied family of left adjoints to the literal cuspidal inclusions.
It also proves injectivity of the unit for every adjunction whose left adjoint
is faithful. It does not assert existence of the cuspidal reflectors,
faithfulness or exactness, and does not prove the whole
`BernsteinCuspAdjunctionStatement`.

## Source and implemented proof

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, VI.7.2 second Lemma, printed pp.182–183 /
PDF pp.188–189; source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These pages were read. The categorical helpers are internal derived content.

`piLimitAdjunction` assembles a family of adjunctions with common source:
a map from the tuple of left-adjoint objects is a tuple of maps, which the
component adjunctions identify with the legs of a cone. Taking the limiting
cone yields the adjunction to the product. The proof checks both inverse
identities and both naturality conditions. `piCoproductAdjunction` uses the
natural isomorphism between colimits and limits of discrete diagrams in a
category with biproducts. Empty indexing types are allowed.

`normalizedJacquetInductionAdjunction` is a compatibility name for the published
`Langlands.Aubert.General.firstAdjointnessAdjunction` in `InductionLimits`.
It uses the same actual normalized first-adjointness maps and naturality. The group universe
is independent from the auxiliary carrier universe, and carriers lie in their
maximum, so normalized induction has exactly the required end universe.

`bernsteinCuspAdjunction_of_reflectors` applies that adjunction at every
standard parabolic of the actual `BernsteinStandardFamily`. Unimodularity is
proved by the published standard-cocharacter theorem and the actual unipotent
compact-containment theorem; it is not added as a hypothesis. Each adjunction
is composed with the supplied cuspidal reflector adjunction. There are finitely
many standard indices, and `SmoothRep` is abelian, so their finite biproduct
identifies product and coproduct. The resulting right adjoint is literally
the `Functor.pi`, discrete-diagram and `colim` composite in the target.
Independent `uF` and `uV` are retained.

`injective_adjunction_unit` uses Mathlib's result that a faithful left adjoint
has monic units, followed by the published equivalence between monicity and
carrier injectivity in `SmoothRep`. This gives clause (iii) once faithfulness
of `R` is known, for every adjunction. This categorical proof does not need
the exactness hypotheses used by Renard's printed kernel argument.

The target statement and all its imported Lean/Markdown pairs are unchanged.
