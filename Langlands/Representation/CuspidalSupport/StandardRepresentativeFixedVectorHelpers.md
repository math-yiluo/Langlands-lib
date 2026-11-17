# Fixed-vector constituent and criteria for one standard cuspidal presentation

This derived supporting module concerns an arbitrary published
`BernsteinStandardFamily i ν`. It constructs a chosen fixed-vector constituent
of a standard Bernstein induction and proves the reverse implication of the
first claim in Renard VI.10.6's Corollary, together with an equivalence for a
specified cuspidal support presentation. It does not prove
`StandardRepresentativeFixedVectorCriterionStatement`: the forward implication
for an arbitrary representative of an inertial class remains outside this module.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, VI.10.6, printed pages 213–215, PDF pages
219–221. Its registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, with SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The author read these three original pages. The proof uses the already published
normal-level Mackey criterion instead of the Corollary's Jacquet-module route.

`nontrivial_bernsteinInduction_fixedVectors_iff_exists_cuspidalSupport`
says that the induction of a specified datum `a` has a nonzero compact-open
`K`-fixed vector exactly when some irreducible representation with cuspidal support
`a` has one. In the forward direction, the published
`SmoothRep.hasFixedVectorConstituent_of_nontrivial` keeps a nonzero fixed vector
in an irreducible quotient of its cyclic subrepresentation. In the reverse
direction, `SmoothRep.nontrivial_fixedVectors_of_isSubquotient` uses compact-open
exactness to lift a nonzero fixed vector from the subquotient.
The carrier of the constituent is `max uF uV`, matching `bernsteinInduction`.

`bernsteinFixedVectorConstituent` is the noncomputable choice of this witness,
given `a`, a compact open level `K`, and nontriviality of the induction's fixed
space. `bernsteinFixedVectorConstituent_spec` records both the prescribed
cuspidal support and nontriviality of the chosen representation's `K`-fixed space.
Irreducibility and the subquotient relation are included in
`IsBernsteinCuspidalSupport`. No uniqueness or canonical choice is asserted.
The definition is an internal witness construction derived from the proved
existence equivalence; it is not a separate construction attributed to Renard.
The definition, its specification, and the first equivalence do not use the
valuative relation, the local-field hypothesis, or local finite type of `G`.

`exists_bernsteinCuspidalSupport_fixedVectors_iff` combines that equivalence
with `Jacquet.nontrivial_standardInduction_fixedVectors_iff`. Its level
hypotheses are compact openness of `K`, normalization by `K₀`, the minimal
standard Iwasawa decomposition with `K₀`, and the Iwahori decomposition of `K`
along the standard parabolic of `a`. The resulting right side is the nonzero
fixed space of `bernsteinLiteralLeviRep` for
`K.toSubgroup.comap (levi i ν a.roots).subtype`. It requires neither compactness
of `K₀` nor containment of `K` in `K₀`. These stronger assumptions occur in the
published target, but the imported Mackey criterion does not use them.

`exists_bernsteinInertialSupport_fixedVectors_of_literalLevi` then forgets
the precise support presentation using
`IsBernsteinCuspidalSupport.inertial`. Thus a nonzero literal Levi fixed vector
gives an irreducible representation in the datum's inertial class with a nonzero
`K`-fixed vector.

The construction and all four lemmas are unconditional consequences of the imported Library
theorems. They assume no admissibility, finite length, Bernstein decomposition,
or inertial-support invariance. In particular, the converse of the last result
requires additional work and is not asserted here.
