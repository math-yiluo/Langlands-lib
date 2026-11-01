# Conditional whole-spectrum assembly

Author: Worker 146.

`wholeSpectrumRationalGluing_of_standard_inputs` is a conditional assembly
theorem for the unchanged `WholeSpectrumRationalGluingStatement.{u}`. Its
explicit premises are the published propositions
`FiniteRationalRefinementStatement.{u}` and
`NontrivialStandardRationalGluingStatement.{u}`.

`wholeSpectrumRationalGluing_of_nontrivial_standard` applies this helper to
the published `finiteRationalRefinement` theorem from
`Langlands.Geometry.Analytic.StrictTestDomain.FiniteRationalRefinementProof`.
It therefore has just one explicit premise:
`NontrivialStandardRationalGluingStatement.{u}`. Both assembly theorems are
polymorphic in `u`. The separate `WholeSpectrumRationalGluingProof` applies
this helper to the published `nontrivialStandardRationalGluing` theorem.
No premise is added to the unchanged whole-spectrum target.

The proof first treats an empty covering index. Its point-cover assumption
makes the spectrum empty. The preparation module uses the published
nonemptiness theorem for nonzero presented strict bases to deduce that the base
is zero. Its empty-cover gluing lemma supplies the unique base section.

For a nonempty covering index, split on the existence of a scalar of norm
greater than one. If such a scalar exists, apply the refinement premise to
obtain a standard rational cover. Choose a containing original rational locus
for each standard locus and use the actual `RationalData.Inclusion` to form
the restriction maps. The refinement adapter transfers gluing from this
standard cover to the original cover. It obtains both global gluing and local
separation after base change from the universal standard-cover descent
premise. That base-change separation is essential to recover every original
section.

If no scalar has norm greater than one, every scalar has norm at most one.
The localization adapter's `existsUnique_whole_gluing_of_trivial_scalar_norm`
then applies. Its localization premise has already been discharged by the
published `trivialScalarRationalLocalization` proof.

The first assembly is an internal consequence of the two named propositions,
the published localization theorem, and the formal adapters. The second is
its direct application to the published finite refinement proof, with no
additional geometric or analytic argument. It preserves the
coefficient universe, zero and nonreduced bases, empty covering types and
rational loci, empty numerator tuples, and trivial scalar valuations. Its
unconditional application has scope scalar degree-zero descent for unit-radius
rational quotients over presented strict bases. No higher Cech exactness,
admissibility, arbitrary radii, relative rational-target gluing, or categorical
sheaf theorem is asserted.
