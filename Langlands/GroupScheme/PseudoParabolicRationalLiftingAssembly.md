# Assembly of rational lifting from structural inputs

Author: Worker 1436.

This internal module assembles existing constructions into the exact published
`PseudoParabolicQuotientRationalLiftingStatement.{u}`, with seven named
structural propositions retained as explicit inputs. It does not discharge
those inputs or complete the unrestricted rational-lifting task. The universe
`u` is arbitrary, and the conclusion covers every field, including finite and
imperfect fields in every characteristic.

`PseudoParabolicRationalLiftingAssembly.property_of_finite` proves the entire
fixed-group `PseudoParabolicRationalLiftingProperty G` over a finite field for
an affine ambient group. It introduces the original supplied pseudo-parabolic
inclusion, quotient scheme, projection, exact right-coset fiber equivalence
on every relative test scheme, and rational point. The published
`HomogeneousQuotient.rational_lifts_pseudo_finiteField` then gives an actual
rational point of that same `G` with the required equation under that same
`q`. Ambient smoothness and connectedness, and the target's separatedness
and finite-type hypotheses, are unnecessary for this finite-field step.

`property_of_trivial_split_radical` treats a smooth connected affine group
over an infinite field, with a supplied represented split ground-field radical
whose full subgroup-functor range is bottom. Its three explicit structural
inputs are `PseudoParabolicSplitRadicalProductStatement`,
`TorusGeneratedEnvelopeNormalityStatement` and
`TorusGeneratedEnvelopeRationalDensityStatement`.

The proof first chooses an actual smooth representative `D` of the fixed
closed envelope of all ground-field tori, using
`exists_pointed_torusDominated_envelope`. For each supplied pseudo-parabolic
inclusion, the exact product input and the radical's trivial range give
`DynamicParabolicPresentation.ofSplitProduct`. This identifies the original
inclusion, on every relative scheme test, with the dynamic parabolic of an
actual cocharacter of the original ambient group. The normality and density
inputs apply to this same `D`. The published
`D.rational_lifts_dynamic` now gives an actual lift under the original
projection. No density of the ambient group's rational points is assumed.
No supplied quotient model or projection is replaced in the conclusion.

`statement_of_structural_inputs` invokes the published
`PseudoParabolicSplitRadicalInduction.statement_of_trivial_split_radical`.
The first three inputs are the represented split-radical existence statement,
the normal affine group-quotient statement and the split-unipotent
affine-torsor statement. Together with the exact pseudo-parabolic descent
input, these construct a quotient with an actual scheme section and transfer
the lifting property along a strict decrease of actual Lie dimension whenever
the radical has nontrivial full range. In the remaining trivial-radical case,
the proof divides fields into finite and infinite fields. The finite branch
uses `property_of_finite` with no structural input; the infinite branch uses
`property_of_trivial_split_radical`.

Thus the seven explicit inputs are split-radical existence, normal quotient
existence, split-unipotent affine-torsor triviality, exact split-radical
product replacement, exact pseudo-parabolic descent, fixed-envelope normality
and infinite-field fixed-envelope rational density. The existing induction
does not assume that the radical of its quotient is trivial. All full-range
equalities and fiber equivalences retain arbitrary nonaffine and nonreduced
relative test schemes. The unchanged target still concludes an actual lift
of every rational point of every supplied quotient under its original `q`.

`liftOfStructuralInputs` chooses an actual rational group point from this
existence theorem. Its returned subtype includes the exact equation under the
original supplied projection. It takes the same seven structural propositions;
the chosen point is not assumed, and no canonical choice or scheme section is
claimed.

The provenance is internal: the module composes the imported published
finite-field lifting proof, exact dynamic-presentation construction, actual
smooth torus-envelope construction, dynamic lifting proof and split-radical
dimension induction. It asserts no new result from the literature, no proof
of the seven structural inputs and no unconditional proof of the host target.
