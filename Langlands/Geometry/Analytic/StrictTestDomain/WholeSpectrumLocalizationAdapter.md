# Ordinary-localization adapter for whole-spectrum descent

This conditional assembly lemma assumes that every actual rational quotient
is a localization of the base at its denominator, for the base algebra structure
induced by the actual structural map. The final lemma
`existsUnique_whole_gluing_of_trivial_scalar_norm` discharges this premise when
`∀ c : K, ‖c‖ ≤ 1`, using the published
`trivialScalarRationalLocalization` theorem from
`TrivialScalarRationalLocalizationProof`. The unconditional whole-spectrum
gluing statement is proved separately in
[`WholeSpectrumRationalGluingProof.md`](WholeSpectrumRationalGluingProof.md).

The point cover implies that the denominators generate the unit ideal, by the
preparation module's spectrum ideal argument. Choose one covering member for
each distinct denominator and identify its actual quotient with Mathlib's
canonical ordinary localization. Localization extensionality identifies the
actual overlap restrictions with the canonical maps to the localization at the
product. Mathlib's `Localization.existsUnique_algebraMap_eq_of_span_eq_top`
then supplies a unique base element for the chosen members.

For any unchosen member, its denominator equals that of its chosen
representative. The localization property gives a ring map back from their
intersection to that member. This map is a left inverse to the first restriction,
and compatibility carries the representative's base section to the desired
section. Uniqueness follows from the canonical localization theorem.

This is an internal algebraic adapter, derived from the named Mathlib theorem
and the actual rational quotient maps. It needs neither a finite covering index
nor a nonzero base. The repeated-denominator argument is essential: selecting
one index per denominator alone would not justify descent for every member.

The final lemma applies the generic adapter to
`trivialScalarRationalLocalization K P hK`. That theorem uses exactly the
structural-map algebra instance required by the adapter. No localization or
analytic descent premise remains in this scalar-bound lemma. It preserves empty
covering types, empty rational loci, empty numerator tuples and zero and
nonreduced bases. Its scope is scalar degree-zero descent for unit-radius
rational quotients of presented strict bases under the scalar norm bound. It
does not assert higher Cech exactness, admissibility, arbitrary radii or relative
rational-target gluing.

Worker 146 authored this adapter. Worker 228 authored the imported localization
proof, which is used by its published Lean name. The literature provenance of
that comparison is documented in
[`TrivialScalarRationalLocalizationProof.md`](TrivialScalarRationalLocalizationProof.md);
the subsequent gluing argument here uses ordinary algebraic localization.
