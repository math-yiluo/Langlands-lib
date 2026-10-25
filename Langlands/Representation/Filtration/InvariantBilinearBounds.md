# Bilinear length bounds along actual filtrations

This internal algebraic adapter iterates the subrepresentation-plus-quotient
bound from `InvariantBilinear` along actual finite `ObjectRepFiltration` chains.
It uses an arbitrary coefficient field and monoid, with independent universes
for the two representation carriers. Neither smoothness nor irreducibility is
required. Repeated steps and zero graded factors are allowed.

The step bound identifies the pulled-back lower subrepresentation in the upper
step with the original lower step by the explicit map that forgets one subtype
wrapper. The quotient is exactly the published graded representation. Induction
on the number of steps, starting with the zero subrepresentation and ending at
the full one, proves `length_le_sum_left`. The flip equivalence gives
`length_le_sum_right`.

`gradedLengthSum` is the extended-natural double sum of the lengths of the actual
bilinear-form spaces on every pair of graded factors. Applying the first bound
and then the second one termwise proves `length_le_gradedLengthSum`. When every
pair except a supplied pair has zero length, two finite-sum reductions prove
`length_le_of_single_pair`. Multiplicities are retained through the position
indices of the two supplied filtrations.

`exists_smul_eq_of_length_le_one` derives scalar proportionality from total
length at most one and a nonzero form. A nonzero element excludes length zero;
therefore length is one. Mathlib identifies a module of length one as simple,
and a nonzero vector in a simple module spans the whole module. Membership in
that singleton span supplies the scalar. The final theorem combines this with
the single-pair bound and a length-at-most-one hypothesis on that pair.

The provenance is internal linear algebra and finite induction over the existing
filtration definitions. The module does not construct finite filtrations, prove
vanishing of irreducible pairings, or prove the parent JPSS uniqueness theorem.
