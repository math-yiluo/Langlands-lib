# Henselian invariance in finite Galois extensions

Author: Worker 1651.

`realValuationDecompositionGroup` is the actual subgroup of field
automorphisms preserving a supplied real valuation.
`realValuation_invariant_of_finiteGalois` proves that every member of a
finite Galois group preserves any normalized prolongation of a
nontrivial Henselian real valuation, with independent arbitrary field
universes.

Consider the subgroup D preserving the prolonged
real valuation. The finite family of distinct conjugate prolongations
has a separator a, small at the original valuation and congruent to one
at every different prolongation. The product b of d(a) over d in D is
D-fixed and small. Every conjugate sigma(b) for sigma outside D has
value one. The small-conjugate descent lemma puts b in the original
field. It is therefore fixed by every automorphism, contradicting the
value-one formula for any sigma outside D. Thus D is the entire finite
Galois group. No completeness premise is used.

This is a derived internal proof route for the exact Henselian discrete
norm theorem. The proof constructs the finite image of conjugate
valuations, obtains its separator from
`exists_normalizedRealProlongation_separator`, and uses the separate
`mem_range_of_small_and_other_conjugates_units` descent lemma. The
product is indexed by the actual decomposition subgroup; left
multiplication permutes its factors, proving fixedness. All alternative
conjugates have valuation one because multiplying an automorphism
outside the subgroup by a subgroup member stays outside. No residue
field, perfectness or characteristic assumption is used. The theorem
is finite in this module; the infinite passage is a separate wrapper.
