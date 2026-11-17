# Unique conjugacy indices for a complete standard family

This internal lemma assumes a connected reductive group over any field, a
maximal split torus, a generic cocharacter, and a supplied family of standard
cocharacters indexed by an equivalence with all subsets of its simple roots.
It also assumes subgroup schemes whose ranges represent those dynamic
parabolics. For every rational parabolic subgroup, it proves the existence and
uniqueness of a family index to which the subgroup is rationally conjugate.
The equality is between subgroup functors on all scheme tests.

The proof uses `parabolicDynamic` to realize the given parabolic as a dynamic
one. The published `standardParabolicClassification` then supplies its unique
simple-root subset. The published `standardCocharacter` identifies each family
member with the corresponding standard subgroup functor. The supplied indexing
equivalence transfers uniqueness to the family. Finally, `range_comp_iso` and
`eq_comap_iso_iff` convert the classification's inverse-image equality to the
range of the subgroup inclusion followed by the inner automorphism. These are
derived uses of published structure results; the lemma constructs neither a
uniform family over a base nor a parabolic moduli scheme.

`standardFamilyConjugacyIndex` chooses the unique index furnished by this
lemma. Its `spec` theorem proves the stated conjugacy for the selected index,
and its `unique` theorem identifies every other index with that property with
the chosen one. Thus the construction records a rational parabolic's class in
the supplied family, with a specification independent of the chosen conjugating
element.
