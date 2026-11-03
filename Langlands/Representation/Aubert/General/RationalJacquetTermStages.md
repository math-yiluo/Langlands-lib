# Collapsing the source of rational standard geometric terms

This internal adapter defines `rationalRestrictedJacquetTerm` using actual
normalized Jacquet restriction inside a source coarse Levi, actual
inverse-conjugation pullback between fine ambient Levis, and actual normalized
induction inside a target coarse Levi. Source and target finite subsets and
their fine subtype indices are arbitrary. Actual fine-Levi conjugation
membership is explicit.

`rationalRestrictedJacquetTerm_eq_standard` identifies these wrappers with
the full `standardIntersectionTermK0`. This is a definitional equality:
the canonical `subgroupOfContinuousEquiv` pullbacks, normalized functors,
and preservation witnesses are precisely those in that standard term.

Over a nonarchimedean local field,
`rationalRestrictedJacquetTerm_comp_ambient` shows that composing this
restricted term with ambient Jacquet restriction to its source coarse
Levi gives `standardConjugatedJacquetTerm`. The proof applies
`standardLeviJacquetK0_comp_ambient` at the source fine index. The needed
positive Haar-character product equality is proved by
`standardJacquetModulus_stages` from continuity of the actual standard
projections. Thus no modulus equation or representation comparison is
assumed here. A private elementary associativity lemma inserts this
Jacquet restriction in stages into the complete term.

The field and representation universes are independent; carriers lie in
`max (u + 1) v`. Rational points have their actual point topology and are
locally compact and nonarchimedean. The connected reductive group,
maximal split torus, generic cocharacter, standard-cocharacter and
Levi-intersection statements are explicit. Closed ambient standard Levis
and radicals and the ambient and literal restricted finite-length and
short-exact preservation data are retained. The stages comparison also
retains continuity of the standard projections and compact-limit
decomposition of each restricted radical.

Provenance is internal, through the actual standard wrappers, generic
intersection term, normalized Jacquet stages and rational Haar-factorization
modules. The argument uses the full exact finite-length Grothendieck groups.
It does not prove actual geometric intersection identities, geometric
expansion or the complete rational Aubert Jacquet compatibility.
