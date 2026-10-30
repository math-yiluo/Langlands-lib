# Continuous positive characters on compact subgroups

`Langlands.RankinSelberg.LastRowReduction.eq_one_of_isCompact` says that a
continuous group homomorphism to `ℝ≥0ˣ` is one on every compact subgroup.
No topological-group instance on the source is required.

The declaration and proof were moved unchanged from
`Representation/RankinSelberg/EqualRankLastRowReductionProof`. The historical
namespace is retained for existing users. The real-valued image of the compact
subgroup is bounded above. Powers rule out values greater than one, and applying
the same argument to inverses rules out values less than one.

Both the last-row reduction and the normalized exponent family import this
shared proof.
