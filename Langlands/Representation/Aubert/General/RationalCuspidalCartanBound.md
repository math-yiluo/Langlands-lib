# Coefficient pairing bounds on the actual rational Cartan cover

This internal specialization supports Renard VI.2.1 (a) implies (c), using the
finite-relation calculation and root-gap argument on printed p.139 / PDF p.145
of the 2026 edition. It does not yet assert compact support.

`dominantUniformizerCartanSet` is the set of literal translates `e(x) f`, where
`e` is the existing actual uniformizer section mapped into the group, `f` lies in
a specified finite centralizer subset, and the simple-root pairings selected by
the face are nonnegative. Its lattice model uses no auxiliary centralizer
valuation or bijective character evaluation. Its representation field has bound
zero. Membership and centrality of uniformizer powers, centralizer membership in
every Levi, standard cocharacters, and contraction are the published actual
results in `RationalPointFamily` and `RationalCartanLatticeModel`.

`IsCuspidal.mem_jacquet_relations` reads the normalized Jacquet object's actual
quotient carrier. Subsingletonness kills the image of each vector, and
`Jacquet.Localization.relations_one` identifies its kernel with the untwisted
Jacquet relation space. This keeps the actual normalized functor and all proper
standard indices, including the empty-root boundary.

`exists_rational_coefficient_pairing_bound` instantiates the generic finite-wall
bound with this model. The finite simple-root set comes from the existing
relative root-system hypothesis, and `StandardCocharacterStatement` supplies the
standard cocharacters. The actual full Levi is the group by
`RationalPointFamily.levi_univ_eq_top`. A smooth dual functional provides an open
invariance subgroup. No admissibility or irreducibility is assumed; the carrier
universe is independent of the field universe.

`exists_rational_compact_translate_pairing_bound` makes the bound uniform over
both left and right translates in any specified compact set. The smooth source
orbit is finite by `JacquetCartanDatum.finite_image_of_isCompact`. The same theorem
on the smooth part of the dual proves finiteness of the functional orbit. The
maximum of the finitely many individual bounds gives one bound for all these
translated coefficients, using the actual contragredient evaluation convention.

The exact target additionally needs the fixed ambient-character valuation fiber,
joint detection, and the final compact-support assembly. Those are separate
obligations.
