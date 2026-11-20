# Irreducibility descends to consecutive real blocks

`realStandardIrreducibilityInStages` proves that if the real standard module of `pre ++ ds ++ post` is irreducible and the full block list has rank `n`, then the standard module of `ds` is irreducible in rank `realRank ds`.

For a stable subspace of the middle module, take the full vectors whose compact slices all belong to that subspace. The compact action translates the slice parameter. To check stability under the Lie action, average a linear projection to the middle subspace over the middle compact group. Inducing this averaged map gives a projection onto the space of full vectors with the required slices. The middle Lie commutation defect takes values in the middle subspace, and the derivative formula for induced maps puts every slice of the full defect in that same subspace. Stability under the complexified Lie algebra follows by linearity.

The slice at the identity is surjective. It detects both alternatives forced by irreducibility of the full module. If the full subspace vanishes, a prescribed middle vector in the invariant subspace lifts by applying the induced projection to any preimage under the slice, so that middle vector vanishes. If the full subspace is the whole module, every middle vector belongs to the middle subspace. The Library's nonvanishing of the actual real standard module supplies nontriviality.

This is the ordinary parabolic induction argument on the Library's actual scalar-valued standard function models. The compact realization of ordinary induction is described by Vogan (1986), Proposition 10.5(a), p. 476 (PDF p. 28). The Lean proof uses the Library's slice, averaging and derivative formulas directly.
