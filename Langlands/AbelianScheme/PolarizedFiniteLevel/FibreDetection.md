# Detection of finite-level maps by the ordered sections

This is internal support for eventual representability of the existing ordinary
polarized full-level functor. It is derived directly from the published
`FullLevel` and `Datum` definitions and Mathlib's basis extensionality. It does
not introduce a separate notion of level structure or invoke a geometric
rigidity theorem from the literature.

`levelHomLinear f T n` is the already defined map `GroupScheme.Tate.levelMap`
for the actual abelian-scheme homomorphism `f`, equipped with its canonical
`ZMod n`-linearity using `AddMonoidHom.toZModLinearMap`. It uses the same actual
torsion points and postcomposition formula for every test scheme `T`.

`FullLevel.fibreLevelMap_ext` says that two actual homomorphisms which agree
on every ordered global section induce equal linear maps on the actual torsion
module at every algebraically closed field-valued point of the base. Restriction
of sections commutes with the homomorphisms by `fibreTuple_map`; hence they
agree on the basis `FullLevel.fibreBasis`. Basis extensionality proves equality.
The result works in any fixed scheme universe and imposes no positivity,
invertibility, connectedness or reducedness hypothesis.

`PolarizedIso.mapTuple_eq` restates the existing section condition as equality
of actual tuples. `PolarizedIso.fibreTuple_eq` restricts it to any field-valued
point. Basis extensionality then proves `PolarizedIso.fibreLevelIso_eq`: any
two polarized isomorphisms between the same two data act identically on each
geometric torsion fibre. Its automorphism specialization
`PolarizedIso.fibreLevelIso_eq_refl` identifies that action with the identity
linear equivalence.

These conclusions concern the action on the specified finite torsion fibres.
They neither identify the underlying abelian-scheme homomorphisms nor prove
equality of global torsion-scheme morphisms. They supply no finite-level
existence, automorphism rigidity, moduli scheme, or representability assertion.
The polarization and degree witnesses are retained in the datum and are not
used by these fibrewise arguments.
