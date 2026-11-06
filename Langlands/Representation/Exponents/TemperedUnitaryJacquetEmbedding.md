# Induction embedding from a unitary Jacquet quotient

This derived supporting construction isolates the Frobenius-reciprocity step
in Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026,
VII.2.6, printed p.231 / PDF p.237. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The implementation uses the actual published normalized Jacquet and induction
functors and the actual rational-point topology of the chosen Levi.

The field universe `u` and representation-carrier universe `v` remain
independent. The original representation and its chosen irreducible Levi
quotient have carriers in `v`, while normalized induction has its prescribed
carrier in `max u v`. The supplied maps `p`, `l` and `r` are the actual
parabolic, rational Levi and matching geometric unipotent radical, with
their multiplication isomorphism and split component.

The map-level helpers expose an affine structure instance for the Levi's
canonical point topology. This follows from the supplied rational Levi
witness; the final existence corollary derives it internally and needs
no separate affine premise.

For any `UnitaryJacquetIrreducibleQuotientData`, the definition
`unitaryJacquetQuotientFullMap` composes the existing
`leviUnitaryJacquetRetraction` with the stored quotient map. The retraction
identity proves that restricting this full map to the literal unitary
inclusion gives the stored map. Every vector in the irreducible quotient
therefore has a preimage in the full normalized Jacquet module.

`unitaryJacquetQuotientImageMap` keeps this surjective linear map and
transports its intertwining equation along the inverse of `leviPointsEquiv`.
The identity `e (e.symm m) = m` identifies its source with the actual Jacquet
action on the literal Levi image. `unitaryJacquetQuotientInductionMap`
applies the inverse of the existing `General.FirstAdjointness.equiv` to
this intertwiner. Its target is exactly the prescribed
`leviInductionFunctor` of the same stored quotient.

If the ambient representation is irreducible, an intertwiner from it is
injective or zero. If this adjoint were zero, applying first adjointness
would make the full Jacquet quotient map zero. That contradicts its
surjectivity and nontriviality of the irreducible quotient. This proves
`unitaryJacquetQuotientInductionMap_injective`.

The corollary
`exists_irreducible_induction_embedding_of_unitaryJacquetPart` applies
`unitaryJacquetIrreducibleQuotient` to select the data from quotient
compactness, ambient irreducibility, complementarity and nontriviality
of the actual unitary part. It returns an irreducible smooth representation
of the Levi and an injective intertwiner into its actual normalized
induction. It retains the supplied radical unimodularity witness.

Complementarity of the actual unitary and nonunitary Jacquet parts and
`IsUnimodularModulus` of the literal radical are explicit inputs. Quotient
compactness is needed by the separate quotient-selection construction,
and is retained by the final existence corollary; it is unnecessary for
the map-level adapter once the data are supplied. This pair proves no
minimality assertion, quotient temperedness, square-integrability,
uniqueness or unitarizability. It leaves the three unconditional VII.2.6
propositions open.
