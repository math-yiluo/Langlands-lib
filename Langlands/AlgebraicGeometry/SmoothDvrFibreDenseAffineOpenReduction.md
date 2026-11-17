# Affine-open data from normal common neighbourhoods

Author: Worker 219.

`FibreDenseAffineOpen p` is the type of actual opens `U : X.Opens`
together with `IsAffineOpen U` and the proof that every `x : X` has a
generization `y ∈ U` with `p y = p x`. Its `opens`, `isAffineOpen` and
`exists_generization` accessors provide the open and both required
properties directly.

`smoothDvrFibreDenseAffineOpenOfNormalNeighbourhoods` is a **conditional
constructor** of this data for every smooth quasi-compact separated
scheme over any DVR, in the common universe `u`. Its first argument is
the general proposition
`NormalCodimensionOneAffineNeighbourhoodStatement.{u}`. This file proves
the specialization and the construction from that proposition; it does
not prove the general proposition itself or supply an unconditional DVR
constructor.

The constructor uses `fibreGenericPoints p` as its finite set. The DVR
base has finitely many points, and the morphism is locally of finite
type and quasi-compact, so this set is finite. The published smooth-DVR
stalk theorem supplies integrally closed domain stalks, and
`SmoothDvrFibreGenericPoints.ringKrullDim_stalk_le_one` supplies the
dimension bound at every selected point. Thus all hypotheses of the
general common affine neighbourhood theorem are discharged from the
DVR scheme's given hypotheses.

Classical choice selects an affine open containing this finite set.
`fibreGenericPoints_subset_iff` converts containment into the exact
same-fibre generization property. No connectedness or nonempty-fibre
assumption occurs.

This is derived supporting development for the argument after
Bosch–Lütkebohmert–Raynaud, *Néron Models*, §6.4 Lemma 4, printed p.155
(PDF p.162; registered source
`bosch-lutkebohmert-raynaud-1990-neron-models`). Task 7561 owns the
substantial missing general affine-neighbourhood construction. The
unconditional final DVR constructor remains an obligation of Task 7523.
