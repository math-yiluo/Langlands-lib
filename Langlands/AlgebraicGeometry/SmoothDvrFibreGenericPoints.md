# Finite fibre generic points of smooth DVR schemes

For a smooth quasi-compact scheme `p : X ⟶ Spec R` over an arbitrary DVR
`R : Type u`, `smoothDvrFibreGenericPoints R X p` is an actual `Finset X`
containing exactly the images of generic points of components of the two
scheme-theoretic fibres. It has no separatedness or group assumption.

This supplies the finite set and the codimension bound for applying
Bosch–Lütkebohmert–Raynaud, *Néron Models*, §6.4 Lemma 4 and the paragraph
following it, printed p.155 (PDF p.162; registered source
`bosch-lutkebohmert-raynaud-1990-neron-models`). This is a derived
construction; common affine neighbourhood existence remains separate.

The internal `point_eq_generic_or_closed` and `finite_base` lemmas show
that a DVR spectrum has just its generic and closed points. The finite-set
constructor applies `finite_fibreGenericPoints`, whose hypotheses follow
from smoothness and quasi-compactness.

`noProperGenerization_in_fibre` uses the topological embedding of a
scheme fibre to reflect specialization and the minimality of a component
generic point among its generizations.

`ringKrullDim_stalk_le_one` proves the dimension bound for every member
of the corresponding set. A generic-fibre component generic point has no
proper generization anywhere in `X`, since its image is the generic point
of `Spec R`. Smoothness over a DVR gives domain stalks, hence reducedness.
The stalk at a generic point of a reduced scheme is a field, so its
dimension is zero. For a special-fibre component generic point, the
published theorem
`Smooth.isDiscreteValuationRing_stalk_of_forall_specializes` proves that
its stalk is a DVR. Its dimension is at most one.

`mem_smoothDvrFibreGenericPoints` identifies finset membership with
membership in `fibreGenericPoints p`.
`smoothDvrFibreGenericPoints_dim_le_one` transfers the dimension bound to
the finset.
`fibreGenerizationDense_of_smoothDvrFibreGenericPoints_subset` shows that
any subset containing this finset contains a same-fibre generization of
every point of `X`. In particular this will apply to a common affine
neighbourhood of the finset. Empty schemes and empty fibres are allowed.
All declarations are polymorphic in the common universe `u`.

The DVR two-point-spectrum lemma is reused from `SmoothDvrAffineOpenGeometry`.
