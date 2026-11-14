# Finite projective tensor coordinates and actual vector-group retracts

Worker 645.

This internal helper derives an actual vector-group retraction from natural
finite projective tensor coordinates, using the actual vector-group and cocycle
constructions and Mathlib's finite projective module splitting.
It does not define the relative filtration or prove relative Levi existence.

For an arbitrary commutative ring `R`, `TensorCoordinates.Points R M T` is
`Γ(T, O_T) ⊗[R] M`, with the algebra structure on the first factor induced by
the actual map `T -> Spec R`. `pullback` tensors the actual algebra map on
relative global sections with the identity on `M`. `IsNatural e` requires a
supplied family of group isomorphisms from the points of an actual group scheme
to these additive tensor modules to commute with these restriction maps on all
scheme tests.

`moduleMap f T` tensors the identity on global sections with a linear map `f`
of coefficient modules. `pullback_moduleMap` proves that restriction commutes
with this extension. `pointMap e d f T` conjugates this linear map by the two
supplied group-coordinate equivalences. Its naturality follows from this
commutation and the two `IsNatural` hypotheses.

`hom e d he hd f` sends this natural family of point homomorphisms to an actual
group-scheme morphism by the published `homOfPoints`. `hom_coordinates`
identifies its action on all test schemes. `hom_retract` proves that a split
pair of coefficient-module maps gives a split pair of actual group-scheme
maps. The proof uses `hom_ext_points`, the tensor composition law, and the
original module retraction equation.

`free R n` is the standard free tensor model, obtained from the polynomial vector group's
published natural coordinates and `TensorProduct.piScalarRight`. The finite
projective module splitting
`Module.Finite.exists_comp_eq_id_of_projective` then supplies a retraction from
a finite free vector group in `isFiniteVectorGroupRetract`, without choosing a basis of `M`. The bound `n`
is a number of generators; it is not required to equal a constant rank of `M`.
Thus the construction permits non-free modules and varying finite ranks over
disconnected spectra.

`cocycle_isTrivial` applies the resulting actual retraction to the imported
finite-vector cocycle theorem. It treats every affine `T -> Spec R` and every
affine flat surjective `U -> T`, with a cocycle for the actual base change of
`V` to `T`.

`exists_section` applies the corresponding imported torsor-section theorem.
Over every affine test `T`, it assumes an actual action `ModObj V_T.X X`,
invertible `ModObj.leftSMul`, and flat, surjective, quasi-compact structure
map `X -> T`. It produces an actual scheme morphism `s : T -> X` whose
composite with the structure map is the identity. No affine or connectedness
hypothesis is imposed on `X`. Every type and scheme remains in an arbitrary
universe `u`; no field, noetherian or connected-base hypothesis is used.

The provenance is internal: these are tensor-algebra and all-test Yoneda
consequences of imported Library constructions and Mathlib lemmas. A supplied
natural coordinate model is a hypothesis. This file does not construct
such a model from sheaf data or claim a general finite-series induction.
