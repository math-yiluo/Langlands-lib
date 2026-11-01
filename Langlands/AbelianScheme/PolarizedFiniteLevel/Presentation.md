# Independence of auxiliary dual presentations

This internal transport module compares the auxiliary inverse Poincaré bundles
and evaluations in the actual dual construction. Its provenance is the existing
`IsPolarization` definition and the actual contravariant dual maps, together with
the ordinary isomorphism-class definition in `Data`.

`ParameterPolarization` merely reexpresses the existing polarization predicate
on its actual morphism to the dual parameter scheme. `isPolarization_parameter`
is definitional. Consequently two auxiliary evaluations with the same actual
underlying scheme morphism give the same polarization predicate:
`isPolarization_iff`. This does not assert existence of any relative dual or
polarization.

`changeMap` composes an actual map to the dual with the comparison obtained
by dualizing the identity of the original abelian scheme. Its parameter map
is unchanged, because that dual map is the identity on the constructed parameter
scheme. `Datum.withDualWitness` uses this map to replace the auxiliary witnesses
of a supplied datum. The reexpressed polarization predicate proves that it is
still a polarization, and equality of parameter maps proves preservation of the
native degree. The abelian scheme, dimension and ordered full level are retained.

`withDualWitnessIso` is the identity on the original abelian scheme. Its
polarization equation follows from contravariance and the identity law for the
two comparison maps. It preserves every ordered section. Therefore
`withDualWitness_classOf` proves equality in the actual quotient: these auxiliary
choices do not create extra moduli.

`parameterMap_injective` and `PolarizedIso.ofParameterMap` provide a faithful
bridge from equations of actual parameter maps to the actual homomorphism
equations used in this quotient. The latter retains precisely the prescribed
polarization equation and the ordered-section condition.
