# Decomposition in the bounded norm source

For a torus over the maximal unramified field \(K\), choose a finite
Galois splitting field and split coordinates. The Weil restriction
in those coordinates is induced by `InducedEmbedding.permTorus_isInduced`.
Its smooth integral model is `ConnectedImage.model`.
`ConnectedImage.map_model_integralPoints` identifies the image of its
integral points under `ConnectedImage.normMap` with the norm-defined
depth-zero group. `localTorusFiltration_zero` and
`connectedNeronModel_integralPoints` identify this with the connected
Néron integral points.

`exists_induced_normCover_decomposed` also describes each integral
section of this norm source. `WeilGm.sectionUnitsEquiv` gives the
coefficient units, and `exists_principal_and_torsion` factors each
coordinate into a principal unit and a torsion unit. The product of
the coordinate exponents is a common exponent and is a unit in the
separable valuation ring. There is a common depth \(0<r<1\) below the
finitely many positive valuations of the principal coordinate
differences from one. `WeilGm.rationalUnitsEquiv_integralPointMap`
and `ConnectedImage.piTensorEquiv_tmul` carry these values to the
generic coordinates.
`InducedTorusShallow.mem_geometricCharacterCongruence_iff` puts the
generic point of the principal part in the geometric character
subgroup at this depth.

The bounded norm source is the one in Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), Definition 2.5.13 and the proof of
Corollary B.8.7, printed pp. 90 and 683, PDF pp. 121 and 714. Its unit
decomposition follows from `GeometricPrincipalUnits` and the induced
torus coordinate test.
