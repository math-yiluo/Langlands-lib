# A maximal torus split by the prescribed cubic field

`trialitarianCubicSplitMaximalTorus` proves
`TrialitarianCubicSplitMaximalTorusStatement.{u}`. For the anisotropic
simply connected trialitarian group in that statement, a split maximal
torus over the prescribed cubic Galois extension gives a maximal torus
over the base that splits over the same extension.

First the proof chooses a split pinning on the supplied torus over the
cubic field. Galois comparison with the absolute pinning identifies
the root data and gives the rational parabolic transports. It also
shows that the star action factors through the cubic Galois group.
The no-fixed-leaf condition then yields a generator and a lift
cycling the three leaf types. The first application of triple
parabolic descent obtains a closed connected reductive subgroup over
the base whose scalar extension is a rational conjugate of the
common Levi of the three leaf parabolics.

The conjugate of the original split maximal torus factors through this
Levi over the cubic field. The centralizer root calculation identifies
its coroots using the `A₂` subsystem of the common zero roots. Comparing
the Levi pinning over the separable closure to its split torus over
the cubic field allows a second application of triple parabolic
descent, now with three `A₂` line cocharacters. This gives a torus over
the base whose scalar extension is conjugate to the split maximal
torus of the Levi. The composite with the Levi inclusion becomes a
conjugate of the original maximal torus of the ambient group after
scalar extension. Maximal-torus reflection and the isomorphism over
the cubic field give the two desired properties.

Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994),
§6.8, printed pp. 371–372, construct the prescribed torus in the common
Levi of three leaf parabolics. The proof here constructs the torus
inside that Levi by descent of a second intersection, using a regular
cocharacter difference.
