# Transport of sigma-lifts along representation equivalences

`SigmaIntertwiner.transport` conjugates the supplied intertwiner by an equivalence of the upstairs actions. The underlying linear map sends \(x\) to \(e(A(e^{-1}(x)))\). The intertwining condition uses the same equivalence evaluated at the entrywise automorphism of each group element.

`twistedDistribution_eq_of_equivalent` conjugates both the integrated action and the twist. The composition is the conjugate of the original finite-rank map, whose trace is invariant under linear equivalences across carrier universes.

`IsSigmaLift.transport` transports the ordinary character on the downstairs group and the twisted character on the upstairs group. It retains the same scalar and the same matching test functions. This checks that an identification with the actual normalized orbit product by a representation equivalence suffices for using the local induction interface.
