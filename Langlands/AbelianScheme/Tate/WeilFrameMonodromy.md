# Geometric monodromy on actual Weil-compatible adelic frames

This module constructs the geometric action on the actual restricted full
frame space and its fixed right orbits. It depends explicitly on
`RationalWeilGeometricTransportStatement`; the module does not prove that
proposition. The construction follows the frame and invariant-orbit portion
of Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, p.91, and Kottwitz, *Points on some Shimura
varieties over finite fields* (1992), Section 5, pp.390–391.

`weilFiniteAdeleTwistedMonodromyRepresentation` pairs the actual
tensor-algebra-linear Tate monodromy with the actual section-ring
Tate-twist monodromy. It takes values in `PEL.twistedSimilitudes` of the
actual `adelicWeilAlongHomBilinearMap`. The preservation equation follows
by applying the displayed geometric compatibility proposition to a loop.
Thus both inputs and the value module act together. The representation
laws come from the two existing monodromy representations. This
construction is available for every selection of positive torsion orders
whose invertibility and root finite étaleness are retained explicitly.

`weilAdelicFrameMonodromyAction` specializes to all positive orders and
postcomposes the previously constructed `WeilAdelicFrame` by that
representation. Its existential twist trivialization is postcomposed with
the actual twist monodromy. The left action therefore retains the
nontrivial root action and makes no choice of roots or basis.

`weilAdelicFrameActionsComm` proves that this geometric left action
commutes with right precomposition by the scalar-extended rational source
similitude group. The proof checks the underlying maps: target
postcomposition and source precomposition commute.

For any subgroup `U` of that source group, `WeilAdelicLevel U` is the set
of right `U`-orbits in the actual Weil-compatible frame space fixed by the
actual geometric fundamental group. This uses the existing
`PEL.InvariantOrbit`, so invariance is a condition on the orbit class; it
does not require a fixed representative. The subgroup construction also
applies when `U` is compact open, once a topology and that hypothesis are
supplied in the intended PEL specialization.

All dual/Poincaré and scalar comparison inputs remain those of
`WeilAdelicFrame`. The rational source form and dual-valued homomorphism
retain the generality documented there: finite-dimensionality,
faithfulness, involution compatibility, alternation, nondegeneracy and the
polarization predicate are separate PEL assumptions. No nonemptiness,
compact-openness theorem, path existence, canonical change-of-base-point
equivalence or unpointed moduli functor is asserted here. This is a
conditional actual-geometric construction, with a named proposition
dependency rather than an arbitrary pairing or action supplied as data.
