# Normal sublevels for ordinary normalized Harris CM representability

This is an internal adapter for `DivisionCMNormalSublevelRepresentabilityStatement`.
It links `HarrisTaylorCMDivisionQuasiProjectiveDecomposition` to the actual-isomorphism
presheaf of `HarrisTaylorCMOrdinaryPresheaf`. It does not define a new moduli problem.

## Open subgroups in Hodge coordinates

`exists_smallCMNormalSublevel_le_hodgeOpenSubgroup` starts with an actual small
level `U` and an open subgroup `K` of the Hodge scalar-extension similitude
group on the finite adeles. It produces a small level `V ≤ U`, normal as a
subgroup of `U`, whose image under `hodgeLevelFunctor` is contained in `K`.
The proof pulls `K` back along the published continuous multiplicative
equivalence. `CompactOpenLevel.normalCoreIn` gives a compact open subgroup of
that pullback, contained and normal in `U`. Smallness passes to it by
`LevelSufficientlySmall.mono`. Finally, the membership formula for
`hodgeLevelFunctor` transports the inclusion back to Hodge coordinates.
This part does not assume division.

## Ordinary quasi-projective representation data

At a small level `U` whose Hodge transport stabilizes the actual integral
source lattice, `CMOrdinaryQuasiProjectiveRepresentation` is an `F`-scheme
with an immersion into a finite projective space over `F`, together with a
natural isomorphism from its restricted functor of points to
`tateNormalizedCMOrdinaryDisconnectedPresheaf` on the full componentwise
admissible test category. It uses the `PolarizedFiniteLevel.Prerequisites`
package and the separate duality naturality, Weil transition, rational
profinite-integer adele comparison and torsion finite étale inputs.

`CMOrdinaryQuasiProjectiveRepresentation.toQuasiProjective` leaves the scheme,
immersion and structure map unchanged. It composes the natural isomorphism
with `tateNormalizedCMOrdinaryDisconnectedIso` at that same level. The
comparison uses the Library theorems `properFibreAmpleAffineOpen` and
`Tate.commensurableInvariantLatticeRealization` to identify the ordinary
actual-isomorphism classes with the original rational-isogeny classes.

## Conditional application

`divisionCMNormalSublevelRepresentabilityStatement_of_ordinary` takes one
open subgroup `K` in Hodge coordinates and an existence hypothesis: in the
division case, every small level transported into `K` and stabilizing the
source lattice has ordinary quasi-projective representation data. For each
original small level, the proof chooses a normal sublevel using the intersection
of `K` with `harrisIntegralAdeleOpenStabilizer`. It applies the existence
hypothesis at this sublevel and transports the witness using
`CMOrdinaryQuasiProjectiveRepresentation.toQuasiProjective`. The conclusion
is the published normal-sublevel statement with the tensor, Picard and
polarization inputs taken from the given package.

The ordinary existence hypothesis remains to be proved. The module also
supplies no descent to the original level, smoothness, properness, or final
division-case representability proof.
