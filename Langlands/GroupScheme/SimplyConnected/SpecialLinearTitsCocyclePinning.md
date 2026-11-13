# Coordinate pinned presentations of simply connected groups of type A

This internal construction retains the coordinate data needed for the
special-linear Tits cocycle theorem. It combines the coordinate root datum of
`SpecialLinear.FinSucc.exists_coordinateRootDatum`, the integral coroot criterion
`splitSimplyConnectedCorootSpan`, the Cartan extension
`corootSpanCartanEquiv`, and the actual pinned lifting theorem
`pinnedIsomorphism`. It asserts no Galois discrepancy formula.

`coordinatePinning` uses the fixed determinant-one diagonal torus indexed by
`ULift (Fin n)` and its actual inclusion into `SL_(n+1)`. Its input is an actual
finite reduced root datum for that inclusion and a base. Simple-root Lie
trivializations are supplied by `RootPinning.ofSplitMaximalTorus`.

`CoordinatePinnedIso q eG` retains that source root datum, its base and numbering,
the adjacent-coordinate root formulas, and an actual pinned isomorphism to `q`.
The isomorphism's index map extends the prescribed target numbering `eG`.
`CoordinatePinnedIso.simpleRoot_pullback` states the resulting character formula:
the pullback along its torus isomorphism of target simple root `eG.symm i` is
`rootChar n k i.castSucc i.succ`.

`exists_coordinatePinnedIso` constructs these data for any simply connected
split group with a supplied pinning whose numbered simple pairings are the
Cartan matrix `A_n`. The proof obtains the coordinate root datum of `SL_(n+1)`.
The source coroots span by its construction; the target coroots span by simple
connectedness. The given numbering identifies their Cartan matrices, so the
Cartan extension theorem supplies a full root-datum equivalence extending that
numbering. Surjectivity of the numbering proves that the equivalence preserves
both simple supports. The pinned lifting theorem then supplies the actual group
and torus isomorphisms. Applying inverse character transport to its root equation
gives the displayed pullback formula.

This is a derived composition of the named Library interfaces, with no new
external mathematical input. The coordinate root-datum and Cartan-extension
implementations are due to Worker 235 and Worker 237 respectively. Arbitrary
fields, arbitrary characteristic, and all natural numbers `n`, including zero
and one, are retained.
