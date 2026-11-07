# Actual integral lifts outside a finite set of global places

These derived constructions combine the residue-point, Henselian-lifting
and arithmetic-cardinality steps in Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Theorem 4.5, printed
p.12, third proof paragraph, and p.13, last paragraph. The full uniform
Lang–Weil estimate remains an explicit premise `hLW`.

`curvePlaceAlmostAllIntegralPointLifts` applies to every function field
`F` over a finite constant field `k`, using all actual discrete curve
places and their native completed valuation rings.
`numberFieldAlmostAllIntegralPointLifts` applies to every number field
`K`, using all its finite places and their native completed integer rings.
All fields, coefficients and schemes range over an arbitrary common
universe. Neither constructor replaces the local rings by an abstract
place system.

In both cases `C` is an arbitrary commutative coefficient ring, `B` and
`Y` are actual schemes over `Spec C`, and `f : Y ⟶ B` is their actual
relative morphism. The assumptions are precisely those of the reused
uniform Henselian construction: `B` is quasi-compact and locally of
finite type over the integers, and `f` is smooth, separated, surjective,
locally of finite type, quasi-compact and geometrically connected, with
every actual fibre of the supplied common pure dimension `d`. The total
schemes need not be affine or separated over the integers.

Each constructor returns a finite set `S` before quantifying over the
place, coefficient algebra and prescribed integral point. For every
place outside `S`, every supplied `C`-algebra structure on its native
completed integer ring and every actual relative point `p` of `B`, it
constructs an actual relative point `a` of `Y` with the exact equality
`a ≫ f = p`. Consequently the induced integral-point map is surjective
at every such place. The bound is independent of the coefficient map and
of the point. A coefficient map is requested only at the place in use;
there is no requirement that a ring of S-integers map to the integer
rings at its excluded places. One may enlarge the returned exceptional
set by any prescribed finite set and retain all the lifts.

The implemented proof first chooses the positive constant supplied by
`uniformLangWeilLargeHenselianRingPointLifts`. It then takes the exact
finite set of places whose completed residue cardinality is at most the
square of that constant, using `CompletionResidueBounds`. Outside that
set the required strict lower bound is proved. The native completion
integer rings are Henselian by `CompletionIntegersSmoothPointLifting`;
finiteness of their actual residue fields is proved by the published
arithmetic residue-field results. Applying the uniform Henselian
constructor to the canonical residue quotient and the original integral
point gives the selected exact lift. No local lifting or residue-growth
assertion is assumed separately.

This unit does not prove the uniform Lang–Weil estimate. It also does
not construct compatible integral spreads of a given generic-fibre
morphism, reduce varying fibre dimensions to the pure-dimensional case,
prove local openness, or glue local maps into adelic openness. Those
remain obligations for Theorem 4.5 and the whole-paper task. The base's
finite-type-over-integers hypothesis is explicit here; its verification
for a chosen spread is a separate application step.
