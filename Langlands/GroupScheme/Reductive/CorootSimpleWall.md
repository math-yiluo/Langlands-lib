# A simple-wall cocharacter and its contracted root groups

This internal lattice construction isolates the opposite pair of a simple
root by an integral coordinate cocharacter. It uses the published
height-cocharacter construction and the elementary simple-reflection
properties of a base. It is preparatory work for isolating the rank-one
factor in a cell-translation argument.

Let `P` be a reduced root datum on a finite coordinate lattice, with finite
root index, and let `b` be a base. The pairing is explicitly assumed to be
the coordinate integer dot product, written `coPairing` in `LocalSplitCell`.
For a simple root `a`, the published theorem
`exists_coPairing_eq_height` supplies an integer `d > 0` and an integral
cocharacter `ν` pairing with every root β as `d * b.height β`.

Set `mu = 2ν - d*a∨`. Linearity of the coordinate pairing and the height
formula for a simple reflection give

`coPairing (P.root β) mu = d * (height(β) + height(s_a β))`.

This is zero at `a`. If β is positive and distinct from `a`, then both β
and `s_a β` are positive, so the pairing is strictly positive. Root
negation gives a strictly negative pairing on every negative root except
`-a`. The pairing at `-a` is zero. These sign alternatives prove that its
zero roots are exactly the opposite pair.

`exists_simpleWallCocharacter` gives this existence and the full sign
specification. `simpleWallCocharacter` chooses such an integral vector; the
three accompanying theorems expose its zero, positive and negative tests.
No scheme or base-ring hypothesis is involved in this lattice construction.

The final lemma
`IsRootParametrization.rootPoint_mem_dynamicUnipotent` is separate and
general. It takes an actual root parametrization for an exponent `m` and an
integral cocharacter `ν` with positive coordinate pairing. Over any
commutative ring and on every relative scheme test, the root point lies in
the dynamic unipotent subgroup for the composite cocharacter into the
ambient group. The root-parametrization representation gives membership in
the full root subgroup. The coordinate exponent-composition formula
identifies the root character on `ν` with a positive power, and the
published `RelativeRoot.subgroup_le_dynamicUnipotent_of_power` gives the
claimed contraction. This argument adds no reducedness, field or
reductivity assumption.

The module does not establish the negative-simple cell translation law or
any rank-one Bruhat relation.
