# Explicit coinduction from a stage of finite degree

`D.cj k` is conjugation of inertia by `lift ^ k`. The lemmas `coe_cj`, `cj_zero`,
`cj_conj`, `cj_add` and `continuous_cj` record its basic properties.

A `Stage D E f` relates a split group `(G, D)` to another split group `(H, E)` by:

- an injective continuous homomorphism `ι : H → G` with
  `deg_D (ι h) = f · deg_E h` and `ι (E.lift) = D.lift ^ f`;
- a continuous homomorphism `κ` from `D`-inertia to `H` with `ι (κ n) = n`.

For the local Weil group of `K` and an unramified extension of degree `f`, `ι` is the
inclusion of Weil groups and `κ` identifies the two inertia groups. Only these axioms
are used here.

For a stage of degree `m + 1` and a representation `τ` of `H` on `V`, the carrier
of the coinduction is `Fin (m + 1) → V`:

- `block τ k` is the inertia representation `n ↦ τ(κ(lift^k n lift^{-k}))`.
- `inertiaRep τ` is the block-diagonal representation `blockRep` with these blocks.
- `cycUnit E m τ` is the invertible operator `v ↦ (k ↦ v(k+1))` for `k < m`, with
  last coordinate `τ(E.lift)(v 0)`. This is `cyclicEquiv`, a rotation of
  coordinates twisted by `τ(E.lift)` at the last coordinate.

`κ_conj_lift` derives `κ(lift^{m+1} n lift^{-(m+1)}) · E.lift = E.lift · κ(n)` from
injectivity of `ι`. With it, `inertiaRep_conj_mul` and `compatible` verify the
hypothesis of `SplitDegree.extend` for `inertiaRep τ` and `cycUnit E m τ`.
`Stage.coind τ := D.extend (inertiaRep τ) (cycUnit E m τ) _` is the coinduced
representation. `coind_inertia` and `coind_lift` give its values on inertia and at the
lift.

This is an explicit model of the representation induced from the unramified stage,
used in the proof of Henniart (1988), Proposition 2.2. It is internal
infrastructure; no identification with an abstract induction functor is claimed.
