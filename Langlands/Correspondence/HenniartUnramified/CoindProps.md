# Frobenius reciprocity, twists, kernels and continuity of the coinduction

Let `S` be a stage of degree `m + 1`, `τ` a representation of `H` on `V`, and
`S.coind τ` the explicit coinduction on `Fin (m + 1) → V`.

- `recip D m ρ' P` sends `v` to `k ↦ P(ρ'(lift^k) v)`. It is nonzero when `P` is
  nonzero (`recip_ne_zero`, from the coordinate `k = 0`).
- `recip_intertwines` (Frobenius reciprocity): if `P ∘ ρ'(ι h) = τ(h) ∘ P` for all `h`,
  then `recip D m ρ' P` intertwines `ρ'` with the coinduction. It is checked on
  inertia, using `lift^k n = ι(κ(lift^k n lift^{-k})) lift^k`. It is checked at the
  lift coordinate by coordinate, using `ι(E.lift) = lift^{m+1}` at the last
  coordinate. `intertwines_of_inertia_and_lift` then gives all of `G`.
- `diagPow u` is the diagonal operator with entries `u^k`.
  `twist_equiv_of_pow_eq_one` shows that when `u^{m+1} = 1` it is an equivalence from
  the twist of the coinduction by `u^deg` to the coinduction. At the last coordinate
  the factor `u · u^m = 1` is used.
- `coind_trivial_iff`: for a normal subgroup `N` of `G`, the coinduction is trivial on
  the inertia elements of `N` exactly when the first block `τ ∘ κ` is. The blocks are
  conjugates of the first one, and conjugation preserves `N`.
- `continuous_coind`: if `G` is a topological group and `V` is finite-dimensional over
  `ℂ`, a continuous `τ` gives a continuous coinduction. The blocks are
  continuous, so the block-diagonal inertia action is continuous, and
  `continuous_extend` applies.

These are the properties of the induced representation used in the proof of
Henniart (1988), Proposition 2.2. They are internal lemmas for that proof.
