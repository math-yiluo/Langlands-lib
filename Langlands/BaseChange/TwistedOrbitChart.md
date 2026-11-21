# Product charts for twisted conjugation

This internal lemma assembles a chart for the regular transfer argument.
Let `G` be a topological group with a continuous endomorphism `θ`, and
let `p` be a continuous map from `G` to a topological parameter space `B`
that is invariant under `θ`-twisted conjugation. Let `s : V → G` be a
continuous section of `p` over a subset `V` of `B`. The chart uses the
subspace topologies on `V` and `p ⁻¹' V` and the quotient topology on
`H \ G`. Every section value has the same stabilizer subgroup `H`, and
each fiber over `V` is the orbit of its section value. For each `b : V`
and each identity neighborhood `W` in `G`, all points `x` sufficiently
near `s b` in the whole subspace `p ⁻¹' V` are twisted conjugate to
`s ⟨p x, x.property⟩` by a conjugator in `W`.

The chart sends `(b,Hg)` to `g⁻¹ * s b * θ(g)`. The formula on `V × G`
is continuous by continuity of `s`, `θ`, and the group operations.
The product of the identity and the quotient projection is an open
quotient map, so the formula descends to a continuous map. The stabilizer
and orbit hypotheses make it bijective. To prove openness at `(b,Hg)`,
translate points near its image back to points near `s b` by twisted
conjugation by `g⁻¹`. The nearby points admit conjugators near the
identity by hypothesis. Multiplying them on the right by `g`
places their cosets near `Hg`, while continuity of `p` controls the
parameter coordinate. The chart intertwines `p` with projection.
