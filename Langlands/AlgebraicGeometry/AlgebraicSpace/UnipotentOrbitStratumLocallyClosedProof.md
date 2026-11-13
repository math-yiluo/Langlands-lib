# Orbit-dimension strata are locally closed: proof

Author: Worker 79 of the previous project instance (revision 2 of the shared draft of
Task 5217). Submitted by Worker 169, who rechecked it against the current Library.

Proof of `Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitStratumLocallyClosedStatement.{u}`,
the first clause of Conrad's Example 5.5 (printed p.16). The theorem is
`Langlands.AlgebraicGeometry.AlgebraicSpace.unipotentOrbitStratumLocallyClosed`. For a
unipotent algebraic group `G` over a henselian valued field `K` of characteristic zero
acting by `a` on a reduced `K`-scheme `V` of finite type, and for `d : ℕ`, the set
`{v : V.left | HasOrbitDimension a v d}` is locally closed.

The proof uses only that `G.X.hom` is locally of finite type, the second component of
`IsUnipotentAlgebraicGroup K G`. It does not use unipotence, the field, its henselian
valuation, characteristic zero or the hypotheses on `V`. The general result is
`UnipotentOrbitStratum.isLocallyClosed_orbitStratum`: for any scheme `S`, group scheme
`G` over `S` with `G.X.hom` locally of finite type, action `a` of `G` on `V : Over S`, and
`d : ℕ`, the stratum `{v | HasOrbitDimension a v d}` is locally closed.

Conrad's only justification is a parenthetical remark: the set is locally closed "due
to applying semicontinuity of fiber dimension to the action map `G × V → V`". The Lean
proof instead applies upper semicontinuity of relative local dimension to the
projection of the stabilizer scheme to `V`. It uses two published Library results:

- `stabilizerFibreLocalDimension : StabilizerFibreLocalDimensionStatement.{u}` (Stacks
  Lemma 39.8.1, Tag 045X, for stabilizer fibres): if `σ` is the projection of the
  stabilizer scheme to `V`, then at every point `x` of the stabilizer scheme
  `relativeTopologicalKrullDimAt σ.left x = topologicalKrullDim (σ.left.fiber (σ.left x))`.
  The same module supplies `StabilizerFibre.locallyOfFiniteType_proj`: `σ.left` is
  locally of finite type when `G.X.hom` is.
- `SchemeFiberGeometry.relativeDimensionSublevelOpenness_proof :
  RelativeDimensionSublevelOpenness.{u}` (Stacks Lemma 29.29.4): for a morphism `f`
  locally of finite type and `n : ℕ`, the set of points where the relative local
  dimension of `f` is at most `n` is open.

Helper declarations are in the namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitStratum`.

## Level sets of a function with open sublevel sets

Let `f : X → WithBot ℕ∞` on a topological space `X`, with `0 ≤ f x` for all `x` and
`{x | f x ≤ m}` open for every natural number `m`.

- `isOpen_le_of_sublevels`: `{x | f x ≤ e}` is open for every `e : WithBot ℕ∞`. For
  `e = ⊥` it is empty because `f` is nonnegative, for `e = ⊤` it is everything, and for a
  natural number `e` it is a hypothesis.
- `isOpen_lt_of_sublevels`: `{x | f x < e}` is open for every `e`. For `e = ⊥` and `e = 0`
  it is empty. For `e = m + 1` it equals `{x | f x ≤ m}`, by
  `ENat.WithBot.lt_add_one_iff`. For `e = ⊤` it is the union over `m : ℕ` of
  `{x | f x ≤ m}`.
- `isLocallyClosed_level_of_sublevels`: `{x | f x = e}` is the intersection of the open
  set `{x | f x ≤ e}` with the closed set `{x | f x < e}ᶜ`, hence locally closed.

`withBot_add_natCast_cancel`: in `WithBot ℕ∞`, `x + d = y + d` with `d : ℕ` implies
`x = y`. If one side is `⊥`, then so is the other, because `d ≠ ⊥`. Otherwise the
equation holds in `ℕ∞`, where `d ≠ ⊤` can be cancelled (`WithTop.add_right_cancel`).

## The identity section of the stabilizer scheme

`stabilizerUnit a : V ⟶ pullback (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))` is the
section `v ↦ (1, v)`. It is `pullback.lift (lift 1 (𝟙 V)) (𝟙 V) _`, where the pullback
condition `lift (a.act 1 (𝟙 V)) (𝟙 V) = lift (𝟙 V) (𝟙 V)` follows from
`SchemeAction.act_one`. `stabilizerUnit_snd` says that it is a section of the projection
`σ = pullback.snd …`.

## The main argument

Fix `a`, `hG : LocallyOfFiniteType G.X.hom` and `d`. Write `σ` for the projection of the
stabilizer scheme to `V`, `ε = (stabilizerUnit a).left` for the identity section on
underlying schemes, and `δ v = topologicalKrullDim (σ.left.fiber v)` for the dimension of
the stabilizer of `v`. Then `σ.left (ε v) = v` by `stabilizerUnit_snd`.

1. `stabilizerFibreLocalDimension` at the point `ε v`, together with `σ.left (ε v) = v`,
   gives `δ v = relativeTopologicalKrullDimAt σ.left (ε v)`.
2. Since `σ.left` is locally of finite type (`locallyOfFiniteType_proj`),
   `relativeDimensionSublevelOpenness_proof σ.left m` says that the sublevel set
   `{x | relativeTopologicalKrullDimAt σ.left x ≤ m}` is open. Its preimage under the
   continuous map `ε` is `{v | δ v ≤ m}` by step 1, so this set is open for every `m : ℕ`.
3. `δ` is nonnegative by step 1 and `relativeTopologicalKrullDimAt_nonneg`.
4. `HasOrbitDimension a v d` unfolds to `topologicalKrullDim G.X.left = δ v + d`. If
   `topologicalKrullDim G.X.left = e + d` for some `e`, then by
   `withBot_add_natCast_cancel` the stratum is the level set `{v | δ v = e}`, which is
   locally closed by `isLocallyClosed_level_of_sublevels` and steps 2 and 3. Otherwise
   the stratum is empty, hence closed and locally closed.

Finally `unipotentOrbitStratumLocallyClosed` takes `K`, `G` with
`hG : IsUnipotentAlgebraicGroup K G`, `V`, `a` and `d`, and applies
`isLocallyClosed_orbitStratum a hG.2.1 d` over `S = Spec K`.

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.
