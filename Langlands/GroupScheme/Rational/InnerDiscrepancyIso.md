# Actual relative automorphisms representing inner discrepancies

This is an internal construction, derived from the published
`LocalGroupIso` recovery equivalence, refinement, base-change of automorphic
actions, and the definition of `RepresentsDiscrepancy`. It does not transcribe
a separate assertion from the literature.

Let `S` be any scheme, let `G`, `H`, and `A` be group schemes over `S`, let
`U` be a scheme over `S`, let `e : LocalGroupIso G H U`, and let
`a : AutomorphicAction A G`. For a test scheme `T` over `S` and maps
`b c : T ⟶ U`, `e.discrepancyFamily b c` is the natural family sending a
point `g` after a refinement `t : W ⟶ T` to
`(e.toFun (t ≫ b)).symm (e.toFun (t ≫ c) g)`.
Its naturality follows by applying the naturality of `e` and of `e.symm`.
The actual automorphism `e.discrepancyIso b c` of `G` pulled back to `T`
is recovered from this family by `toBaseChangeIso`.
`discrepancyIso_toFun` states its effect on every relative test, and
`discrepancyIso_eq_composite` identifies it with the actual isomorphism
`(e.refine c).toBaseChangeIso` followed by the inverse of
`(e.refine b).toBaseChangeIso`.

For `x : T ⟶ A.X`, `a.relativePointIso x` evaluates the action pulled back
to `T` at the section corresponding to `x` under `coverPointsEquiv`.
`relativePoint_constantPoint` identifies the projection of this constant
section on any test over `T`. `relativePointIso_points` then computes the
action of the evaluated automorphism after projection to `G`.
`relativePointIso_toFun` expresses the same formula on every scheme `W`
over `S` with a specified map `t : W ⟶ T`: its value at `g` is
`a.act (t ≫ x) g`. The proof uses the canonical test over `T` attached
to `t` and naturality of the action.

`representsDiscrepancy_iff_discrepancyIso` proves that the equation
`e.toFun (t ≫ b) (a.act (t ≫ x) g) = e.toFun (t ≫ c) g`
on every refinement and point is equivalent to
`e.discrepancyIso b c = a.relativePointIso x`. In the forward direction,
the recovery equivalence and extensionality reduce equality of actual
isomorphisms to equality on tests; injectivity of `e.toFun (t ≫ b)`
gives that equality. The reverse direction evaluates the equality and
applies the inverse-cancellation identity. Finally,
`hasInnerDiscrepancy_iff_discrepancyIso` applies this equivalence to every
pair `b c`.

No covering, flatness, affineness, reductivity, faithfulness, or
connectedness hypothesis is needed. This construction translates supplied
local innerness into equality of actual relative automorphisms. It does not
construct inner representatives, an invariant pinned datum, or a quasi-split
inner form, and does not prove the host existence statement.
