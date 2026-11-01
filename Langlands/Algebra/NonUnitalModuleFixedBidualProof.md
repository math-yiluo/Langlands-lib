# Fixed-bidual inverse and evaluation comparisons: proof

Worker 6 wrote the Lean proof and its first explanation. Worker 735 revised this
explanation.

The module `Langlands.Algebra.NonUnitalModuleFixedBidualProof` proves the
published closed proposition
`Langlands.Algebra.NonUnitalModuleFixedBidualStatements.FixedBidualComparisons`.
The final theorem is

```lean
theorem fixedBidualComparisons : FixedBidualComparisons.{uA, uM}
```

Its complete type is the unchanged closed target, with independent algebra and
module universes `uA` and `uM`. The module checks the theorem at arbitrary
`uA, uM` and at the two unequal orders `{0, 1}` and `{2, 0}`. Its only import
is the published statement module, which in turn imports the published maps
`toOrdinaryBidual` and `fromOrdinaryBidual` of
`Langlands.Algebra.NonUnitalModuleFixedBidualMaps`; neither is changed.

The proof adds no hypothesis. It uses no finite dimension, admissibility,
reflexivity, simplicity of a dual, or supplied equivalence of vector spaces,
and puts no complex structure on an original carrier other than the canonical
recovered ones.

## Source

The comparisons are internal steps in the corrected proof of the reflexivity
proposition I.5.1 of David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, printed p.26 / PDF p.32. The
registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, PDF p.2,
corrects the converse proof on printed 2010 p.29 by passing through the
ordinary bidual of each fixed space. The source does not number these exact
equations of the actual maps as a separate theorem. Their proofs below are
direct calculations with the actual maps, and the source does not supply them.

## Setup

The proof introduces the algebra `A`, its instances, the module `M`, `hA` and
`hM`. It then installs exactly the structures that the target names:

- the original `Aᵐᵒᵖ`-action `dualAction hA hM` on `Dual hA hM`, and the
  original `A`-action `bidualAction hA hM` on `Bidual hA hM`, which is the
  double-opposite transport;
- the recovered complex scalars
  `NondegenerateScalars.complexModule hA.op (isNondegenerate hA hM)` on the
  actual first dual;
- for the inverse laws, at each idempotent `e`, the recovered scalars
  `NondegenerateScalars.complexModule hA hM` on `M` and the canonical
  fixed-space scalars `NonUnitalModuleCorner.complexModule hA hM e` and
  `NonUnitalModuleCorner.complexModule hA (bidual_isNondegenerate hA hM) e`;
- for the evaluation law, the canonical fixed-space scalars
  `NonUnitalModuleCorner.complexModule hA hM e`, which the target itself
  installs.

An element `Φ` of the fixed part `FixedPart e (Bidual hA hM)` is a nested
subtype: `Φ.val` is in the actual bidual and `Φ.val.val` is a complex-linear
functional on `Dual hA hM`. Equalities in this fixed part are proved by two
applications of `Subtype.ext`, then `LinearMap.ext`.

## Left inverse

For `Φ` in `FixedPart e (Bidual hA hM)`, the goal is
`fromOrdinaryBidual hA hM e (toOrdinaryBidual hA hM e Φ) = Φ`. After the
nested extensionality it suffices to prove, for every `φ : Dual hA hM`,

```
Φ.val.val (extendToDual hA hM e (restrictFromDual hA hM e φ)) = Φ.val.val φ.
```

The left side unfolds by definition of the two published maps.

The local fact `h` states
`extendToDual hA hM e (restrictFromDual hA hM e φ) = op (e : A) • φ`. It is
proved by `Subtype.ext` and `LinearMap.ext`, and then holds by definition at
each `m : M`. The left value is `φ` applied to the projection of `m` to the
fixed part, which is `φ (e • m)`. The right value is the original
precomposition action of `op e` on `φ`, which is also `φ (e • m)`.

After rewriting with `h`, the goal is
`Φ.val.val (op (e : A) • φ) = Φ.val.val φ`. The fixed-part witness
`Φ.property` states `e • Φ.val = Φ.val` for the actual `bidualAction`. The value
of `e • Φ.val` at `φ` is, by definition of the double-opposite transport,
`Φ.val.val (op e • φ)`. Evaluating `Φ.property` at `φ` therefore closes the goal.

## Right inverse

For `Ψ` in the ordinary algebraic bidual of `FixedPart e M`, the goal is
`toOrdinaryBidual hA hM e (fromOrdinaryBidual hA hM e Ψ) = Ψ`. By
`LinearMap.ext` it suffices to show, for every functional `ell` on the fixed
space,

```
Ψ (restrictFromDual hA hM e (extendToDual hA hM e ell)) = Ψ ell.
```

The left side again unfolds by definition. By `congrArg Ψ` and
`LinearMap.ext` the remaining claim is
`ell (NonUnitalModuleCorner.projection e x.val) = ell x` for every fixed
vector `x`. The projection of `x.val` has underlying vector `e • x.val`, and
this equals `x.val` by the witness `x.property`. Hence `Subtype.ext x.property`
identifies the projection with `x`, and `congrArg ell` concludes.

## Evaluation compatibility

For an idempotent `e` and `x : FixedPart e M`, the goal is that
`(fromOrdinaryBidual hA hM e (Module.Dual.eval ℂ (FixedPart e M) x)).val`
equals `evaluation hA hM x.val`, as whole elements of the actual bidual.
After `Subtype.ext` and `LinearMap.ext`, both sides are evaluated at an
arbitrary `φ : Dual hA hM`. The left side is the ordinary evaluation at `x`,
applied to the restriction of `φ`, which is `φ.val x.val`. The right side is
the published actual evaluation, whose value at `φ` is also `φ.val x.val`.
The two values agree by definition, and `rfl` closes the goal.

## Assembly

The two inverse laws, for every idempotent, give `InverseComparisons hA hM`,
and the evaluation law gives `EvaluationCompatibility hA hM`. Their
conjunction, for every original algebra, module and witnesses, is exactly
`FixedBidualComparisons.{uA, uM}`.

The proof is complete, with no `sorry` and no new axiom. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`. It proves neither the
finite-dimensionality criterion nor the I.5.1 admissibility or simplicity
results; those remain separate obligations.
