# Coherence of actual semilinear pinned lifts

Let `k` be a field in an arbitrary universe, `G` an actual affine group scheme
over `k`, and `p : SplitPinning G` a supplied complete split pinning.
For field ring automorphisms `σ, τ : k ≃+* k` and based full root-datum
automorphisms `e, d : p.basedRootDatumAut`, the actual semilinear pinned lifts
satisfy

```text
tower(σ, τ) ; lift(σ.trans τ, d * e)
  = pullback_τ(lift(σ, e)) ; lift(τ, d).
```

Here `;` is diagrammatic composition, `σ.trans τ` applies `σ` first and
`τ` second, and `d * e` applies `e` first and `d` second.
`semilinearPinnedIso_comp` proves this equality of complete
`SplitPinning.Iso` structures. The source of both sides is the actual pinning
obtained by pulling back `p` first along `Spec σ`, then along `Spec τ`;
the target is `p`. `semilinearPinnedIso_comp_groupIso` gives the same equality
of actual ambient group-scheme isomorphisms.

## Actual coefficient pullbacks

`Iso.baseChangeAlong` pulls back a supplied complete pinned isomorphism along
any ring equivalence between two fields in the same universe. As in
`SemilinearPinning`, the equivalence's algebra structure is installed only
inside the construction. Surjectivity proves algebraicity, and the published
`Iso.baseChange` transports the actual group and torus maps, all root data and
the chosen root vectors. The three projection theorems specify its torus
isomorphism, group isomorphism and unchanged root-index equivalence.

For `σ : k ≃+* K` and `τ : K ≃+* L`, `baseChangeAlongTowerIso` constructs the
complete pinned isomorphism from the two successive pullbacks to the direct
pullback along `Spec (σ.trans τ)`. The compatible algebra structures induced by
the equivalences form a scalar tower. Their algebraicity permits the published
`baseChangeTowerIso`.

The group and torus projection theorems identify the output with the actual
`Descent.pullbackComparison` and `Descent.commPullbackComparison`. These compare
iterated scheme pullbacks with the direct pullback; the equality of the base
maps follows from contravariance of `Spec.map`. The root-index projection is the
identity equivalence. Thus `tower(σ, τ)` in the displayed law is this particular
canonical comparison, including its actual group map and root-vector
compatibility.

## Implemented proof

Write `Bσ` for the weight equivalence of
`p.baseChangeAlongRootDatumEquiv σ`. It identifies the entire integral
character lattice with that of the actual coefficient pullback.

`Iso.baseChangeAlong_character` proves that pulling back a pinned isomorphism
commutes with this character map. Its proof is the naturality formula for
character base change under precomposition by the inverse torus map.
`baseChangeAlongTowerIso_character` uses the published character tower formula
to show that the tower comparison takes `Bτ(Bσ χ)` to `B(σ.trans τ) χ`.
`Iso.trans_character` records the diagrammatic composition formula for the
forward character action.

`semilinearPinnedIso_character` specializes the chosen pinned lift's full
character specification and cancels `Bσ` with its inverse. It states that the
semilinear lift takes `Bσ χ` to `e.weightEquiv χ`. The separate index theorem
identifies its index map with `e.indexEquiv`.

To prove the composition law, the implementation uses the published pinned
rigidity theorem `Iso.ext_torus_index`. The full-character faithfulness theorem
for split tori reduces equality of the actual torus isomorphisms to equality
on every character. Surjectivity of `Bτ` and `Bσ` writes each character of the
iterated pullback as `Bτ(Bσ χ)`. The two sides then take it to
`d.weightEquiv (e.weightEquiv χ)`, using the preceding naturality, tower and
semilinear formulas. The specified root-index maps compose in the same order.
Pinned rigidity gives equality of the complete pinned isomorphisms, and
projecting their ambient components gives the final group-scheme law.

## Provenance and scope

This is an internal derivation from the existing complete-pinning scalar
transport, canonical scalar-tower comparison, actual pinned lift and pinned
rigidity theorems. It makes no new external structural assertion.
All fields and their common universe remain arbitrary. Equality is checked on
the full integral character lattice, including central directions, and the
result concerns actual complete pinned isomorphisms rather than only their
root permutations or rational-point actions.

The complete pinning and the based root-datum automorphisms are inputs.
This unit establishes the composition law; it does not yet establish the
canonical identity law, an assembled Galois or Čech descent datum, effective
descent, pinning existence, a full-centre quotient, or unconditional
quasi-split inner-form existence.
