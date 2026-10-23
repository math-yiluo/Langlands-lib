# Full and away Tate modules of the multiplicative group

For any scheme `S`, test scheme `T : Over S`, and predicate `P : ℕ → Prop`,
this module canonically identifies the selected actual torsion limit of `Gm S`
with the selected roots-of-unity limit in `Γ(T.left, ⊤)`. It gives continuous
linear equivalences for the full and away residue scalar rings and compatibility
with full-to-away restriction and prime-power extraction. The declarations are
in `Langlands.GroupScheme.Gm.TateComparison`.

## Internal provenance

The module imports the published `MultiplicativePrime` comparison and the
published `PrimeComparison` module. Their imports supply `Tate.Integral`,
`Tate.Scalars`, `TateTwist.Divisibility`, and `TateTwist.Divisibility.toPrime`.
No carrier, transition, scalar ring, scalar action, or topology is replaced.
The finite-level maps are the canonical `levelEquiv` from
`MultiplicativePrime`, ultimately derived from the actual `Gm`-units
identification. Their transition and residue-linearity laws give the new
comparison by applying them coordinatewise. This is an internal consequence
of the published constructions, with no additional claim attributed to an
original source.

## Selected and full limits

`integralEquiv T P` is a linear equivalence

```text
Tate.Integral (Gm S).toGrp T P ≃ₗ[Global.ProfiniteIntegerRing]
  TateTwist.Divisibility.Integral Γ(T.left, ⊤) P.
```

Both limits are indexed by the same type `Tate.Index P` of positive natural
numbers satisfying `P`. No closure, nonemptiness or cofinality property of `P`
is assumed. The map sends a coherent family `x` to the family
`n ↦ levelEquiv T n.val (x n)`. Its inverse applies the inverse finite-level
equivalence at every coordinate.

The forward coherence proof uses `levelEquiv_transition` and the source
coherence equation for any `n ∣ m`. The inverse coherence proof applies
injectivity of the finite-level equivalence and uses the target coherence
equation. The inverse laws and additivity follow coordinatewise from those
of `levelEquiv`. The scalar law follows from `ZMod.map_smul` applied to the
finite-level additive equivalence and the shared residue
`Tate.fullReduction P n a`. Thus it preserves the existing actions of the
full profinite-integer ring.

`evaluation_integralEquiv` and `evaluation_integralEquiv_symm` record the
coordinate formulas in both directions; they are definitional equalities.

`continuous_integralEquiv` and `continuous_integralEquiv_symm` use the existing
product-subtype topologies. Each coordinate is the corresponding continuous
evaluation followed by a map between discrete finite-level types. Continuity
into the product and then the subtype proves continuity in both directions.
Here “finite-level” refers to a torsion order, not an assumption that its
underlying set is finite.

`integralContinuousLinearEquiv T P` bundles the linear equivalence with these
continuity proofs, and its `_apply` lemma identifies its underlying map.
`fullContinuousLinearEquiv T` is the specialization `P = fun _ => True`.

## The away scalar ring

For any natural number `m`, `awayEquiv T m` is

```text
Tate.Away (Gm S).toGrp T m ≃ₗ[Global.PrimeToProfiniteIntegerRing m]
  TateTwist.Divisibility.Away Γ(T.left, ⊤) m.
```

Its underlying additive equivalence is `integralEquiv T` for the predicate
`fun n => Nat.Coprime n m`. Its new scalar-linearity proof uses
`ZMod.map_smul` with the shared residue `Tate.awayReduction m n a`.
It therefore preserves the existing action of the away scalar ring, as well
as the full-ring action already expressed by the selected comparison.
`awayEquiv_apply` is the definitional equality of these underlying functions.

`awayContinuousLinearEquiv T m` bundles the same equivalence with the
continuity proofs from the selected construction. Its `_apply` lemma also
identifies the underlying selected map. No primality assumption is imposed
on the excluded modulus `m`.

## Restriction and prime extraction

`awayContinuousLinearEquiv_restrictAway` states that restricting actual full
Tate families to orders coprime to `m` and then applying the comparison equals
applying the full comparison and restricting the roots-of-unity family.
`awayContinuousLinearEquiv_symm_restrictAway` proves the inverse square.
Both are definitional: the operations read the same coordinates and apply
the same finite-level equivalence or its inverse.

For a natural prime `p`, with `Fact p.Prime`,
`primeIntegralContinuousLinearEquiv_toPrime` says that the existing actual
prime-power extraction followed by the published prime-adic `Gm` comparison
equals the selected comparison followed by roots-of-unity extraction. This
requires an explicit witness `hP : ∀ n, P (p ^ n)`. Both sides at exponent `n`
apply `levelEquiv T (p ^ n)` to the same selected coordinate, so the equality
is definitional.

`primeIntegralContinuousLinearEquiv_fullToPrime` gives the full specialization.
`primeIntegralContinuousLinearEquiv_awayToPrime` gives the away specialization
with `h : Nat.Coprime p m`. The latter ensures that every power of `p` is
retained. These two identities are also definitional. They are pointwise
commuting-square formulas for the existing maps; no product comparison is
needed.

## Scope

The equivalences require no characteristic, invertibility, rank, finite
étaleness, compactness or torsion-finiteness hypotheses. They compare actual
coherent families and do not trivialize the twist. Rationalization, comparison
with products or restricted products, base change of test schemes, geometric
monodromy and Weil pairings are outside this focused unit. In particular,
full-to-away restriction here changes the set of torsion orders, not the test
scheme. The broader Tate/Weil/PEL task remains incomplete.
