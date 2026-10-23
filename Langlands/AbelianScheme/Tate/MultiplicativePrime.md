# The prime-adic Tate module of the multiplicative group

This module identifies the actual torsion-section Tate module of the published
multiplicative group scheme with the published roots-of-unity Tate twist.
Fix any scheme `S`, any test scheme `T : Over S`, and, for the prime-adic
constructions, a natural number `p` with `Fact p.Prime`. All declarations are
in `Langlands.GroupScheme.Gm.TateComparison`.

The main construction is

```text
primeIntegralContinuousLinearEquiv T p :
  Tate.PrimeAdic.Integral (Gm S).toGrp T p ≃L[ℤ_[p]]
    TateTwist.Integral Γ(T.left, ⊤) p.
```

It uses the existing scalar structures and inverse-limit topologies on both
sides. Its maps act coordinatewise by the canonical identification of torsion
sections of `Gm` with roots of unity in global sections. No primitive roots or
bases are chosen.

## Internal provenance

This is an internal comparison of three published constructions:
`Langlands.GroupScheme.Multiplicative`,
`Langlands.AbelianScheme.Tate.PrimeAdic`, and
`Langlands.AbelianScheme.Tate.Twist` (the last is imported through
`Multiplicative`). Their paired Markdown records their original provenance.
The new equivalence is derived from `mu.torsionPointsUnitsEquiv` and its
underlying map `Gm.pointsEquiv`, followed by a coordinatewise passage to the
existing coherent limits. It asserts no additional theorem from original
literature. Its elementary compatibility and continuity proofs are described
below.

## Finite levels

For every natural number `n`, `levelEquiv T n` is an additive equivalence
from `Tate.Level (Gm S).toGrp T n` to
`TateTwist.Level Γ(T.left, ⊤) n`. It is the additive form of the published
multiplicative equivalence `mu.torsionPointsUnitsEquiv S n T`. Thus the source
is the actual torsion subgroup of sections, and the target is the actual
subgroup of roots of unity, written additively. The definition also permits
`n = 0`, using the existing zero-torsion convention on both sides.

`toUnit_levelEquiv` identifies the underlying unit as the image of the
underlying section under `Gm.pointsEquiv S T`. The equality is definitional.
`levelEquiv_kernelLevelEquiv` states that composing the actual kernel-point
identification `Tate.kernelLevelEquiv` with `levelEquiv` is the published
`mu.pointsLevelEquiv`; this too is definitional.

For `h : n ∣ m`, `levelEquiv_transition` states

```text
levelEquiv T n (Tate.transition (Gm S).toGrp T h x) =
  TateTwist.transition Γ(T.left, ⊤) h (levelEquiv T m x).
```

The proof applies the injective inclusion of roots into units. Both transitions
are then raising to the natural power `m / n`, and the result is preservation
of powers by `Gm.pointsEquiv`. The lemma needs no positivity assumption beyond
the given divisibility relation.

`levelLinearEquiv T n` packages the same map as a `ZMod n`-linear equivalence.
`ZMod.map_smul` supplies the scalar law for the additive homomorphism between
the existing residue modules; `levelLinearEquiv_apply` is reflexive.

For `a : T' ⟶ T`, `levelEquiv_restrict` compares the actual restriction
`torsionPointsRestrict` with `TateTwist.levelMap a.left.appTop.hom n`.
After inclusion into units, it is exactly the naturality of `Gm.pointsEquiv`.
This is a finite-level restriction law; this module does not package
restriction maps on the inverse limits.

## Prime-adic limit and scalar structure

At level `p ^ n`, `levelEquiv_padic_smul` proves preservation of the existing
`ℤ_[p]`-actions. Both act through
`PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)`, so the same residue-linearity
lemma proves the result.

`primeIntegralEquiv T p` is the `ℤ_[p]`-linear equivalence of the two coherent
prime-power limits. The forward map applies `levelEquiv T (p ^ n)` at every
coordinate; the inverse applies its inverse. The forward coherence proof
rewrites by `levelEquiv_transition` and the source's coherence equation. The
inverse coherence proof applies injectivity of the finite-level equivalence
and reduces to the target's coherence equation. The inverse laws and
additivity are coordinatewise; the scalar law is `levelEquiv_padic_smul`.

`evaluation_primeIntegralEquiv` and
`evaluation_primeIntegralEquiv_symm` give the coordinate formulas for both
directions using the existing evaluation maps. Both identities are reflexive.

## Topology

Each finite level on either side already has the discrete topology. Each
integral limit already has the subtype topology inherited from the product
of those levels. `continuous_primeIntegralEquiv` and
`continuous_primeIntegralEquiv_symm` prove continuity into the subtype by
checking every coordinate: a finite-level equivalence or its inverse is
continuous by discreteness, and the existing coordinate evaluation is
continuous.

`primeIntegralContinuousLinearEquiv T p` bundles `primeIntegralEquiv` with
these two proofs. Its `_apply` lemma records that its underlying map is
unchanged. Continuity here does not require finite torsion levels or compact
limits.

## Scope

The construction works over arbitrary test schemes and arbitrary base
schemes. It assumes no invertibility of `p`, finite étaleness, rank, or
finiteness of torsion. It constructs no twist trivialization, Weil pairing,
monodromy action, or rational/full/away comparison. Those remain separate
integration obligations in the parent task.
