# Perfectness of an invariant pairing from surjectivity at each compact open level

Author: Worker 937.

`Langlands.exists_smoothDualEquiv_of_fixedSurjective` is a generic criterion
for an invariant pairing to identify one smooth representation with the smooth
contragredient of another. It is an internal derivation from the Library's
smooth lifting and fixed-level restriction results, with no external source
attribution. It is a variant of `Langlands.smoothInvariantPairingDuality`
(`InvariantPairingProof.lean`) in which the admissibility of one side is
replaced by a surjectivity condition at each compact open level.

## Statement

Let `G` be a topological group in which every open subgroup contains a compact
open subgroup (`hcofinal`). Let `ρ` on `V` and `σ` on `W` be smooth complex
representations of `G`, and let `b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ` be a bilinear map with

- invariance: `b (σ g w) (ρ g v) = b w v` for all `g`, `w`, `v`;
- nondegeneracy on `W`: `w = 0` when `b w v = 0` for every `v`;
- surjectivity at each compact open level: for every compact open subgroup
  `L` and every linear functional `φ` on the fixed vectors `V^L`, there is
  `w ∈ W^L` with `b w v = φ v` for every `v ∈ V^L`.

Then there is a representation equivalence `E` from `σ` to the smooth
contragredient of `ρ` with `smoothDualPairing ρ (E w) v = b w v`.

No admissibility, finite-dimensionality or nondegeneracy on `V` is assumed.

## Proof

By invariance, `b` is an intertwiner from `σ` to the full dual `ρ.dual`: the
calculation applies invariance to `w` and `ρ g⁻¹ v`. Since `σ` is smooth,
`smoothLift` restricts it to an intertwiner `F` from `σ` to the smooth
contragredient, and `F w` evaluates to `b w`. Nondegeneracy on `W` says that
`F` has zero kernel, so `F` is injective.

For surjectivity take a smooth functional `ℓ`, fixed by an open subgroup `K`.
By `hcofinal` choose a compact open `L ≤ K`; then `ℓ` is `L`-fixed. Apply the
surjectivity hypothesis at `L` to the restriction of `ℓ` to `V^L`, obtaining
`w ∈ W^L` whose pairing agrees with `ℓ` on `V^L`. Since `F` is an intertwiner,
`F w` is `L`-fixed as well. The two `L`-fixed smooth functionals `F w` and `ℓ`
have the same restriction to `V^L`. The injective half of
`smoothDualFixedRestriction_bijective` (for the smooth `ρ` and the compact open
`L`) gives `F w = ℓ`.

Finally `Representation.IntertwiningMap.ofBijective` turns `F` into a
representation equivalence; its evaluation identity is definitional.

## Scope

This file constructs no induction or Jacquet pairing and proves none of their
hypotheses. Its use is the duality of smooth parabolic induction for every
smooth inducing representation, where the level-wise surjectivity comes from
the finite double-coset decomposition of the fixed vectors of an induced
representation.
