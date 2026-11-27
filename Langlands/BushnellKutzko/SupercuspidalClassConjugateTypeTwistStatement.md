# Supercuspidal classes containing conjugate maximal simple types are unramified twists

Module `Langlands.BushnellKutzko.SupercuspidalClassConjugateTypeTwistStatement`, namespace
`Langlands.BushnellKutzko`. It defines the proposition
`SupercuspidalClassConjugateTypeTwistStatement.{uK, uV, uT}` and does not prove it.

## Statement

Let `p` be a prime, `K : PadicField.{uK} p` and `k : ℕ`. Let `x` and `x'` be pairs of
`GLRepresentationPair.{uK, uT} (k + 1) K.Carrier`, that is, subgroups of `GL_{k+1}(K)` with
smooth complex representations on carriers in `Type uT`. Suppose that

- `x ∈ glMaximalSimpleTypesAt (k + 1) K.Carrier t m` for some `t, m : ℕ` with `1 ≤ t` and
  `1 ≤ m`, or `x ∈ glMaximalLevelZeroSimpleTypes (k + 1) K.Carrier`;
- `x'` is `GL_{k+1}(K)`-conjugate to `x`: `AreConjugatePairs x.2.representation
  x'.2.representation` (`Langlands/BushnellKutzko/PairConjugation.lean`), so for some
  `g ∈ GL_{k+1}(K)` the subgroup of `x'` is `gJg⁻¹`, `J` the subgroup of `x`, and the
  representation of `x'` pulled back along `j ↦ gjg⁻¹` is equivalent to that of `x`.

Then for all supercuspidal classes `π, π' : Correspondence.SupercuspidalAutomorphicClass.{uK,
uV} K k.succPNat` such that `π` contains `x` and `π'` contains `x'`, there is `z : ℂˣ` with

```
Henniart.Numerical.supercuspidalUnramifiedTwist K k z π = π'.
```

Containment is `SupercuspidalClassContainsType`
(`Langlands/BushnellKutzko/SupercuspidalClassContainment.lean`). The twist by `z`
(`Langlands/Correspondence/HenniartNumericalStatement.lean`) is the class twist by the
character `g ↦ z ^ ord(det g)` of `GL_{k+1}(K)` (`determinantUnramifiedCharacter`), that is,
`π ↦ π ⊗ (χ ∘ det)` for the unramified quasicharacter `χ` of `K^×` with `χ(ϖ_K) = z`. The field
`K.Carrier` carries the instances of `K.canonicalTopologicalData`, as in the class space and
the two sets of pairs (`Langlands/BushnellKutzko/GLMaximalSimpleTypeSets.lean`). The universes
`uK`, `uV` and `uT` are independent.

## Provenance

The statement transfers to the Library's class objects, and from one maximal simple type to
`GL_{k+1}(K)`-conjugate pairs, the last assertion of BK93 (6.2.3), printed p. 204: if `(J, λ)`
is a simple type with `e(𝔅 | 𝔬_E) = 1` and `π` is an irreducible representation containing
`λ`, then an irreducible representation `π'` contains `λ` if and only if
`π' ≅ π ⊗ (χ ∘ det)` for some unramified quasicharacter `χ` of `F^×`. The Library states
this as `Langlands.BushnellKutzko.MaximalSimpleTypeUnramifiedOrbitStatement`. The pairs of
`glMaximalSimpleTypesAt` and of `glMaximalLevelZeroSimpleTypes` are maximal simple types in
this sense. The statement is not a numbered result of a source in this form.

Two elementary facts connect the two forms. A representation containing the conjugate pair
`(gJg⁻¹, λ^{g⁻¹})` contains `(J, λ)`: the action of `g⁻¹` carries the
`gJg⁻¹`-homomorphisms from `λ^{g⁻¹}` to the `J`-homomorphisms from `λ`. And every unramified
quasicharacter `χ` of `K^×` is `ϖ_K^j u ↦ z^j`, `u ∈ 𝔬_K^×`, with `z = χ(ϖ_K)`, so
`χ ∘ det` is `g ↦ z ^ ord(det g)`.

## Source

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), (6.2.3), last assertion, and the definition of a maximal simple type before it,
printed p. 204 (PDF p. 216).
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`,
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
