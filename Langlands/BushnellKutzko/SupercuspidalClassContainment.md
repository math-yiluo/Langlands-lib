# Containment of a pair `(J, λ)` in a supercuspidal class

Module `Langlands.BushnellKutzko.SupercuspidalClassContainment`, namespace
`Langlands.BushnellKutzko`. It defines `SupercuspidalClassContainsType`.

## Setting

Let `p` be a prime, `K : PadicField.{uK} p` and `F = K.Carrier`, with the topology of
`K.canonicalTopologicalData`. The topology of `GL_{k+1}(F) = GeneralLinear (k + 1) F` is the
one inferred from that of `F`; the class space
`Correspondence.SupercuspidalAutomorphicClass K k.succPNat`
(`Langlands/Correspondence/SupercuspidalRelations.lean`) uses the same one. That class space is
`GeneralLinear.SupercuspidalClass`: the isomorphism classes of objects of
`GeneralLinear.SupercuspidalRep`: the irreducible admissible smooth complex
representations of `GL_{k+1}(F)`, with carriers in `Type uV`, whose Jacquet quotients for all
proper block parabolics and their conjugates vanish
(`Langlands/Representation/Classification/Supercuspidal.lean`).

## Definition

Let `J` be a subgroup of `GL_{k+1}(F)` and `λ` a smooth complex representation of `J`, with
carrier in a universe `uρ` independent of `uK` and `uV`. A class `π` *contains* `(J, λ)`,

```
SupercuspidalClassContainsType K π λ
```

when some representative `A` of `π` (`A.isoClass = π`) contains `(J, λ)` in the sense of
`ContainsType` (`Langlands/BushnellKutzko/TypeContainment.lean`): there is a nonzero
`J`-homomorphism from `λ` to the restriction of `A` to `J`.

Containment is invariant under isomorphism of representations: if `e : A ≅ B` is an
isomorphism of representations of `GL_{k+1}(F)` and `f` is a nonzero `J`-homomorphism from
`λ` to the restriction of `A` to `J`, then the composite of `f` with `e` is a nonzero
`J`-homomorphism from `λ` to the restriction of `B` to `J`. So if `π` contains `(J, λ)`, then
every representative of `π` contains `(J, λ)`, and the existential form of the definition
agrees with the universal one. This file states the definition and does not prove this
invariance.

The pairs of `glMaximalSimpleTypesAt` and `glMaximalLevelZeroSimpleTypes`
(`Langlands/BushnellKutzko/GLMaximalSimpleTypeSets.lean`) are elements of
`GLRepresentationPair (k + 1) F`. The second component of such a pair is a representation `λ`
of the kind above, so `SupercuspidalClassContainsType K π x.2` says that `π` contains the
pair `x`.

## Source

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), §6.2, (6.2.1), printed p. 202 (PDF p. 214): an irreducible representation `π`
contains a simple type `(J, λ)` when `π | J` contains `λ`. BK93 states containment for a
representation. The definition here applies it to an isomorphism class through a
representative, which the invariance above justifies.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`,
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
