# Pair gamma matching from two Hecke Euler families

Supporting module of Task 5003 (module `Langlands.Automorphic.AssociatedGammaHeckeReduction`). `HasHeckeGammaCertificate` packages, for one
self-dual measure `ν`, an original bad set `T ∋ v`, depths, an automorphic and an arithmetic
`HeckeEulerFamily`, actual gamma factors `G` (automorphic, `IsAutomorphicPairGammaFactor`) and
`H` (arithmetic, `IsArithmeticPairGammaFactor`) whose rational continuations are the untwisted
gamma factors of the two families at `v`, and the five engine inputs
`CommonTwistEulerInputs`, `InfinityGammaPreservation`, `FiniteGammaPreservation`,
`RamifiedGammaStability`, `OutsideGammaStability`.

`isPairGammaMatch_of_heckeGammaCertificate` proves `IsPairGammaMatch` from a self-dual measure
and a certificate for every self-dual measure. Proof: the published `heckeTwistComparison`
with the published `ramifiedTwistIsolation` gives meromorphic equality of the untwisted gamma
functions at `v`; the published `germRationalComparison` (residue cardinality > 1) turns this
into `G = H`. This is the argument of the published `relativeGammaComparison` without its unused
`FiniteAdditiveSupport` and `FiniteTwistGammaRealizations` inputs.
