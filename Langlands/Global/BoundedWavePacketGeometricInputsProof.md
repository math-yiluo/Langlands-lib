# The two geometric inputs to the bounded wave packet reduction

Module `Langlands.Global.BoundedWavePacketGeometricInputsProof` proves the two existence
statements used in `Langlands.Global.boundedWavePacketLocalSufficiency`: a Levi projection
and a compatible Levi Haar measure. Both statements are in `AdelicLocalWavePacketStatement`.
The module does not prove the analytic premises or Lapid's Lemma 10.

## Levi projection (C1)

`Langlands.Global.leviProjectionExistence : LeviProjectionExistenceStatement` uses the rational
Levi condition of `r.isCompatible`. Its `exists_unipotentRadical` supplies a geometric
unipotent radical `r₀ : U₀ ⟶ P` for which `subgroupMultiplication l r₀ : M × U₀ → P` is an
isomorphism of schemes. This is the radical supplied by the Levi condition, not necessarily
the presentation's given `iU`. Normality of the range of `r₀` gives the group-scheme
homomorphism `leviRetraction l r₀ hr₀.1.isNormal`, the Levi coordinate of the inverse of that
isomorphism. The lemma `levi_comp_leviRetraction` verifies that its composition with `l` is
`𝟙 M`.

This implements the projection of the semidirect product `P = M ⋉ U`, as in Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Theorem 1.5.8, Definition 1.5.9 and the
remark after it (p. 16). It does not construct a quotient by `U`.

## Iwasawa-compatible Haar measure (C2)

`Langlands.Global.wavePacketIwasawaCompatibleMeasureExistence :
WavePacketIwasawaCompatibleMeasureExistenceStatement` applies the published
`iwasawaCompatibleMeasureIntegrationReduction` to the proofs
`AdelicGroupPoints.adelicIwasawaIntegration` and `AdelicGroupPoints.adelicParabolicModulus`.
The resulting `IwasawaCompatibleMeasureExistenceStatement` has the same conclusion for the
same parabolic presentation and compact subgroup. Its hypotheses are weaker: it does not
require the three split-torus and relative-Weyl instances on the presentation's root data or the
two split-torus proofs `hA` and `hT`. The specialization leaves those binders in the wave packet
statement and uses the result for its given `r`, `K` and `hK`.

The measure is therefore the one for the Iwasawa integral of Getz–Hahn, Exercise 3.5 (p. 99),
with the normalizations of `IsIwasawaCompatibleMeasure`: the ambient Mathlib Haar measure, the
unipotent Haar measure of quotient mass one, and the compact Haar probability. This proof
reuses the published integration and modulus results; it adds no measure comparison.
