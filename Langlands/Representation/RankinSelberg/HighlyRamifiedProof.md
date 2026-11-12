# Proof of highly ramified gamma stability

Module `Langlands.Representation.RankinSelberg.HighlyRamifiedProof`.

`highlyRamifiedGammaStability : HighlyRamifiedGammaStabilityStatement.{uF, uV, uW}` proves
the statement `Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement` of the
Library module `HighlyRamifiedStatement`. That statement is Jacquet and Shalika, A Lemma on
Highly Ramified ε-Factors, Math. Ann. 271 (1985), Proposition (4.1) (printed p. 326), for
generic pairs.

## Statement

The statement keeps all of its data. `F` is any p-adic field with its canonical topology.
`ψ` is any additive character of conductor exponent zero, and `ν` its supplied self-dual
Haar measure. The positive ranks `r + 1` and `t + 1` are arbitrary, in either order.
`π₁, π₂` are representations of `GL_(r+1)(F)` on independent carriers in universe `uV`,
generic in the sense of `Whittaker.IsGeneric` (which includes irreducibility and
admissibility), with `SameGLCentralCharacter F π₁ π₂`. `σ` is a `Whittaker.IsGeneric`
representation of `GL_(t+1)(F)` in universe `uW`. The conclusion is a conductor bound `A`,
depending on the fixed representations. For every quasicharacter `χ` with
`A ≤ multiplicativeConductor χ` there is a common rational function `G` such that both
`IsPadicSymmetricGammaFactor F ψ ν (π_i ⊗ χ ∘ det) σ G` relations hold. The universes
`uF, uV, uW` are independent.

## Proof

The proof is one application of Library reductions to Library theorems and to the essential
pair input proved in this development. Let `U = max uF uV uW`.

- `HighlyRamified.highlyRamifiedGammaStability_of_adjacentStep` (module
  `HighlyRamified.AdjacentInduction`) derives the statement from three inputs: the
  uniform rank-one statement in universes `(uF, U)` and `(uF, uV)`, and the adjacent-rank
  step `UniformPairStability (n + 1) n → MonomialTwistGamma n →
  UniformPairStability (n + 2) (n + 1)` for all `n`. The induction over ranks and the
  reduction of non-adjacent rank pairs to adjacent ones (Jacquet–Shalika 1985, printed
  p. 327) are inside this Library theorem.
- The uniform rank-one statement is the Library theorem
  `UniformRankOneTwist.uniformRankOneTwist` (Jacquet–Shalika 1985, Proposition (2.2),
  level-uniform form), used in both universe instances.
- `HighlyRamified.adjacentStep` (module `HighlyRamified.AdjacentStep`) proves the
  adjacent-rank step from three inputs:
  - the completeness lemma `WhittakerCompletenessStatement` (Jacquet–Shalika 1985,
    Lemma (3.2)), the Library theorem `Whittaker.CompletenessProof.whittakerCompleteness`;
  - the essential pair inputs `EssentialPairInput n` for all `n`. These are
    `HighlyRamified.essentialPairInput_of_uniformRankOne` (module
    `HighlyRamified.EssentialPairInputProof`) applied to `uniformRankOneTwist`;
  - the Kirillov shell input `KirillovShellInput`, the Library theorem
    `HighlyRamified.kirillovShellInput`.

The new mathematics is in the essential pair input, which needs only the uniform rank-one
statement. Its supporting modules, all in `Langlands/Representation/RankinSelberg/HighlyRamified/`,
are:

- `UnitarySpherical`: norm-one unramified principal series are generic, spherical, and
  have Jacquet's spherical function as normalized spherical test function.
- `UnitaryGamma`: gamma factors of highly ramified twists against all unramified principal
  series are explicit monomials (`exists_bound_principalSeriesGamma`).
- `ZeroCellLift`: Kirillov lifts of the zero-cell function, and their invariance under the
  integral row-mirabolic subgroup.
- `ZeroCellDualIntegral`: corank-one integrals of translated zero-cell vectors.
- `UnitarySeparation`: a vector with restriction invariance whose integrals against all
  norm-one spherical functions vanish is zero on the mirabolic subgroup.
- `EssentialDualIntegral`: the forward integral of the dual-translated zero-cell vector is
  a constant independent of the norm-one tuple.
- `EssentialLevel`: the zero-cell lift is fixed by `K_1(m)` under the monomial gamma
  hypothesis (`exists_levelFixed_zeroCellLift_of_unit_gamma`).
- `EssentialPairInputProof`: the essential pair input.

Each module has its own Markdown that describes its proof.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
