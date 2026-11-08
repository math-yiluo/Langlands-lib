# Level-uniform stability of pair gamma factors

Internal definitions for the proof of `HighlyRamifiedGammaStabilityStatement`.

The level predicate is the published `HasPrincipalLevelVector F π m`
(module `UniformRankOneTwistStatement`): `π` has a nonzero vector fixed by the
principal congruence subgroup `Conductor.principalLevelSubgroup F r m`
(`1 + ϖ^m M_(r+1)(O)`, the integral group at `m = 0`). Using it here lets the
level-uniform rank-one statement feed the induction directly.
`HasPrincipalLevelVector.mono` passes to deeper levels, by antitonicity of the
principal subgroups. `exists_hasPrincipalLevelVector`
gives a level for every smooth representation on a nontrivial space: a nonzero vector
is fixed by an open subgroup, which contains a positive principal level by the
published cofinality theorem `Conductor.principalLevelCofinal`.

`UniformPairStability r t` is the level-uniform form of Jacquet–Shalika 1985,
Proposition 4.1 (printed page 326), for candidate rank `r + 1` and test rank `t + 1`.
For every p-adic field, additive character of conductor exponent `0` and self-dual
Haar measure, and all levels `m, m'`, there is one bound `A` such that for every
quasicharacter `χ` of conductor exponent at least `A`, two gamma certificates
(`IsPadicSymmetricGammaFactor`) of `π₁ ⊗ χ∘det` and `π₂ ⊗ χ∘det` against `σ` are equal,
whenever `π₁, π₂, σ` are generic, `π₁, π₂` have level-`m` vectors and the same central
character (`SameGLCentralCharacter`), and `σ` has a level-`m'` vector. It is phrased
as uniqueness, so it asserts no existence. The uniformity is what the induction of
JS85 §4.4 needs (the source leaves it implicit); the bound may depend on the field,
`ψ`, the ranks and the two levels only.
