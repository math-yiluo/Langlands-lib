# Reflection at the canonical residue cardinality

Definition: Worker 7. Coercion theorem: Worker 31. Integration: Integrator.

`Langlands.LocalFactor.residueReflection F` is the unit `q⁻¹`, where `q` is
`F.canonicalTopologicalData.residueCardinality` for `F : PadicField p`.
It specializes `WeilDeligne.reflectionScale` with the published proof that
`q > 1`. At the rational variable `X = q^(-s)`, the substitution
`X ↦ q⁻¹/X` represents `s ↦ 1-s`.

The definition is moved unchanged from
`Correspondence/SupercuspidalGammaCompatibility`, where it was named
`Langlands.Correspondence.residueReflection`. The reviewed duplicate
`RankinSelberg.padicGammaReflectionScale` is replaced by this same declaration.
Both definitions applied the same `WeilDeligne.reflectionScale` to the same
residue cardinality; their positivity proofs are propositionally irrelevant.
The shared location lets both consumers import the scalar without importing
correspondence predicates into representation theory.

`coe_residueReflection` is the renamed coercion theorem from
`Representation/RankinSelberg/LanglandsGammaFactor`. It unfolds the same scale
and uses `WeilDeligne.coe_reflectionScale` to identify its complex value with
`(q : ℂ)⁻¹`. This module introduces no factor comparison or existence assertion.
