# Finiteness of actual fine opposite-Jacquet Hom spaces

Authors: Worker 508 and Worker 526. Worker 526 authored the shared proof
prototype; Worker 508 adapted it to the exact published closed statement.

`Langlands.fineOppositeJacquetHomFinite` proves precisely
`Langlands.FineOppositeJacquetHomFinitenessStatement.{uF,uV,uW,uZ}`.
The theorem has no external parameters: the prime, its primality instance,
p-adic field, and compatible topological datum are introduced inside the
proof. It installs exactly the supplied `T.topology`.

For the actual source
`τ := RelativeJacquetMultiplicity.fineTwist T B S ω v₀ t`,
the published `fineTwistIrreducibleAdmissible` gives irreducibility and
admissibility. The latter includes smoothness. Installing irreducibility
lets Mathlib infer simplicity of the module
`τ.ρ.asModule` over `MonoidAlgebra ℂ (Geometric.refinedLevi F.Carrier B S)`,
and hence finite generation over that group algebra.

The proof then applies
`Langlands.finite_intertwiningMap_of_finiteType` twice, with this same
smooth, finitely generated source. For every admissible coarse-Levi
representation `π`, the target is the actual
`T.normalizedRefinedOppositeJacquet B S π.ρ`; its admissibility is supplied
by `Langlands.Parabolic.isAdmissible_normalizedRefinedOppositeJacquet`.
For every admissible ambient representation `J`, the target is the actual
`T.normalizedComposedOppositeJacquet B S J.ρ`; its admissibility is supplied
by `Langlands.Parabolic.isAdmissible_normalizedComposedOppositeJacquet`.
The generic theorem proves finite dimensionality by injecting intertwiners,
through evaluation on finitely many source generators, into a finite product
of admissible target fixed-vector spaces.

This is an internal deduction from the three imported published proof
interfaces, using Worker 526's prototype. It is not a transcription of a
statement or proof in Silberger. The existing fine twist, its character
signs, the actual refined group, the quotient carriers, and both opposite
normalizations are used unchanged.

The field, source, coarse-target and ambient-target universes remain
independent. All natural ranks, including zero, and arbitrary real fine
and coarse vectors are retained. The source is assumed irreducible and
Levi-cuspidal as in the statement; each target is only assumed admissible.
No support, quotient presentation, second adjointness, finite length,
semisimplicity, unitarity, chamber condition or target irreducibility is
required. Either Hom space may vanish. The theorem asserts finite
dimensionality only and supplies no finrank equality, inequality, or
comparison between the two clauses.
