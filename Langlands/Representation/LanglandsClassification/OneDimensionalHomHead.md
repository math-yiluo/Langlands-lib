# Strong irreducible heads from a one-dimensional Hom space

Author: Worker 148, Task 5295 (`717df3ca-7a3c-40fc-a8b3-79617086393e`).
Module `Langlands.Representation.LanglandsClassification.OneDimensionalHomHead`,
namespace `Langlands.Classification`.

This internal algebraic helper implements the final kernel argument in David
Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, VII.4.2 (i), printed p.243 / PDF p.249. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The page was read as text and checked in the rendered original.

`quotientKernels_eq_of_finrank_one` considers representations `ρ`, `β`, `π₁`
and `π₂` of the same group on complex vector spaces in four independent carrier
universes. It assumes that `Hom(ρ, β)` has dimension one, that the maps
`qᵢ : ρ → πᵢ` are nonzero, and that the maps `jᵢ : πᵢ → β` are injective.
It proves equality of the actual linear kernels of `q₁` and `q₂`.
Surjectivity, irreducibility, smoothness and finite length are unnecessary
for this algebraic assertion.

The compositions `jᵢ qᵢ` are nonzero by injectivity of `jᵢ`. The
one-dimensionality hypothesis makes one composition a scalar multiple of the
other. The scalar is nonzero because the second composition is nonzero.
Evaluating this identity at a vector and using injectivity of the `jᵢ`
proves both implications between membership in the two kernels. This is
equality of kernels, including when the two quotient representations happen
to be isomorphic or identical.

`isIrreducibleHead_of_finrank_one` applies this comparison to any supplied
irreducible quotient of `ρ`, under the hypothesis that every irreducible
quotient in the source carrier universe embeds into `β`. Irreducibility
ensures that the quotient targets are nonzero; surjectivity therefore makes
their quotient maps nonzero. The theorem proves the published
`IsIrreducibleHead` relation, including its universal kernel equality.
It retains existence of an irreducible quotient as a premise.

`smooth_isIrreducibleHead_of_finrank_one` permits the embedding hypothesis
to quantify only over bundled smooth quotients. Every algebraic quotient
occurring in the published strong-head relation is smooth because its
quotient map is a surjective intertwiner from a smooth representation. The
proof bundles this inherited action on the same carrier and applies the
algebraic theorem. The comparison representation may lie in an independent
carrier universe.

`smoothHeadOfFinrankOne` is the actual construction entry. Given the same
Hom and embedding inputs and the existence of a smooth irreducible quotient,
it chooses such a quotient and returns it together with the proved
`IsIrreducibleHead` certificate. The choice is not claimed canonical; its
strong-head property includes the full kernel uniqueness.

For Renard's application, `ρ` is the normalized induction from a Langlands
triplet and `β` is induction from the opposite parabolic. The
one-dimensionality and quotient-embedding hypotheses must still be proved
for those actual inductions. This module establishes neither those inputs
nor existence of their irreducible quotients, and proves no component of the
unconditional Langlands classification on its own.
