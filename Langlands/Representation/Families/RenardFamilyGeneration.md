# Finite generation from compact-open constituent detection

This internal supporting unit for Renard VI.10.7, Variant, proves
`Langlands.Renard.AlgebraicFamily.CoefficientFamilyGenerationStatement`.
It does not prove the full finite-type characterization or assert existence
of a uniform compact-open detector.

For a topological group `G`, a commutative complex algebra `B`, and a smooth
`B`-linear representation `ρ` on a compatible complex vector space `V`, fix
a compact open subgroup `K`. Assume that every irreducible actual subquotient
of the underlying smooth complex representation has a nonzero `K`-fixed
vector. If the `K`-fixed space is contained in the `B`-span of the categorical
centre orbits of finitely many vectors `s j`, then those same vectors generate
`V` over `B[G]`. The vectors need not themselves be fixed. No flatness,
Noetherian, reducedness or reductive-group premise is used.

The implemented proof takes the `B[G]`-span `N` of the `s j` and views it as
an actual complex subrepresentation `S`. Naturality of an element of
`CatCenter` along the inclusion of `S` shows that `S` contains each centre
translate of each `s j`. Its coefficient stability and the spanning
hypothesis therefore give `V^K ⊆ S`. The published
`fixedVector_of_irreducible_subquotient_detection` and
`fixedVectors_generate_subquotients_of_detection` imply `S = V`.
Consequently `N` is the whole group-algebra module. The finite-generation
wrapper uses that the range of a map from `Fin n` is finite.

`center_mem_subrepresentation` isolates the naturality argument.
`groupAlgebra_span_eq_top_of_center_span_and_detection` supplies the
explicit span equality, and `coefficientFamilyGeneration` proves the named
proposition without further hypotheses.

Provenance: these are derived algebraic supporting lemmas for David Renard,
*Représentations des groupes réductifs p-adiques*, version dated 9 July 2026,
VI.10.7, Variant (printed p.217 / PDF p.223), with the definition of
`(G, B)`-modules in VI.8.1 (printed p.187 / PDF p.193). The source is
registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard states the Variant without its proof. This unit implements the
generation step through the Library's unconditional detection consequences;
it is not attributed to a separately numbered assertion in the source.
