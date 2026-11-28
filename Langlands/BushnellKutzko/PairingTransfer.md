# Transfer by characters of a finite quotient

`Langlands.Jacquet.FiniteQuotientCharacterTransferStatement` concerns a complex representation of a group `G`, subgroups `K` and `M`, a character `ϑ` of `K`, and a surjection `p` from `K` to a finite abelian group `Y`. An additive group acts through a homomorphism to `G`. Its elements normalize `K` and `M`, conjugate trivially on `Y`, and fix the restriction of `ϑ` to the kernel of `p`.

`quotientConjRatios` descends `ϑ(k) / ϑ(gkg⁻¹)` to `Y`. The quotient action ensures that composing conjugations multiplies their ratios. If the resulting family surjects onto the complex character group of `Y`, then a vector transforming through `ϑ` on the kernel of `p` outside the `M`-relations yields a `ϑ`-isotypic vector for `K` outside those relations.

`exists_isotypic_not_mem_relations_of_quotientConjRatios` uses the finite double dual to evaluate the ratio characters at `p(k)`. Orthogonality of the resulting characters gives the scalar sums required by `exists_isotypic_not_mem_relations`. Each conjugation preserves the `M`-relations, so a nonzero class in the quotient by the relations survives in some conjugated isotypic component.

This formulation isolates the vector transfer of Bushnell–Kutzko (8.2.14) and the transitivity mechanism applied in (8.2.26). The book derives transitivity from a stabilizer index, while this formulation takes surjectivity of the conjugation ratios as a hypothesis.
