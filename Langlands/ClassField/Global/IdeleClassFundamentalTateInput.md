# Tate cup isomorphisms for global fundamental classes

Worker 1736 derives the subgroup conditions and Tate cup bijectivity for the
actual relative idele-class representation. This is an internal prerequisite
of transfer reciprocity; the transfer assertion itself is not proved here.

For number fields `F E : Type u` with `[Algebra F E] [IsGalois F E]`,
`ideleClassFixedFieldCohomologyIso F E H n` reindexes cohomology along the
Galois equivalence between a subgroup `H` of `Gal(E/F)` and the Galois group
of `E` over its fixed field. Its coefficient equivalence is the identity
on the additive wrapper of the actual idele classes of `E`.
`ideleClassFixedFieldCohomologyIso_restriction` proves that relative
restriction followed by this equivalence is subgroup restriction.

Given a class family `c` satisfying `FundamentalClass.Generates` and
`FundamentalClass.Restriction`, `fundamentalClass_subgroupConditions` proves
that, for every subgroup `H`, its first cohomology vanishes, its second
cohomology has cardinality `Nat.card H`, and the restriction of `c F E`
generates its second cohomology. The first claim uses the published global
theorem `ideleClassH1Vanishing` at the fixed field. For the other claims,
restriction compatibility identifies the restricted class with the
family's fixed-field class. That class generates and has additive order
`[E : fixedField H] = Nat.card H`.

`fundamentalClass_tateCup_bijective` applies the published theorem
`Langlands.Tate.tateCupIsomorphism` to these conditions on all Sylow
subgroups. It proves bijectivity of the Library's actual integral cup map
in every integer Tate degree. The finite enumeration of `Gal(E/F)` is
constructed with `Fintype.ofFinite`, and the universe `u` is retained.
No local normalization or inflation assumption is needed for this helper.

The provenance is an internal specialization of the Library's proved Tate
theorem, global first-cohomology vanishing and fixed-field Galois
correspondence. The general cup theorem's source correspondence and
implemented dimension-shifting proof are documented in
`Langlands/Cohomology/Tate/TateTheoremProof.md`. This helper does not
identify the kernel or cokernel of a group extension's transfer.
