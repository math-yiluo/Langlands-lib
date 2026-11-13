# Rank-one conductors at intermediate fields of the common closure

Statement only. Worker 4803 introduces it as the arithmetic premise of
`SpectralConductor.spectralConductorRankOneReduction`. No proof is claimed here.

## Statement

`SpectralConductor.CommonClosureRankOneConductorStatement F`, for a p-adic field `F`,
says the following. Let `e` be a reciprocity family on the common closure of `F` with
`NormalizedReciprocity F e`. Let `L` be a finite intermediate field, `M` an actual
finite Galois subfield of the algebraic closure with `L ⊆ M`, and
`χ : W_L → ℂˣ` a continuous character of `W_L = weilSubgroup F L`. Let `ρ` be a
character of the inertia group of `M/L` that agrees with `χ` on inertia: for every
`w ∈ W_L` in Weil inertia and every `σ` in the inertia group of `M/L` that acts on
`M` as the Galois image of `w`, `ρ(σ) = χ(w)`. Then

`inertiaArtinConductor (M's canonical data) L (ρ on ℂ) = a(χ̃)`,

where the left side is the Library's Artin expression of `ρ` for the inertia group of
`M/L` acting on the integer ring of `M`, and `a(χ̃)` is the multiplicative conductor of
the field character `χ̃ = fieldCharacterEquiv F e L χ` attached to `χ` by the supplied
reciprocity component at `L`.

The algebra structures of `M` over `L` are the actual inclusion `L ⊆ M`, and the
`ℚ_p`-structure of `L` is that of `L.asPadicField`.

## Meaning and sources

The left side is the Artin conductor of the Galois character `ρ` of `M/L`
(Serre, *Local Fields*, VI §2, Proposition 2). The equality is the theorem that the
Artin conductor of a character equals the conductor of the corresponding character
of `L^×` under local class field theory. For a finite abelian extension it is the
upper-numbering reciprocity theorem: reciprocity carries `U_L^n` onto `G^n`
(Serre, *Local Fields*, XV §2, Theorem 1 and its Corollaries 2 and 3, printed
pp. 227–228, PDF pp. 232–233; the Remark there is the Hasse–Arf theorem). The
bracketed remark after Corollary 2 identifies the conductor with the Artin conductor
of a character (VI §2, Proposition 5 and its Corollary, printed p. 102, PDF p. 109).
Passing from `M/L` to the abelian extension cut out by `ρ` is inflation invariance
of the Artin conductor (VI §2, Proposition 3 and its Corollary, printed p. 101,
PDF p. 108).
The geometric versus arithmetic normalization of `e` does not matter, because `χ̃`
and its inverse have the same conductor.

## Relation to other Library statements

Proved in the Library: the comparison of a normalized family with standalone
geometric reciprocity at finite extensions (`commonClosureGeometricProof`) and the
finite upper reciprocity theorems
(`finiteUpperReciprocityTheorems_of_normCardinality finiteAbelianNormUnitImageCardinality`).
Unproved ingredients have tasks: `FiniteCharacterConductorTheorems` (finite abelian
conductor transport, Task 5738) and `FiniteGaloisConductorInflationStatement`
(Task 5739). The statement here is their transport to the intermediate fields of the
common closure and the supplied family.
