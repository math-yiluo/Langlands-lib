# Iwahori contraction for the full split valuation image

`Langlands.Hecke.IwahoriDominantCentralizerContractionStatement` relates
Renard's V.5.2(ii) basis clauses to the dominant centralizer generators of
V.5.3. It uses the actual `ParahoricBuildingData` of a connected reductive
group over a nonarchimedean local field, with its maximal split torus
`S → G` and represented centralizer `j : Z → G`. A generic cocharacter
`ν` selects the positive relative roots by positive pairing. The
empty-index groups are then the Levi and radical of the corresponding
minimal standard parabolic and the radical of its opposite, as in
Renard V.3.8 and V.3.12.

The subgroup `K` is normalized by the norm-kernel stabilizer
`B.apartment.specialCompactSubgroup x` of the supplied apartment point
`x`. It satisfies `StandardParabolicBasisMember` for a compatible split
component of the minimal standard parabolic. Both conditions apply to
the members of the V.5.2 simultaneous basis at a special vertex.

The additional hypothesis is `splitValuationImage B.centralizer.s = ⊤`.
The valuations on `Z(F)` from rational characters of `Z` are already
attained by points of `S(F)`. This holds when `S(F) → Z(F)` is surjective,
in particular when the split torus represents its own centralizer.

The conclusion gives weak contraction of `K ∩ N_∅` by every dominant
centralizer point, weak contraction of `K ∩ N̄_∅` by its inverse, and
normalization of `K ∩ M_∅` by the point. Restricting these assertions to
the dominant transversal gives (P) in
`IwahoriHeckeSubalgebraFinitenessStatement`.
[Finiteness statement](IwahoriHeckeSubalgebraFinitenessStatement.md)

The statement is derived from David Renard,
*Représentations des groupes réductifs p-adiques*, French edition of
9 July 2026, V.3.23 and V.5.2(ii)–V.5.3, printed pp. 117, 123–125,
PDF pp. 123, 129–131. When the split valuation image is full, each
dominant centralizer point is a product of a dominant uniformizer
section element and a point of the centralizer norm kernel. V.5.2(ii)
applies to the section element. The norm kernel maps into the
norm-kernel stabilizer of `x`, and the centralizer normalizes the minimal
standard Levi and both radicals.
[Centralizer action](../../Geometry/Building/KPCentralizerCompatibility.md)
