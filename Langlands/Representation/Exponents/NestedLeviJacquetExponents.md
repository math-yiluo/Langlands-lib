# Actual nested Jacquet maps and exponent inheritance

Worker 17. This is internal support for the unitary Jacquet temperedness
argument. It uses the published actual Levi-parabolic transitivity and
extension results, without changing their statements or supplying their
structural proofs.

For three compatible supplied actual triples, `nestedLeviUnitaryJacquetMap`
applies the inner normalized Jacquet functor to the original inclusion of
the outer unitary Jacquet part, then composes with the inverse of the
published actual normalized transitivity isomorphism. The result is a
morphism from the inner Jacquet module of the outer unitary part into the
fine ambient Jacquet module, over the original common Levi's rational points.

The map is injective: the original unitary-part inclusion is injective, the
inner radical is a limit of compact subgroups over the supplied
nonarchimedean local field, and normalized Jacquet restriction consequently
preserves this injectivity. The final transitivity map is an isomorphism.

The exponent inheritance theorem tests both normalized Jacquet exponents
on the actual common Levi points. The restricted intertwiner carries a
nonzero vector in a uniform character space to a nonzero vector in the
same character space of the fine ambient module. Thus the exact same
character of the original fine split component is an ambient normalized
Jacquet exponent. This result requires no temperedness or compatible root
presentation, and proves no root-cone comparison.

`exists_ambient_isNormalizedJacquetExponent_of_unitary` removes the need
for a preselected ambient fine triple. It applies `leviParabolicExtension`
to the supplied outer and inner triples, evaluates the extension's
all-test subgroup inclusion and intersection equality at the original
field, and applies the same-character inheritance theorem. The resulting
ambient triple has the exact original inner Levi scheme, its exact
embedding into the ambient group, and its exact split component. No
presentation or exponent-cone comparison is asserted by this corollary.

All constructions and lemmas are derived from the Library's actual
normalized Jacquet functors, their compact-radical injectivity theorem,
actual extension and transitivity, and generalized character-space
transport. They retain the arbitrary field and carrier universes and the
supplied local-field and group topology assumptions.
