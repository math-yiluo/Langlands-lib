# Compact irreducibles and the semisimple compact subcategory

Worker 141 proves the first two conjuncts of
`CompactBlockDecompositionStatements`, with independent group universe `u`
and carrier universe `v`, in a separate module.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, IV.1.6, printed
pages 94–95 / PDF pages 100–101. Both pages were read. The source uses the
compact isotypic projector to reduce projectivity and injectivity to the
semisimple isotypic category. This implementation uses the already published
projectivity theorem and smooth contragredient duality instead.

A compact irreducible is admissible by the published compact fixed-vector
argument. Its smooth contragredient is irreducible and compact, so the
published projectivity theorem applies to it. A monomorphism becomes a
surjection under the smooth contragredient, using cofinal compact open
subgroups. Lift the dual of the given map into the compact irreducible, then
recover the desired extension by the published Hom duality theorem. Bijective
bidual evaluation of the admissible target makes the recovered extension
identity faithful. This proves `injective_of_irreducible_compactCoefficients`.
Together with published projectivity this proves
`compactProjectiveInjective : CompactProjectiveInjectiveStatement`.

For the compact subcategory, the published exhaustion theorem proves that an
object all of whose irreducible subquotients are compact has compact
coefficients itself. Published semisimplicity therefore applies. The compact
constituent predicate is definitionally the general irreducible-subquotient
Serre predicate. Its full-subcategory inclusion preserves finite limits and
finite colimits, hence monomorphisms and epimorphisms. The fully faithful
inclusion then transfers ambient projectivity and injectivity of the stated
irreducible objects to that subcategory. This proves
`compactPartSemisimple : CompactPartSemisimpleStatement`.

No published statement or imported dependency is changed, and neither theorem
adds a hypothesis. The ambient injectivity helper needs only a left Haar
measure; the two exact statements retain all their published assumptions.
