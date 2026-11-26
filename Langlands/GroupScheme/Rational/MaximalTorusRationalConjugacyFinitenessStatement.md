# Finiteness of rational conjugacy classes of maximal tori

`Langlands.GroupScheme.HasFiniteMaximalTorusConjugacyClasses G` asserts that
a finite family of maximal torus embeddings into \(G\) meets every rational
conjugacy class of maximal tori. Each embedding is a closed subgroup over
the ground field and satisfies `IsMaximalTorus`. The conjugacy relation
`SubgroupConjugate` uses a rational point of \(G\) and an isomorphism of the
two torus domains over the ground field. A finite family meeting every
class gives finiteness of the set of classes, with repetitions allowed in
the family.

`Langlands.GroupScheme.MaximalTorusRationalConjugacyFinitenessStatement`
asserts this property for every connected reductive group over a
nonarchimedean local field of characteristic zero. The maximal tori
include tori that require a field extension to split.

This is the characteristic-zero finiteness assertion in David Renard,
*Représentations des groupes réductifs \(p\)-adiques*, 9 July 2026,
§ V.2.1, printed p. 104 (PDF p. 110). The section refers to Springer,
*Linear Algebraic Groups*, second edition, bibliography item [42].
