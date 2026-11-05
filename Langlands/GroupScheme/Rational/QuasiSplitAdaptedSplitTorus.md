# Maximal split tori adapted to a dynamic solvable subgroup

This is an internal construction for the quasi-split centralizer proof. Over
an arbitrary field, every cocharacter of an affine group locally of finite
type factors through an actual maximal split torus. The proof takes its
closed split-torus image and extends that image by the published maximal
split extension theorem. The centralizer of the resulting torus is contained
in the dynamic centralizer, hence in the dynamic parabolic, of the original
cocharacter. These are inclusions of subgroup functors on every test scheme.

`MaximalSplitTorusThroughCocharacter` packages the actual torus, its inclusion,
its maximal split property, the lifting cocharacter, its composition equality,
and the centralizer containment. The noncomputable definition
`maximalSplitTorusThroughCocharacter` chooses such data from the existence
theorem. It requires only affineness and local finite type of the ambient
group over the given field.

When a supplied subgroup represents that dynamic parabolic, the construction
retains containment in its exact range. A separate lemma factors any
representative of a whole-torus centralizer through a supplied solvable
subgroup and proves that representative solvable by monicity.

The last theorem applies the construction to a given geometric Borel of a
connected reductive group. It explicitly assumes
`ParabolicDynamicStatement.{u}` to obtain the required ground-field
cocharacter. It does not prove that structural statement, reductivity of
centralizers, ordinary maximal split torus conjugacy, or the unconditional
`QuasiSplitMaximalTorusCentralizerStatement`.

The provenance is the composition of existing image factorization, maximal
split extension, dynamic centralizer containment, and represented-subgroup
factorization results. No additional assertion from the literature is used.
