# One actual norm-kernel level for all specified positive generators

This internal geometric adapter constructs `NormKernelCompressionLevel` from a
supplied `SimultaneousStandardBasisAt i ν K0`. It does not prove existence of
that simultaneous basis or the final uniform coefficient-support theorem.
The field is any nonarchimedean local field; no characteristic or positive-rank
restriction is imposed. This geometry has no representation-carrier parameter.

The group is the actual `Plancherel.rationalCommonNormKernel G`, with the topology
inherited from the canonical `pointTopology` on the actual rational points of
`G`. The positive homomorphism and its coordinate generators are exactly those
of `NormKernelFundamentalCocharacters`; all directions use its one canonical
field uniformizer. `normKernelStandardOpposite I` is the inverse image of the
actual opposite standard radical for `I` under the kernel inclusion. The upper
radicals and Levis are the existing `normKernelUnipotent` and `normKernelLevi`,
also literal inverse images under that inclusion.

A level record contains a compact open subgroup below the prescribed open
subgroup `U`. The intersection of the supplied ambient `K0` with the kernel
normalizes this level. At this same level every specified generator has an
`IsIwahoriContraction` for its complementary-root face. Every positive orthant
element preserves the level intersection with every standard upper radical
in the direction needed for compression. The record also retains the ordered
opposite-radical, Levi, radical factorization for the minimal standard face,
whole-orthant membership in `Hecke.iwahoriPositiveMonoid` for that face, and
forward conjugation preservation of the level's minimal Levi intersection.
No admissibility, coefficient or support premise enters the record.

`nonempty_normKernelCompressionLevel` assumes connected reductivity, a maximal
split torus, a generic cocharacter, the published standard-cocharacter
statement, the relative-root-system realization, local compactness and the
nonarchimedean group property of the canonical ambient point topology, and the
supplied simultaneous basis. The finite type of simple-root labels is explicit.
It first maps `U` into the ambient group, using the proved openness of the actual
norm kernel. Cofinality chooses one member `K` of the supplied basis inside
this ambient open subgroup. Pullback gives the compact open kernel level;
compactness follows because its inclusion image is exactly the compact `K`.
Normality of `K` in `K0` gives the recorded normalizer inclusion after pullback.

For each complementary face, the proof reuses
`RationalCoefficientDecay.uniformizer_mem_chambers`. The diagonal root
pairings of the prescribed cocharacters give weak-chamber membership and
strict positivity outside the face. The simultaneous basis clauses then give
contraction for that same specified uniformizer value, and
`IsIwahoriContraction.comap_of_le` restricts it to the actual kernel. No new
choice of a contracting element occurs.

The minimal-face weak chamber contains every orthant value, because its simple
root pairings are natural multiples of positive diagonal pairings. Its basis
clauses supply the three positive-monoid conditions, forward Levi preservation
and ordered factorization. To extend the upper bound to every standard radical,
`unipotent_le_minimal_of_standard` uses the relative-root realization to obtain
root negation, the proved sign implications for nested standard faces, and
`Dynamic.unipotent_le_of_positive_rootSigns`. Testing against each minimal
standard cocharacter proves containment of the actual standard radical in the
minimal one. Thus no standard-parabolic-order theorem is added as a premise.

The provenance is internal: this module combines the published simultaneous
basis predicates, actual-root sign comparison, uniformizer chamber lemmas and
open-subgroup transport. The new content is their assembly at one arbitrarily
small level of the actual norm kernel, retaining all specified generators and
all the recorded orthant bounds. Simultaneous-basis existence, a finite Cartan
cover, representation-theoretic bounds and the final common support remain
separate obligations, including when the root system is empty.
