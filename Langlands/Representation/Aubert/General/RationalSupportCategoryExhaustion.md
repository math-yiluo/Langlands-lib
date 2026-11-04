# Finite invariant spans for actual standard induction-Jacquet objects

This derived adapter by Worker 288 applies the finite-span image exhaustion to
the existing standard point subgroups of a connected reductive group scheme
over a nonarchimedean local field. The point group is literally
`RationalPoint k G.X`, with the canonical `pointTopology`. The index `K` is a
finite subset of the actual `SimpleRoot i ν`. The group and representation
universes match the rational support-stability target: `u` and
`max (u + 1) v`, with independent `u` and `v`.

`standardInductionJacquet_iSup_finiteSpanFunctorImage` proves that every actual
normalized induction-Jacquet object is the invariant sum of the images obtained
by applying that same functor to the finite invariant spans of its input. The
maps are the actual normalized functor maps of the existing inclusions.

The hypotheses are an affine group scheme, connected reductivity, a maximal
split torus, a generic cocharacter, the published
`StandardCocharacterStatement`, local compactness and the nonarchimedean group
structure at the canonical topology, and closedness of the chosen standard
unipotent subgroup. Compactness of the actual left quotient by the chosen
standard parabolic remains an explicit premise of this intermediate theorem.
It is not derived here. There are no length or admissibility hypotheses, and
the theorem includes empty simple-root sets and relative rank zero.

The proof applies `General.inductionJacquet_iSup_finiteSpanFunctorImage`. Its
compact-limit input is discharged by the published
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`,
using exactly the displayed standard-cocharacter, connected-reductivity,
maximal-splitness and genericity data. That published adapter compares the
actual standard unipotent subgroup with the dynamic unipotent subgroup, then
applies `BruhatTits.dynamicUnipotentCompactOpenContainment` and
`BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups`. No compact-limit
premise is added here.

The implemented proof is internal composition of those declarations. Its
functor-exhaustion dependency is described in the paired
`SupportCategoryExhaustion` module: finite double-coset covers for induction,
actual quotient representatives for Jacquet restriction, and compact-limit
injectivity. No classification, character independence, geometric lemma or
adjointness theorem is invoked by the new proof. Inherited imports include
the Library's general subquotient algebra and the standard rational-family
construction; this is not an assertion that their import closures are empty.

This theorem supplies an exhaustion step only. Support preservation on every
finitely generated supported input and actual parabolic quotient compactness
remain to be proved or supplied by exact published results before applying it
to `RationalSupportCategoryInductionJacquetStatement`.
