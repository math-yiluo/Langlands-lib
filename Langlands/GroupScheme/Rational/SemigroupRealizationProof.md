# Realization of the actual semigroup subgroup

Worker 1281 assembled this proof. Its geometric construction is by Workers
1281, 1324 and 1224. The structural proofs and their coordinate and Hopf-algebra
constructions are by Workers 1285, 1324, 1388, 1398, 1389 and 1419; the supporting
modules retain their individual attribution.

The theorem
`Langlands.GroupScheme.RelativeRoot.semigroupRealization` has exactly the type
`SemigroupRealizationStatement.{u}` from
`Langlands.GroupScheme.Rational.WeightSemigroupStatement`. It holds at every
universe `u`, over every field `k`, for a smooth affine group scheme `G`, a
split torus `S`, an actual automorphic action `b` of `S` on `G`, and every
additive subsemigroup `A` of the original character lattice of `S`. The ambient
group need not be connected. The semigroup may be empty or contain zero.

This is an internal composition of the geometric realization and the two
structural theorems. The source conclusions are CGP, *Pseudo-reductive Groups*,
second edition (2015), Proposition 3.3.6 and Lemma 3.3.8 with their proofs,
printed pp.109–112 (PDF pp.135–138), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. The implemented coordinate and
graded Hopf arguments are described in their supporting modules.

The proof supplies the six clauses of the unchanged statement:

1. `isSmoothConnectedClosed_semigroupSubgroup` constructs a smooth connected
   closed representative of the original `semigroupSubgroup b A`. Its
   construction takes the identity component of the actual coordinate
   subgroup. The exact tangent calculation makes its range an admissible
   generator. Conversely, equivariant augmentation pullback and affinization
   place every original generator in that range. These two containments
   identify the generated functor on every test scheme.
2. `semigroupSubgroup_isStable` gives stability under the original action `b`.
3. `hasLieImage_semigroupSubgroup` gives the exact selected ambient Lie image
   `semigroupWeightSpan b A`. The coordinate comparison uses the original
   action, actual dual-number points over every coefficient algebra, and
   the original character lattice.
4. If `0 ∉ A`, the representative adapter
   `semigroupSubgroup_unipotent_and_split_of_hasLieImage` applies the proved
   `torusActionUnipotence` and `torusActionSplitUnipotence`. Stability and the
   exact Lie image exclude the zero weight for the induced action on a
   smooth connected closed representative. The first structural theorem
   proves its representation-theoretic unipotence. The second constructs a
   finite Ga-series from a grading of its actual coordinate Hopf algebra,
   homogeneous unitriangular generating coefficients and primitive-function
   quotient steps. Representing-object uniqueness then transports both
   conclusions to every `H` and `j : H ⟶ G` representing the same functor.
   Thus the result retains `IsUnipotent H ∧ IsSplitUnipotent H` for every
   representative. The finite series has smooth connected closed normal
   steps, represented fppf one-dimensional vector-group quotients with
   natural coordinates on all tests, and a final group trivial on all tests.
5. `semigroupSubgroup_maximality` proves the full equivalence
   `actionWeightSupport b F ⊆ A ↔ F ≤ semigroupSubgroup b A` for every smooth
   connected stable closed subgroup functor `F`.
6. `eq_semigroupSubgroup_of_exact_lieImage` gives uniqueness among such
   subgroup functors with the exact selected Lie image. Its supporting
   argument first obtains an actual inclusion, then uses the full-Lie
   closed-subgroup theorem.

The first, second, third, fifth and sixth clauses impose no zero-exclusion
condition. The fourth clause alone uses `0 ∉ A`. No realization, representation,
unipotence or split-series conclusion is an extra premise of the theorem.
