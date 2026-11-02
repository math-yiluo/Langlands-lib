# Intrinsic action weights and all-test semigroup subgroup functors

These internal constructions implement the setting of CGP, *Pseudo-reductive
Groups*, second edition (2015), §3.3, especially Proposition 3.3.6 and the
cyclic filtration preceding Lemma 3.3.8 (printed pp.109–112; PDF pp.135–138).
The registered source is `conrad-gabber-prasad-2015-pseudo-reductive`. Related
KP statements are Propositions 2.11.12–14 and Theorem 2.11.15 (printed p.135;
PDF p.166), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`.
The registered KP corrections were checked at PDF p.25 and do not change
these source statements.

The base field and scheme universe are arbitrary. S is an actual commutative
group scheme; the constructions take an actual automorphic action on an
affine group scheme G. Splitness, smoothness, and connectedness needed for
source realization theorems are hypotheses of later targets, not fields
needed to construct the functors.

`actionEigenvectors b χ` tests the actual action on the dual-number identity
kernel after every coefficient extension A/k and against every A-point of S.
It uses the constant dual-number lift of that acting point and compares the
result with actual epsilon scaling by χ(s). `actionWeightSpace` is the linear
span of precisely those eigenvectors. The span agrees with the intrinsic
weight submodule because the torus action on this identity kernel is linear;
the equality with the Library's adjoint weight spaces for conjugation is a
separate target. No character is declared a weight merely by evaluation on
k-rational torus points. `actionWeightSupport b F` records the characters
having a nonzero vector in the intersection of that weight subspace and the
actual tangent image of F; it includes the zero character when it occurs.

`IsSemigroupGenerator b A F` requires that F already have a smooth connected
closed representative, that it be stable under the action on every test, and
that its tangent weight support lie in the additive subsemigroup A. The
canonical `semigroupSubgroup b A` is generated pointwise by the union of
all such subgroup functors. In this construction F ranges over all admissible
subgroups; it does not assume that a subgroup with the maximal desired Lie
algebra has already been realized. Its restriction proof uses subgroup closure
induction, preserving each generator by its own restriction law. The
`generator_le_semigroupSubgroup` and `semigroupSubgroup_mono` lemmas prove the
stated inclusion properties directly from this definition. Smooth closed
representability, the exact weight span, maximality, and uniqueness remain
source theorem targets. Once that maximal subgroup is realized, it is itself
among the generators, so this construction recovers its entire functor on
every test, including points not expressible as products from a fixed smaller
family of generators.

`cyclicTail a j` is the additive semigroup of n·a with n≥j and n>0. In
particular it is not a monoid closure inserting zero. For j≥1 this is CGP's
A_j. `weightFiltration b a j` uses that semigroup in the actual generated
functor. `weightFiltration_antitone` proves descending inclusions. Normality,
commutator bounds, vector quotients and unique equivariant linear structures
remain later targets.

`orderedMultiplication` is an actual morphism from the categorical finite
product of the representing group schemes to G, obtained by multiplying the
projected inclusion maps in the order 0,…,n−1. It is a morphism of schemes
over the base; it need not be a group homomorphism. No isomorphism or
surjectivity is claimed by the construction. `IsSolvableScheme` expresses
solvability by uniform termination of the point-group derived series on all
test schemes, which is the group-identity formulation of scheme-theoretic
solvability in the intended smooth connected affine setting.

The implemented closure, functoriality and multiplication constructions are
derived internal infrastructure for the cited sources. No substantive
semigroup realization or ordered-product theorem is proved here.
