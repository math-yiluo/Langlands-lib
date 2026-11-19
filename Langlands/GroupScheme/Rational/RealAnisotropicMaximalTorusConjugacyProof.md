# Conjugacy of maximal tori in anisotropic real semisimple groups

Worker 862.

`Langlands.GroupScheme.realAnisotropicMaximalTorusConjugacy` proves
`Langlands.GroupScheme.RealAnisotropicMaximalTorusConjugacyStatement`,
the Library statement of Cartan's theorem. For any two maximal torus
embeddings in an anisotropic semisimple group scheme over `ℝ`, it gives
a real point whose inner automorphism carries the first subgroup onto
the second as a subgroup functor on every test scheme over `ℝ`.
[Statement and source correspondence](RealAnisotropicMaximalTorusConjugacyStatement.md)

Semisimplicity supplies connected reductivity and hence the affine
instances. The first conjunct of `realAnisotropicCompactConnected` gives
compactness of `RingPoint ℝ G.X ℝ` in its evaluation topology.
The inverse of `rationalPointHomeomorph ℝ G.X` transfers compactness
to the real sections `rationalPoints G` with `rationalPointTopology ℝ G.X`.
[Anisotropic compactness proof](RealAnisotropicCompactConnectedProof.md)

`isCompact_univ` supplies the compactness premise of
`realCompactMaximalTorusConjugacy` for the same group and the same
semisimplicity proof. Its conclusion supplies the real conjugator and
the required equality of `SubgroupFunctor.range`.
[Compact real conjugacy proof](RealCompactMaximalTorusConjugacyProof.md)

The target is Theorem 25.57 on printed p. 561 of Milne's *Algebraic Groups*
(2017), registered as `milne-2017-algebraic-groups`. Milne refers to Suzuki's
Theorem 2. The Lean proof combines the published anisotropic compactness
theorem with the published compact-form conjugacy theorem.
