# Maximal-torus conjugacy for compact real semisimple groups

`Langlands.GroupScheme.RealCompactMaximalTorusConjugacyStatement : Prop`
is the compact-form version of Cartan's maximal-torus conjugacy theorem,
with no universe parameters. The module defines this proposition and
does not prove it.

Let `G` be a semisimple group scheme over `Spec ℝ`, and give its actual
point group `rationalPoints G` the topology
`Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology ℝ G.X`.
The affine instances in this expression are supplied by
`hG.isConnectedReductive.isAffineHom`. The hypothesis is compactness
of the whole real point group in this topology.

For every two maximal torus embeddings `j : T.toGrp ⟶ G` and
`j' : T'.toGrp ⟶ G`, the conclusion supplies a real point `g` such that
`SubgroupFunctor.range (j ≫ (G.innerIso g).hom) =
SubgroupFunctor.range j'`. The inner automorphism acts by `x ↦ g x g⁻¹`.
Equality is equality of subgroup functors on every test scheme over
`Spec ℝ`, so the conclusion identifies the algebraic subgroups. It is
stronger than equality of their real-point sets alone.

`IsMaximalTorus` asserts that the source is a torus, the embedding is
closed, and there is no proper larger torus through which it factors.
The precise predicates and the all-test interpretation are unchanged
from
[`RealAnisotropicMaximalTorusConjugacyStatement`](RealAnisotropicMaximalTorusConjugacyStatement.md).
There is no separate hypothesis of analytic connectedness, a choice of
matrix realization, or a supplied complex conjugator.

## Source correspondence

Kazuo Suzuki, *A note on a theorem of E. Cartan*, Tohoku Mathematical
Journal 23 (1971), 17–20, source ID `suzuki-1971-cartan`, readable PDF
SHA-256 `208820540ee03a5bd60b7d8cf5065c691a21d60013fa497a008882108da99602`.
The relevant statement is Theorem 2 on printed p. 19, with its proof
continuing on p. 20 (PDF pages 3–4). The publisher gives DOI
`10.2748/tmj/1178242683`; the initially registered citation metadata
contains a DOI typo, but its PDF and URL identify this article.

The theorem on p. 19 assumes a real semisimple algebraic group of compact
form and concludes conjugacy over the real numbers of its real maximal
tori. The proof works with algebraic tori, complex conjugation and a
real conjugating element; its conclusion is algebraic conjugacy. We
encode compact form by compactness of the real-point group in the
canonical affine evaluation topology. Suzuki's discussion on pp. 17–18
identifies that compactness interpretation. The theorem's algebraic
subgroup equality becomes equality of full subgroup functors in Lean.
This is a derived encoding of that theorem.

The introduction's version of Theorem 2 on p. 17 omits the compact-form
hypothesis. The present statement follows the compact-form version on
p. 19. In particular it does not assert conjugacy for the split group
`SL₂/ℝ`, whose split and circle maximal tori are not real conjugate.

## Role in the anisotropic target

The statement intentionally uses the conclusion of the published
`RealAnisotropicMaximalTorusConjugacyStatement` verbatim. Applying
[`RealAnisotropicPointsCompactnessStatement`](RealAnisotropicPointsCompactnessStatement.md)
to its anisotropy premise supplies the compactness hypothesis here.
The original target then follows without changing any of its
hypotheses or its subgroup-functor conclusion.
