# Splitting the twisted spectrum at an unramified orbit

Fix an admissible irreducible representation `τ` of a group `G`, a twisting
automorphism `θ`, and a measure `μ`. The following subspaces of `Distribution G`
use the Library's twisted distributions of irreducible admissible pairs in
a fixed carrier universe.

- `twistedOrbitSpan μ θ τ` uses the representations equivalent to invariant
  unramified twists of `τ`. The identity twist puts `τ` in its own orbit.
  The composition and inversion laws for `twist` and `twistEquiv` give
  stability of membership under further invariant unramified twists.
- `twistedOtherEssentiallyTemperedSpan μ θ τ` uses the representations
  outside the orbit that become tempered after an invariant unramified
  twist. A tempered representation outside the orbit qualifies by using
  the identity character.
- `twistedInvisibleSpan μ θ J` uses the representations with zero space
  of `J`-fixed vectors.

For `GL_n(E)`, `twistedPseudoCoefficientComplementSpan σ μ τ J` is the sum
of the other essentially tempered span, the span of twisted distributions
of proper inductions, and the span with zero `J`-fixed space.

`TwistedPseudoCoefficientSpectrumSplittingStatement.{u,v,z}` is a
structural proposition in ranks at least two. For each σ-discrete series
and Haar measure, it asks for a compact open subgroup `J` such that the
orbit span and the complementary span are disjoint and their sum contains
every irreducible admissible twisted distribution. Disjointness gives the
extension of evaluation on the orbit by zero on the complementary span.
Containment of the irreducible characters supplies a decomposition for each
one-block inducing pair, which is then twisted as the character varies.

This derived formulation isolates the spanning and separation implicit in
Henniart–Lemaire (2011), II.5.10, Proposition and Corollaire, pp. 108–109,
II.5.11, Lemme 2, pp. 111–112, and the two cases of II.5.13, p. 114. The
source uses a basis of twisted Langlands standard classes and the support
in one Bernstein component. The Lean proposition packages the required
consequences for spans of actual distributions and the compact domination
condition. The spectrum splitting is a premise of the spectral construction.
