# Renard III.3.2: singleton sheaves and smooth representations

This is an unproved closed proposition target for David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, III.3.2, printed p.84 / PDF p.90, the singleton example in the
opening category paragraph and the following compact-section functor.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original page was read directly.

`Langlands.Sheaf.Renard.SingletonEquivalence.Statement` quantifies over every
topological group `G : Type uG` with the explicit predicate
`IsLocallyProfinite G`, retaining Renard's Hausdorff compact-open basis.
The group universe is independent of the original universe-zero complex
coefficient and section carriers. No finite-dimensionality assumption is
made. Countability at infinity occurs later in Renard's transitive-action
paragraph; it is not required for this singleton assertion.

The two functors are exactly the published
`SectionActions.gammaC G PUnit` and
`SectionActions.SingletonSheaves.functor G`. The latter is the original
full locally constant complex coefficient sheaf on the actual singleton,
with its existing smooth action. The former uses all original compact
sections. All their existing sheaf, representation and morphism objects
are retained.

The target requires invertibility of the exact published natural
transformations `SingletonSheaves.unit G` and `SingletonSheaves.counit G`.
The unit sends an original local section to its original extension to the
whole singleton, regarded as a compact coefficient section. The counit is
literal evaluation of the original global coefficient section at the
singleton point. Their definitions and application formulas are already
published; no arbitrary comparison is supplied as a hypothesis.

The two subsequent equations are the triangle laws for these exact maps
and functors. The final two conjuncts assert that the actual functors are
equivalences. Together this is the source's singleton identification with
specific existing comparison maps, rather than the bare existence of
some equivalence between replacement categories. The triangle equations
are an internal precise expression of the chosen canonical identification;
Renard does not separately display them.

This proposition is not proved here. It concerns only the singleton
example, not an arbitrary transitive homogeneous quotient, the induction
sheaf, or any III.3.1 fibre or distribution assertion.
