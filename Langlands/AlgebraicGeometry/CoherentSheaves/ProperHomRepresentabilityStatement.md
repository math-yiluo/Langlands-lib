# Affine representation of actual coherent-family morphisms

`ProperHomRepresentabilityStatement.{u}` asserts that the actual Hom
presheaf of any two coherent families over any test scheme is represented
by an actual scheme affine and locally of finite presentation over that
test scheme, when the ambient morphism is proper and locally of finite
presentation. This module states the proposition and gives no proof.

The representation is a natural isomorphism with the explicitly lifted
functor of points on the entire slice `Over T.left`. Thus it includes
actual maps of the ordinary pulled-back module sheaves and their coherent
restrictions on arbitrary test schemes. It is stronger than a bijection
of geometric points. Affineness supplies quasi-compactness and separatedness,
so affine local finite presentation is finite presentation. Neither the
base nor any test scheme is assumed noetherian or quasi-compact.

## Source derivation

This is a derived scheme-family specialization of Stacks Project,
Proposition 99.3.10 (Tag 08K6), Section 99.3 (Tag 08JS). The full section,
proofs and two typo-only comments were read in the retained original
`08JS.html` in source `stacks-hom-functor-08js-2026-11-02`, folder SHA-256
`2d60cda5ae13d9daa5c318ca4cd199e47a3a00b39f5062492b2207f7b56432c4`.
No project errata note was found in the supplied public tree.

Apply that proposition to the projection `T ×_S X → T` and the underlying
modules of `M` and `N`. The projection is proper and locally of finite
presentation by base change. A proper morphism is quasi-compact and
separated, so the projection is of finite presentation, as the source
requires. Both module sheaves are finitely presented and flat over `T` by
the actual family conditions. The source requires relative flatness only
of the target; the additional source flatness here is part of the existing
family definition. `FamilyGroupoid.hasProperSupport` supplies proper
scheme-theoretic support for the target from properness of the ambient
morphism. Every source hypothesis is therefore accounted for without an
extra geometric or rank condition.

The source conclusion is an algebraic space affine of finite presentation
over `T`. An algebraic space affine over a scheme is a scheme. Establishing
this passage, the actual full-slice natural comparison, and the geometric
representability theorem remain proof obligations. The Hom presheaf itself
is the imported construction, not a replacement by geometric points or a
formal matrix model.

## Scope and dependency boundary

This statement is the proper-Hom prerequisite used in the inverse-equation
proof of proper-Isom representability (Stacks Proposition 99.4.3). It makes
no claim of proving either representability result. The original proof of
99.3.10 uses noetherian approximation and the perfect-complex argument in
Lemma 99.3.9 for general finitely presented sheaves. No two-term resolution,
ambient flatness, projectivity, or noetherian hypothesis is added here.
