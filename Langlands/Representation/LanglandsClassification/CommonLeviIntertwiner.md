# Nonzero intertwiners over a common actual Levi

This internal construction supplies the final algebraic step of Renard
VII.4.2(ii). It assumes equality of the two actual Levi images inside the
ambient rational points and a nonzero equivariant linear map. It does not
establish either premise from a common irreducible induced quotient.

## Actual groups and maps

Let `pⱼ : Pⱼ → G` and `lⱼ : Mⱼ → Pⱼ` be actual parabolic and rational
Levi inclusions over a topological field. Assume `G` is affine and
`pointImage (l₁ ≫ p₁) = pointImage (l₂ ≫ p₂)`. The existing
`commonLeviPointsEquiv` compares the rational Levi groups with their
original canonical topologies.

For actions `ρ₁` and `ρ₂` on complex vector spaces `V : Type v` and
`W : Type w`, `commonLeviIntertwiningMap` bundles a supplied linear map
`φ : V →ₗ[ℂ] W` whose equivariance holds whenever two Levi points have
the same ambient image. Its target is `ρ₂` pulled back along the actual
common-Levi group equivalence. Its underlying linear map is exactly `φ`.
The field, `V`, and `W` have independent universes.

## Implemented proof

`commonLeviEquivOfNonzero` additionally assumes that both actions are
irreducible and `φ ≠ 0`. Pullback along the surjective common-Levi group
equivalence preserves irreducibility, using the published
`CuspidalSupport.isIrreducible_comp_of_surjective`. Mathlib's
`Representation.IsIrreducible.bijective_or_eq_zero` makes the bundled
map bijective. `IntertwiningMap.ofBijective` then constructs the
representation equivalence. Its forward linear map is the original `φ`.

`exists_commonLeviEquiv_of_nonzero` expresses the result as a linear
equivalence equivariant on all pairs of original Levi points with equal
ambient images. It also records equality with the supplied linear map.

`commonLeviTwistEquivOfNonzero` and
`exists_commonLeviTwistEquiv_of_nonzero` apply the construction to
arbitrary unit-valued scalar character twists. Irreducibility of the
twists follows from the published `isIrreducible_twist_iff`. No finite
dimension, admissibility, or open-kernel condition is needed for these
algebraic assertions. For the smooth unramified twists in the published
classification statement, these are the same underlying actions and
carriers.

## Provenance and retained obligations

Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, VII.4.2(ii), printed p.246 / PDF p.252, concludes that
the nonzero common-Levi map is an isomorphism because both twists are
irreducible. The constructions here derive that step from published
actual-group transport and Mathlib's algebraic irreducibility lemmas.

The preceding geometric-lemma and spectral comparison, equality of
standard indices and real character norms, existence of the nonzero
common-Levi map, uniqueness of the induced quotient, and exhaustion
remain separate obligations. This module does not prove a complete
component of `LanglandsClassificationStatement`.
