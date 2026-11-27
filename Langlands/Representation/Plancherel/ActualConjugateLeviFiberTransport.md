# Canonical target coefficient fibers for compositions

This module supplies the fiber identifications for the composition and
identity relations of Waldspurger V.3.2. It works with the actual rational
conjugating elements. The equality of the once-conjugated and twice-conjugated
Levi anchor cocharacters uses `GroupScheme.innerIso_mul_hom` in the order
in which the acted-on representation is first conjugated by `t`, then `s`.
The cocharacter for the identity arrow is identified using
`GroupScheme.innerIso_one_hom`. Its inverse-conjugation counterpart follows
from the multiplication and identity equalities.

`multiplicationTarget` transports the presentation of the direct target
parabolic through that cocharacter equality, keeping its cocharacter and
Iwasawa factorization; `identityTarget` and `inverseTarget` do the same for
the identity point and for the return along `g⁻¹`.

## Same-carrier comparisons

For subgroups `M`, `N₁`, `N₂`, `N` of one topological group and a smooth
representation `B` of `M`, the three comparisons below have the identity linear
map of the carrier of `B`; they intertwine because the pullback isomorphisms
agree pointwise and the twisting characters correspond. Each comparison involves
two characters with values in `ℂˣ`, and it takes as hypotheses that both have
open kernels: these openness proofs are what make the two twists smooth
representations.

- `twistPullbackEquiv`: for characters `α` of `M` and `β` of `N` with open
  kernels, from the twist by `β` of the pullback of `B` along `e` to the
  pullback along `e'` of the twist of `B` by `α`, when `e n = e' n` and
  `β n = α (e' n)`.
- `twistPullbackPullbackEquiv`: for characters `α` of `M` and `β` of `N` with
  open kernels, from the twist by `β` of the pullback of `B` along `e₁` and
  then `e₂` to the pullback along `e` of the twist of `B` by `α`, when
  `e₁ (e₂ n) = e n` and `β n = α (e n)`.
- `twistPullbackPullbackTwistEquiv`: for characters `β` of `N` and `δ` of `N₂`
  with open kernels, from the twist by `β` of the pullback of `B` along `e₁`
  and then `e₂` to the pullback along `e₃` of the twist by `δ` of the pullback
  of `B` along `e₄`, when `e₁ (e₂ n) = e₄ (e₃ n)` and `β n = δ (e₃ n)`.

In the three inducing equivalences below, the openness hypotheses are
`unramifiedCharacter_isOpen_ker` for the two literal Levi characters.

The theorems `twistPullbackEquiv_linear_heq`,
`twistPullbackPullbackEquiv_linear_heq` and
`twistPullbackPullbackTwistEquiv_linear_heq` record that their linear
equivalences are `LinearEquiv.refl ℂ B`.

## Anchor change

`anchorMembership` presents the Levi of an anchor as the conjugate by the
identity point of the Levi of an equal anchor; `changeAnchor_parabolicMembership`
and `changeAnchor_radicalMembership` do the same for the parabolic and its
unipotent radical under `changeAnchor`. `fiberDecomposition` and
`fiberRadicalClosed` are the semidirect decomposition of the parabolic of a
presentation over its literal Levi and the closedness of its unipotent
radical, and `radicalUnimodular` is
`DynamicOppositeCanonicalScalar.radical_unimodular` stated with the topology
and Haar structures used for the coefficient fibers here.

For an equality `h : χ = φ` of anchors, a presentation `P` over `χ`, a
representation `A` of the Levi of `φ` and a representation `B` of the Levi of
`χ`, the anchor-change comparison of coefficient fibers takes an inducing equivalence
`e` from `A` to the pullback of `B` along the identity of points (written with
`conjugationFunctor` for the identity point and `anchorMembership`). It is the
composite of two maps:

1. the same-Levi transport `ActualConjugateLeviTensor.coefficientCongr` along
   `e`, from the coefficient fiber of `changeAnchor h P` induced from `A` to
   the coefficient fiber of `changeAnchor h P` induced from the pullback of
   `B`;
2. the inverse of `CoefficientConjugation.leviCoefficientLeftTranslation` for
   the identity point, from that coefficient fiber to the coefficient fiber of
   `P` induced from `B`.

The forward left translation for the identity point goes from the coefficient
fiber of `P` induced from `B` to the coefficient fiber of `changeAnchor h P`
induced from the pullback of `B`. In the target of the inducing equivalence,
`conjugationFunctor` carries the topological-group structure that the left
translation derives from `NonarchimedeanGroup`. With this shared instance, the
coefficient fiber induced from the pullback is definitionally the target of the
forward left translation. That fiber is thus the target of `coefficientCongr`
and the source of the inverse left translation, and the two maps compose
without a transport.

## Inducing equivalences and fiber transports

`identityInducingEquiv`, `multiplicationInducingEquiv` and
`inverseInducingEquiv` are the inducing equivalences, each the identity
linear map of the carrier of `A`:

- for the identity arrow, from the twist of `conjugateRepresentation χ 1 A`
  at the identity-transported unitary point to the anchor change of the twist
  of `A`, by `twistPullbackEquiv` with `identity_point_eq` and
  `identity_character_eq`;
- for two successive conjugations, from the twist of the twice-conjugated
  representation at the twice-transported unitary point to the anchor change
  of the twist of the representation conjugated by `s * t`, by
  `twistPullbackPullbackTwistEquiv` with `multiplication_point_eq` and
  `multiplication_character_eq`;
- for the inverse arrow, from the twist of the representation conjugated by
  `g` and then `g⁻¹` at the twice-transported unitary point to the anchor
  change of the twist of `A`, by `twistPullbackPullbackEquiv` with
  `inverse_point_eq` and `inverse_character_eq`.

The point equations compare maps between Levi subgroups on rational points.
The inverse `(leviConjugation χ g).symm` of the Levi conjugation sends a
rational point `x` to `g⁻¹ x g`. The identity of points
`conjugationEquiv 1 (·)` between the Levi subgroups of two equal anchors sends
`x` to `1⁻¹ x 1 = x`.

- `multiplication_point_eq`: the inverse Levi conjugation for `s` followed by
  the inverse Levi conjugation for `t` equals the identity of points followed by
  the inverse Levi conjugation for `s * t`, that is,
  `t⁻¹ (s⁻¹ x s) t = (s * t)⁻¹ x (s * t)`.
- `identity_point_eq`: the inverse Levi conjugation for the identity point is
  the identity of points, `1⁻¹ x 1 = x`.
- `inverse_point_eq`: the inverse Levi conjugation for `g⁻¹` followed by the
  inverse Levi conjugation for `g` is the identity of points, that is,
  `g⁻¹ (g x g⁻¹) g = x`.

`ActualParabolicUnitaryTranslation.unitaryParameter_conjugation_apply` says
that the literal Levi character at a unitary point transported by `g`, evaluated
at `m`, is the original literal Levi character evaluated at
`(leviConjugation χ g).symm m`. Each character equation
(`multiplication_character_eq`, `identity_character_eq`,
`inverse_character_eq`) is proved by rewriting every character at a
transported unitary point with this theorem, once for each conjugation
involved, and then applying the corresponding point equation.

In the anchors `χ ≫ (G.innerIso (s * t)).hom` and `χ ≫ (G.innerIso g⁻¹).hom`
of the target types the product and the inverse are formed in the group of
morphisms into `G.X`, whereas `leviConjugation`, `conjugateRepresentation`
and `unitaryConjugateParameter` form them in the group of rational points.
The two agree definitionally; the point and character equations are stated
with the rational-point product and inverse through
`conjugationAnchor_mul_points` and `conjugationAnchor_inv_points`, and
the anchor-change memberships `multiplication_anchorMembership` and
`inverse_anchorMembership` (with `identity_anchorMembership` for the identity
point). The theorems `identityInducingEquiv_linear_heq`,
`multiplicationInducingEquiv_linear_heq` and
`inverseInducingEquiv_linear_heq` state
`HEq (·).toLinearEquiv (LinearEquiv.refl ℂ A)`.

`identityEquiv`, `multiplicationEquiv` and `inverseEquiv` are the anchor-change
comparisons along these inducing equivalences. The theorems
`identityEquiv_eq`, `multiplicationEquiv_eq` and `inverseEquiv_eq` state that
each is `coefficientCongr` along its inducing equivalence followed by the
inverse of `leviCoefficientLeftTranslation` for the identity point. No
definition of this module transports along an equation between distinct terms,
so these values reduce definitionally; they retain the full external product
action and support the statements of the identity, composition and inverse
laws.
