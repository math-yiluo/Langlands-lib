# Coefficient transport of rational characters of arbitrary group schemes

This module extends the existing character transport of `Torus/LatticeGalois`
from the character lattice of a commutative group scheme to the actual rational
characters `rationalCharacters` of an arbitrary group scheme. It is an internal
consequence of the published descent-point, character-transport, rational
character and rational-point constructions. No commutativity, affineness,
finiteness, separability or reductivity hypothesis is used, and no
original-source assertion is introduced.

## Generic transport

Fix schemes `B` and `S`, a morphism `b : S ⟶ B`, and an endomorphism
`a : S ⟶ S` with `a ≫ b = b`. For group schemes over `B`, base change along
`b` gives group schemes over `S`.

- `descentPoint_comp_baseChange` proves that the existing `descentPoint b a ha`, which
  changes the `S`-structure of a point by `a`, commutes with every homomorphism
  `f : H ⟶ G` defined over `B`. The proof applies injectivity of
  `baseChangePointsEquiv` and its composition and descent-point laws.
- `transportCharacter_naturality` proves that the existing
  `transportCharacter b a ha` commutes with restriction along the base change
  of such an `f`. Both sides are compared on all points by `hom_ext_points`
  and `Gm.pointsEquiv` injectivity, using `transportCharacter_points` and
  `descentPoint_comp_baseChange`.
- `rationalCharacters.transport b a ha G` is the additive endomorphism of
  `rationalCharacters` of the base change of `G` sending `χ` to
  `transportCharacter b a ha G χ`, written additively. Additivity is proved by
  `ext_characterEval`, the point formula `characterEval_transport` and the
  existing addition and zero laws of `characterEval`.
- `characterEval_transport` states that the transported character evaluates
  `χ` at the same point, seen through `descentPoint`. `transport_toMul`
  records the underlying morphism.
- `transport_id`, `transport_transport`, `transport_of_eq_id` and
  `transport_transport_of_eq` are the identity and composition laws, obtained
  from `transportCharacter_id` and `transportCharacter_comp`.
- `characterRestrict_transport` states that `characterRestrict` along the base
  change of a homomorphism defined over `B` commutes with transport. It follows
  from `transportCharacter_naturality`.

## Coefficient action

Fix commutative rings `k` and `K`, an algebra `k → K`, and a group scheme `G`
over `Spec k`, base changed along `algebraBaseMap k K`.

- `rationalCharacters.galoisRepresentation k K G` is the integral
  representation of `K ≃ₐ[k] K` on these actual rational characters: `σ` acts
  by `transport` along `galoisBaseMap k K σ`. The unit and multiplication laws
  follow from `galoisBaseMap_one`, `galoisBaseMap_mul` and the identity and
  composition laws above. `galoisRepresentation_apply` records the defining
  equation.
- `characterEval_galoisRepresentation` is the point formula specialized to
  `σ`.
- `characterRestrict_galoisRepresentation` proves equivariance of restriction
  along the base change of a homomorphism `H ⟶ G` defined over `k`.
- `equivCharacterLattice_galoisRepresentation` proves, by definitional
  equality, that for a commutative group scheme `T` the identification
  `equivCharacterLattice` intertwines this action with the existing
  `characterLattice.galoisRepresentation k K T`.
- `galoisRepresentation_self_inv` specializes `Representation.self_inv_apply`:
  `σ (σ⁻¹ χ) = χ`.

## Evaluation on rational points

Now let `k` and `K` be fields. The rational characters below are those of
`(GroupScheme.baseChange (algebraBaseMap k K)).obj G`, and the `K`-points are
`rationalPoints (baseChanged k K G)` acted on by the existing
`GaloisPointComparison.rationalConjugate k K G σ`.

- `rationalCharacterEval_galoisRepresentation` proves
  `(σ χ)(σ x) = σ (χ x)` in `Kˣ`, for every character `χ` of `G_K` and every
  `K`-point `x`; the character need not descend to `k`. The proof uses
  `characterEval_galoisRepresentation`, `descentPoint_rationalConjugate` and
  `characterEval_naturality` along `galoisIdentityTestIso k K σ`. The private
  lemma `units_ΓSpecIso_spec_map`, a unit form of `Scheme.ΓSpecIso_naturality`,
  identifies the resulting pullback of global units with `Units.map σ`.
- `rationalCharacterEval_rationalConjugate_of_eq` restates this for any `χ`
  supplied with an equation `σ χ' = χ`.
- `rationalCharacterEval_rationalConjugate` is the inverse form
  `χ (σ x) = σ ((σ⁻¹ χ) x)`, obtained from the previous lemma and
  `galoisRepresentation_self_inv`.

All characters in this section have the same type, so that the implicit group
arguments of `rationalCharacterEval` agree on both sides of each equation.

This module constructs only the coefficient action on characters and its
evaluation laws. It does not prove descent of characters, construct
valuations or apartments, or assert any building comparison.

The descent-point naturality step uses the existing `Langlands.GroupScheme.descentPoint_comp_baseChange` theorem.
