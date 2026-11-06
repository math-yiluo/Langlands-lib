# The all-test centralizer of a section of a group scheme

Worker 1296.

This helper module defines the centralizer of a single section of a group
scheme as a subgroup functor, shows that it is closed and representable over a
separated group, and records how it behaves under base change and under
conjugation. It is internal infrastructure for the proof of
`Langlands.GroupScheme.RegularConjugateFiniteGaloisStatement`; no literature
statement is formalized here. The base `S` is an arbitrary scheme in universe
`u` unless stated otherwise. Points of a group scheme `G` over `S` on a test
`T : Over S` are morphisms `T ⟶ G.X`, with the point group structure.

## Definitions

- `conjugationSchemeAction G`: the action of `G` on its own underlying scheme
  `G.X` by conjugation. It is built with `schemeActionOfPointLaws` from the
  published automorphic conjugation action `AutomorphicAction.conjugation (𝟙 G)`.
  `conjugationSchemeAction_act` states that on every test `T` the action is
  `h • g = h * g * h⁻¹`.
- `pointCentralizer G x`, for a section `x : 𝟙_ (Over S) ⟶ G.X`: the
  stabilizer of `x` for the conjugation action. By `mem_pointCentralizer`, a
  point `c : T ⟶ G.X` belongs to it on the test `T` exactly when
  `c * (toUnit T ≫ x) = (toUnit T ≫ x) * c`. This is the all-test
  (scheme-theoretic) centralizer of `x`, the same condition that appears in the
  hypotheses and conclusion of `RegularConjugateFiniteGaloisStatement`.

## Closedness

`pointCentralizer_isClosedRepresentable`: if `G.X.hom` is separated, the
centralizer of a section is represented by a closed subgroup scheme. This is
the published `SchemeAction.stabilizer_isClosedRepresentable` applied to the
conjugation action.

## Base change

Let `b : S' ⟶ S`. For a point `y : Over.mk b ⟶ G.X`, write `y_b` for the
corresponding section `(baseChangeBasePointsEquiv b G).symm y` of the base
change `G_{S'}`.

- `baseChangePointsEquiv_toUnit_comp_symm`: on a test `T` over `S'`, the
  pullback of `y_b` to `T` corresponds, under `baseChangePointsEquiv b G T`,
  to `y` restricted along the structure morphism `T.hom`.
- `mem_pointCentralizer_baseChange_iff`: a point `c` of `G_{S'}` on `T`
  centralizes `y_b` exactly when its image in `G` commutes with `y` restricted
  to `T`.
- `pointCentralizer_baseChange`: the base change along `b` of the centralizer
  of a section `x` over `S` is the centralizer in `G_{S'}` of the pulled-back
  section `(toUnit (Over.mk b) ≫ x)_b`.
- `baseChangePointsEquiv_constantPoint_symm`: the constant family of `y_b`
  (`constantPoint`) on `T` corresponds to `y` restricted to `T`.

## A commutative representative

`range_eq_pointCentralizer`: let `j : H ⟶ G` with `H.X` commutative. If the
centralizer of `x` is contained in the range of `j`, the two are equal. Proof:
`x` centralizes itself, so `x` restricted to `T` is in the range of `j`; any
point of the range is then the image of a point of the commutative group `H`
and commutes with it.

## Conjugation

`isRepresentedBy_pointCentralizer_baseChange_of_conj`: let `b : S' ⟶ S` and
`c : S'' ⟶ S'`. Let `j : H ⟶ G_{S'}` represent the centralizer of the section
`z_b` attached to a point `z : Over.mk b ⟶ G.X`. Let `g : Over.mk (c ≫ b) ⟶ G.X`
satisfy `g * (toUnit _ ≫ x) * g⁻¹ = c ≫ z`, that is, `g` conjugates the section
`x` to `z` over `S''`. Then the base change of the centralizer of `x` to `S''`
is represented by the composite of

1. the base change of `j` along `c`,
2. the comparison `baseChangeCompIso b c G` (inverse direction) from
   `(G_{S'})_{S''}` to `G_{S''}`, and
3. the inner automorphism `innerIso` of `G_{S''}` by the inverse of the section
   attached to `g`.

The proof composes the published lemmas `IsRepresentedBy.baseChange` and
`IsRepresentedBy.comp_iso` for the monomorphism part. For the range, it rewrites
membership in the range of a composite with an isomorphism and with an inner
automorphism (`MaximalTorusParameterExistence.mem_range_comp_iso_iff`,
`mem_range_comp_innerIso_iff`) and the range of a base-changed homomorphism
(`SubgroupFunctor.range_baseChangeHom`). It then reduces membership in both
subgroup functors to commutation identities in `G`. These two identities are
conjugate by `g` restricted to the test, and the private lemma `conj_comm_iff`
says that `a y a⁻¹` and `a w a⁻¹` commute if and only if `y` and `w` commute.
