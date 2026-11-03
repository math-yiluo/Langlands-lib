# The standard face of a dominant cocharacter

This is derived infrastructure for `StandardParabolicClassificationStatement`.
It supplies the second half of the "standardness by containment" input of that
classification. Let `i` be a maximal split torus, `ν` a generic cocharacter of
it, and `Δ = simpleRelativeRoots i ν`. If `ξ` is a cocharacter of the same torus
and `P(groupHom ν ≫ i) ≤ P(groupHom ξ ≫ i)`, then
`P(groupHom ξ ≫ i) = standardParabolic i ν J` for the explicit face
`J = {α ∈ Δ | ⟨α, ξ⟩ = 0}`. This holds under the actual root-sign criterion for
inclusions of dynamic parabolics and negation stability of the relative roots.
Both are taken as explicit hypotheses: as local premises in the first section,
and as the published, still unproved statements
`RelativeRootSignInclusionsStatement.{u}` and `RelativeRootNegationStatement.{u}`
in the statement-level theorems. The unit proves no published `…Statement`.

The first half, the move from an arbitrary cocharacter `ζ` of `G` to a
cocharacter `ξ` of `i` with the same dynamic parabolic, is the separate unit
`Rational/ParabolicCocharacterConjugacy`; this unit does not import it.

## Setting and premises

The field `k : Type u` is arbitrary. In the section `Face`, `G` is a group
scheme over `Spec k` with `IsAffineHom G.X.hom`, `T` is any commutative group
scheme, and `i : T.toGrp ⟶ G` is any homomorphism; `ν` is any cocharacter of
`T`. No smoothness, reductivity or maximality is assumed there. The results use
some of the following local hypotheses, each stated where it is used:

- `hν : IsGenericCocharacter i ν`: `ν` pairs nonzero with every relative root.
- `hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i`.
- `hparabolic`: for all cocharacters `ζ, η` of `T`,
  `P(groupHom ζ ≫ i) ≤ P(groupHom η ≫ i)` if and only if every relative root
  pairing nonnegatively with `ζ` pairs nonnegatively with `η`. Some lemmas use
  only one direction and state only that direction.

In the last two theorems `G` satisfies `IsConnectedReductive G`, `i` is a
maximal split torus (`IsMaximalSplitTorus i`), and `IsAffineHom G.X.hom` is
`hG.isAffineHom`, as in `StandardParabolicClassificationStatement`. There the
three local hypotheses come from `hν` and the two published statements.

All inclusions and equalities of subgroup functors hold on every test scheme.

## Declarations

- `simpleRootFace i ν ξ` (definition): the set of simple relative roots `α`
  with `latticePairing T α ξ = 0`. `simpleRootFace_subset` records that it is a
  subset of `simpleRelativeRoots i ν`.
- `isStandardCocharacter_simpleRootFace`: if `ξ` pairs nonnegatively with every
  simple relative root, then `ξ` is a standard cocharacter for
  `simpleRootFace i ν ξ`. A simple root outside the face has nonzero, hence
  positive, pairing.
- `IsStandardCocharacter.eq_simpleRootFace`: conversely, a cocharacter standard
  for `J` determines `J` as its face. This lemma is not used by the others.
- `dynamicParabolic_eq_standardParabolic_of_isStandardCocharacter` (premises
  `hν`, `hneg`, and the "if" direction of `hparabolic`): if `ξ` is standard for
  `J`, then `P(groupHom ξ ≫ i) = standardParabolic i ν J`. The inclusion `≥` is
  the Library lemma `standardParabolic_le_dynamicParabolic`. For `≤`, let `η` be
  any standard cocharacter for `J`. The published
  `IsStandardCocharacter.root_pairing_implications_of_subset`, applied to `ξ`,
  `η` and `J ⊆ J`, shows that every relative root pairing nonnegatively with `ξ`
  pairs nonnegatively with `η`. The root-sign criterion then gives
  `P(groupHom ξ ≫ i) ≤ P(groupHom η ≫ i)`. Since `standardParabolic i ν J` is the
  intersection of these `P(groupHom η ≫ i)`, the inclusion follows.
- `pairing_nonneg_of_parabolic_le` (premise: the "only if" direction of
  `hparabolic`): if `P(groupHom ν ≫ i) ≤ P(groupHom ξ ≫ i)`, then `ξ` pairs
  nonnegatively with every positive relative root. A positive root pairs
  positively, hence nonnegatively, with `ν`, so the criterion applies.
- `dynamicParabolic_eq_standardParabolic_simpleRootFace_of_le` (premises `hν`,
  `hneg`, `hparabolic`): if `P(groupHom ν ≫ i) ≤ P(groupHom ξ ≫ i)`, then
  `P(groupHom ξ ≫ i) = standardParabolic i ν (simpleRootFace i ν ξ)`. Simple
  roots are positive, so the previous lemma makes `ξ` nonnegative on `Δ`. Hence
  `ξ` is standard for its face, and the equality lemma above applies.
- `exists_standardParabolic_eq_of_parabolic_le`: the same conclusion as an
  existence statement, `∃ J ⊆ simpleRelativeRoots i ν` with
  `P(groupHom ξ ≫ i) = standardParabolic i ν J`. This is the form of the
  standardness clause in `StandardParabolicClassificationStatement`, restricted
  to cocharacters of `i`.
- `dynamicParabolic_eq_standardParabolic_simpleRootFace_of_statements`
  (premises `RelativeRootSignInclusionsStatement.{u}` and
  `RelativeRootNegationStatement.{u}`): for connected reductive `G`, a maximal
  split torus `i`, a generic `ν` and any `ξ` with
  `P(groupHom ν ≫ i) ≤ P(groupHom ξ ≫ i)`, the face equality holds. The
  root-sign criterion is the first conjunct of the first statement, and `hneg`
  is the second statement.
- `exists_standardParabolic_eq_of_parabolic_le_of_statements`: the existence
  form of the previous theorem.

## Provenance

The mathematics is the classical description of standard parabolic subgroups.
Milne, *Algebraic Groups* (2017), 25.23 (printed p. 550): for a subset `I` of
the base, `P_I` is generated by `C_G(S)` and the root groups `U_α` such that,
when `α` is expressed in the base, "the roots not in I occur with nonnegative
coefficients"; "the P_I are the standard parabolic subgroups of G containing
P". For a cocharacter `ξ` that vanishes on `I` and is positive on the other simple
roots, these are exactly the roots pairing nonnegatively with `ξ`, so
`P(ξ) = P_I`. A parabolic `P(ξ)` containing the minimal parabolic contains the
positive root groups, which forces `ξ` to be nonnegative on the positive roots.

The Lean route does not use root groups or generation. The face `J` and the
standardness of `ξ` for `J` are internal. The equality with
`standardParabolic i ν J` comes from the published root-sign criterion and the
published comparison `IsStandardCocharacter.root_pairing_implications_of_subset`.
The Library defines `standardParabolic i ν J` as the intersection over all
standard cocharacters for `J`, so no standard-cocharacter existence statement is
needed: `ξ` itself is the witness.
