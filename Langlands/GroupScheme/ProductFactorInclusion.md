# Factor inclusions into finite products of group schemes

Authors: Worker 4896.

This internal supporting module is used by the proof of
`Langlands.GroupScheme.RankOneLeviFactorExistenceStatement`
(module `Langlands.GroupScheme.SimplyConnected.RankOneLeviFactorExistenceProof`).
It concerns the published categorical finite product `pi A` of a family
`A : I → GroupScheme S` with `I : Type u` finite (module
`Langlands.GroupScheme.Products`), in arbitrary universe `u`. A decidable
equality on `I` is assumed for the construction; the consumer supplies it by
classical logic.

## Over an arbitrary base scheme

- `piSingle A x : A x ⟶ pi A` is the homomorphism `Pi.lift` of the family
  equal to `𝟙 (A x)` at `x` and to the trivial homomorphism `0` elsewhere
  (`Function.update`).
- `piSingle_π_self` and `piSingle_π_of_ne`: its composite with the projection
  `Pi.π A x` is the identity, and with `Pi.π A y` for `y ≠ x` it is `0`.
- `piSingle_points_self` and `piSingle_points_of_ne`: the same two facts on
  points of an arbitrary test scheme; the coordinates other than `x` are the
  unit point `1`.
- `eq_comp_piSingle`: a homomorphism `f : B ⟶ pi A` with `f ≫ Pi.π A y = 0`
  for every `y ≠ x` equals `(f ≫ Pi.π A x) ≫ piSingle A x`. Both sides have
  the same projections (`Pi.hom_ext`).
- `isNormal_range_piSingle`: the image of `piSingle A x` is normal on every
  test scheme. For a point `g` of `pi A` and a point `w` of `A x`, the
  conjugate `g * (w ≫ piSingle A x) * g⁻¹` is the image of
  `gₓ * w * gₓ⁻¹`, where `gₓ` is the `x`-coordinate of `g`. This is checked
  coordinatewise through `piPointsEquiv`; at `y ≠ x` both sides are `1`.

## Over a field

Here the base is `Spec k` for a field `k`, and `(pi A).X.hom` is assumed
separated.

- `isClosedSubgroup_piSingle`: `piSingle A x` is a closed subgroup. It is a
  homomorphic section of `Pi.π A x`, so the published
  `IsClosedSubgroup.of_comp_eq_id` applies.
- `card_add_card_le_splitRank_pi`: let `x ≠ y`, and let
  `t₁ : splitTorus J₁ ⟶ A x` and `t₂ : splitTorus J₂ ⟶ A y` be closed
  subgroups with `J₁`, `J₂` finite. Then
  `Nat.card J₁ + Nat.card J₂ ≤ splitRank (pi A)`.

  Proof. Let `Ψ : splitTorus J₁ ⊗ splitTorus J₂ ⟶ pi A` be the `Pi.lift`
  that is `fst ≫ t₁` at `x`, `snd ≫ t₂` at `y` and `0` elsewhere. Its
  underlying morphism followed by `lift (Pi.π A x) (Pi.π A y)` is
  `t₁ ⊗ t₂`, a closed immersion by the published
  `ImageGeneration.isClosedImmersion_tensorHom_left`. The second map is
  separated, so `Ψ` is a closed immersion. Composing with the inverse of the
  published `splitTorus.prodIso J₁ J₂` gives a closed subgroup
  `splitTorus (J₁ ⊕ J₂) ⟶ pi A`, and `card_le_splitRank` with
  `Nat.card_sum` gives the bound.

## Provenance

These are internal categorical constructions on the published finite-product,
closed-subgroup and split-rank interfaces. No source assertion is used.
