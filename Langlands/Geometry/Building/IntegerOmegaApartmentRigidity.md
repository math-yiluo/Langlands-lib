# Rigidity of centralizer-compatible apartment classes over any field

This module proves the class-rigidity step of Kaletha–Prasad, *Bruhat–Tits
theory: a new approach* (2023), Proposition 6.2.6, printed p.216 (PDF p.247),
for an integer-valued valuation on an arbitrary field. Two full
`KPApartmentData` classes satisfying the integer-valued V 6 condition
`IntegerValuation.IsOmegaCompatible` for the same actual centralizer datum are
equal. This holds whenever every nonidentity point of every actual relative root
group has an actual opposite factor pair. That existence,
`RelativeRoot.HasOppositeFactorPairs i`, is an explicit premise. The module
proves neither it nor the existence of any compatible class.

## Provenance

The Library already proves this rigidity for nonarchimedean local fields with
the order `localFieldOrder F`
(`KPApartmentData.eq_of_isOmegaCompatible_of_hasOppositeFactorPairs` in
`OmegaCompatibleApartmentRigidity`). The arguments use only the KP valuation axioms,
`N(F)`-stability of the apartment class, the integral coroot formula of an
opposite pair and finiteness of the relative Weyl group. This module repeats
them for an arbitrary field `k : Type u` and an arbitrary order map
`ω : kˣ → ℝ`, working directly with `KPApartmentData i ω`. The proofs closely
follow these published modules:

- `RootReflectionProof`: AS 1, KP Proposition 6.2.1, printed pp.212–214
  (PDF pp.243–245);
- `RootReflectionAction`: the linear reflection of an opposite pair;
- `OmegaCompatibleApartmentValueComparison`: the rank-one value identification
  of Proposition 6.2.6;
- `OmegaCompatibleApartmentComparison`: the finite Weyl-quotient average,
  derived from the existence assertion of KP Proposition 4.4.3, printed
  pp.181–182 (PDF pp.212–213);
- `OmegaCompatibleApartmentRigidity`: the final identification.

The averaging step is stated here for an abstract predicate on common
centralizer displacements, and the integer-valued V 6 is shown to imply it.
The registered 2024 *Corrections and additions* (Chapter 4 pp.28–29,
Chapter 6 p.32) do not change these steps.

## Coroot class and its reflection

Let `S` be a split torus over `k` with an actual monomorphic `i : S.toGrp ⟶ G`,
where `G` is affine over the base. Let `u` be a nonidentity point of the root
group of `α`, and let `hp` be an actual opposite factor pair for `u`.
`oppositeFactorPairCorootClass` is the class of `1 ⊗ ν` in `TranslationSpace i`,
where `ν` is the integral coroot supplied by
`RelativeRoot.IsOppositeFactorPair.coroot_spec`.
`rootForm_oppositeFactorPairCorootClass` shows that the root takes the value two
on it. `translationAction_oppositeFactorPair` proves that the linear action of
`m = p.1 * u * p.2` on the translation space is
`w ↦ w - rootForm α w • (coroot class)`. The proof shows that the integral
reflection is an involution, so it is also the action of `m⁻¹`. It then
compares every root evaluation modulo the root annihilator.

## AS 1 and the displacement formula

Assume that `G` is connected reductive and `i` is a maximal split torus, and fix
`D : KPApartmentData i ω`. `KPApartmentData.oppositeFactorPair_smul_eq_self` is
AS 1. If the root value of `u` at an apartment point `x` is `0`, then `m • x = x`.
The proof is the route of `RootReflectionProof.rootReflection`:

1. Equipollence gives `m • x.val = v +ᵥ x.val`.
2. V 5 (`IsRootDatumValuation.opposite`) and `RootReflectionProof.apply_inv`
   show that both pair factors and the conjugated point have value `0`, so
   `a(v) = 0`.
3. `RootReflectionProof.not_eval_neg` excludes negative and positive root values
   of `v`.
4. `IsRootDatumValuation.vadd_eq_self_iff` gives `m • x = x`.

`KPApartmentData.rootForm_oppositeFactorPair_vsub` proves that the root applied
to `m • x -ᵥ x` is `-2 * t` when the root value of `u` at `x` is `t`. The proof
translates `x` by `-(t / 2)` times the coroot class to a point with value `0`.
AS 1 fixes that point, and the reflection formula computes the displacement.

## Value comparison and identification

Let `E : KPApartmentData i ω` and let `f : D.Apartment ≃ᵃ[ℝ] E.Apartment` have
identity linear part and commute with the two original actions of
`normalizerPoints i`. `KPApartmentData.val_eq_of_equivariant_of_oppositeFactorPair`
proves that `f` preserves the value of every nonidentity root point with an
actual opposite pair. The two displacements of `m` agree because `f` is
equivariant with identity derivative. The displacement formula then equates
twice the two real values; these are finite by V 1.
`KPApartmentData.eq_of_equivariant_of_hasOppositeFactorPairs` assumes
`RelativeRoot.HasOppositeFactorPairs i`. It applies
`IsRootDatumValuation.eq_of_eq_on_nonidentity_root_points` at one apartment point
and concludes `D = E` by `KPApartmentData.eq_of_common_mem`.

## Weyl-quotient averaging

`KPApartmentData.HasCommonCentralizerDisplacements D E` says that every
normalizer point lying in `centralizerPoints i` displaces every point of `D` and
every point of `E` by the same translation. For chosen points `x` and `y`,
`centralizerComparisonDefect` is `(n • y -ᵥ y) - (n • x -ᵥ x)`.
`normalizerDisplacement_mul` and `centralizerComparisonDefect_mul` give its
cocycle law with linear part `translationAction i`. Under the common
displacement predicate, the defect vanishes on the centralizer and is constant
on the fibers of `relativeWeylGroup i`
(`centralizerComparisonDefect_eq_zero` and
`centralizerComparisonDefect_eq_of_weylClass_eq`).

`centralizerComparisonCorrection` is the published
`FiniteQuotientAffineComparison.average` of the defect over the finite relative
Weyl quotient. `centralizerComparisonCorrection_spec` gives the coboundary
identity. `centralizerComparisonAffineEquiv` uses the published
`IsConnectedReductive.finite_relativeWeylGroup` and chosen points `x` and `y`.
It sends `z` to `(z -ᵥ x) +ᵥ (b +ᵥ y)`, where `b` is the correction. Its linear
part is the identity (`centralizerComparisonAffineEquiv_linear`). It commutes
with the normalizer actions under the common displacement predicate
(`centralizerComparisonAffineEquiv_smul`).
`eq_of_hasCommonCentralizerDisplacements_of_hasOppositeFactorPairs` combines this
equivalence with the identification above.

## Integer-valued V 6

Let `v : Valuation k (WithZero (Multiplicative ℤ))`, let `C` be a
`CentralizerDatum i`, and let `D E : KPApartmentData i (IntegerValuation.order v)`.
`IntegerValuation.IsOmegaCompatible.hasCommonCentralizerDisplacements` shows that
`IsOmegaCompatible v D C` and `IsOmegaCompatible v E C` give common centralizer
displacements. Every normalizer point in the centralizer is the image of a
rational point of `C.Z`, by the representation `C.isRepresentedBy`.
`IsOmegaCompatible.smul_eq_vadd` makes that point act on both classes by the same
centralizer translation. `IntegerValuation.IsOmegaCompatible.eq_of_hasOppositeFactorPairs`
then gives `D = E`.

## Statement

`IntegerOmegaCompatibleApartmentRigidityStatement.{u}` quantifies over:

- every field `k : Type u` and integer-valued valuation `v`;
- every affine connected reductive `G`;
- every maximal split torus `i` with monomorphic underlying scheme map;
- opposite-factor-pair existence for `i`;
- a common `CentralizerDatum i`;
- two classes over `IntegerValuation.order v` satisfying `IsOmegaCompatible` for
  it.

Its conclusion is that the two classes are equal.
`integerOmegaCompatibleApartmentRigidity` proves it in every universe.

## Scope

The module proves no existence of opposite factor pairs, centralizer data or
compatible apartment classes. It also proves no Galois stability, metric,
specialness or integral-model comparison.
