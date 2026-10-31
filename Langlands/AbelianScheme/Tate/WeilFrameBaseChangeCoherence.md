# Identity and composition of Weil-compatible frame base change

This module constructs identity and composition comparisons for the actual
`WeilAdelicFrame` and `WeilPrimeToAdelicFrame` types and their right subgroup
orbits. It restricts the canonical geometric comparisons on ambient Tate frames
to the existing form-compatible subtypes.

## Data and hypotheses

Let `A/S` be an abelian scheme, with quasi-separated base, and let
`lam : A ⟶ A∨` be a homomorphism into the constructed dual abelian scheme.
The tensor/Picard hypotheses, chosen dual representability and geometry,
evaluation line bundle and evaluation isomorphism, and relative finite-Weil
transition compatibility are explicit. The comparisons also take
`PicardZeroUniversalBaseChangeStatement`. The rational algebra action is
`i : D →ₐ[ℚ] End0 A`, and `V` has compatible rational and `D`-module structures.
The form `ψ` is a rational bilinear form on `V`.

The full construction uses one
`h : RationalProfiniteIntegerAdeleComparison`, shared by the Tate targets and
their actual twist. The away construction uses one coupled
`hAway : PrimeToRationalProfiniteIntegerAdeleComparison h m` throughout;
`m` can be any natural number. Write `R` for the corresponding full or away
adelic ring. Frames have source `R ⊗[ℚ] V` and are linear over `D ⊗[ℚ] R`.
Their form-compatibility predicate asserts the existence of a trivialization
of the actual twist value module, without retaining a chosen trivialization.

For identity pullback the module takes dual geometry/evaluation data for
`A` and `(baseChange (𝟙 S)).obj A`. For composition, let
`b : S' ⟶ S` and `c : S'' ⟶ S'`, with all three bases quasi-separated.
Four dual geometry/evaluation packages are explicit: those for `A`, `b* A`,
`(c ≫ b)* A`, and `c* (b* A)`. The direct dual-valued map is the canonical
pullback of `lam` along `c ≫ b`; the successive map is the canonical pullback
along `c` of its canonical pullback along `b`. Rational algebra actions are
pulled back by the actual `rationalBaseChangeEnd` algebra homomorphisms.
No equality between these different abelian-scheme objects is assumed.

## Equality of points and identity

For equal field-valued points `s = t`, `weilAdelicFramePointEq` transports
actual compatible frames by equality elimination. Its `_underlying` theorem
identifies this transport with the existing `adelicFrameTestIso` whenever
the test-scheme isomorphism has identity underlying morphism.
`_right` proves compatibility with source precomposition, and
`weilAdelicFrameRightOrbitPointEq` descends to every right subgroup orbit set.
The `weilPrimeToAdelicFrame…` declarations give the same constructions away
from `m`.

`weilAdelicFrameBaseChangeId` is the existing compatible-frame base-change
equivalence for `𝟙 S`, followed by equality transport from `s ≫ 𝟙 S` to `s`.
Its `_underlying` equation identifies it with `adelicFrameBaseChangeId`.
Its `_apply` equation states that, for every vector `x`, the result is

```text
rationalMap (Over.mk s) P (baseChangeIdIso A).hom (eta x),
```

where `P` is the all-orders predicate, or `Nat.Coprime · m` in the away
version. The proof uses the published ambient identity-coherence equation
after the point-equality comparison. `BaseChange_id` records the identity
square on the actual subtypes.

## Composition

`weilAdelicFrameBaseChangeComp` goes from direct-pullback compatible frames
to successive-pullback compatible frames. It first applies direct base change
back to `A` at `s ≫ (c ≫ b)`, transports along the inverse associativity
equality to `(s ≫ c) ≫ b`, and applies the inverses of the comparisons for
`b` and then `c`.

`weilAdelicFrameBaseChange_base_comp` proves the resulting square by
cancelling these equivalences. Its `_underlying` theorem identifies the
constructed comparison with `adelicFrameBaseChangeComp`; thus its pointwise
map is exactly

```text
rationalMap (Over.mk s) P (baseChangeCompIso b c A).hom (eta x).
```

For the underlying-map proof, injectivity of the two ambient base-change
equivalences reduces the claim to a square on ambient frames.
The subtype square and the point-equality comparison supply one side.
Linear-map extensionality, the published
`finiteAdeleAlgebraBaseChange_base_comp` equation evaluated on a vector,
and inverse cancellation supply the other side. The away proof uses
`primeToFiniteAdeleAlgebraBaseChange_base_comp` in the same way.
The final conversions are definitional equalities between the corresponding
over-category expressions. These proofs do not take a new coherence
assertion as a hypothesis.

## Right orbits, Hecke maps and level forgetting

The identity and composition comparisons commute with the existing right
similitude action, whose convention is `eta * g = eta ∘ g`.
Their `RightOrbitBaseChangeId` and `RightOrbitBaseChangeComp` equivalences
descend using `RightOrbit.equiv`. The `_mk` theorems give the formula on a
representative class. The `RightOrbitBaseChange_id` and
`RightOrbitBaseChange_base_comp` theorems give the identity and composition
squares after quotienting, including the required point-equality transport.
They are proved by quotient induction from the actual frame equations.

All subgroup statements allow an arbitrary subgroup of
`ScalarExtensionSimilitudes D V R ψ`. For source subgroup `U` and target
subgroup `U'`, the `_translate` theorems commute with
`RightOrbit.translate g hg` under
`∀ u ∈ U, g⁻¹ * u * g ∈ U'`. They use the generic
`RightOrbit.map_translate` theorem and the proved right equivariance.
The `_forget` equations specialize to `g = 1` and `U ≤ U'`.
The full and away constructions have parallel statements.

## Provenance and scope

These are derived comparisons from
[WeilFrameBaseChange](WeilFrameBaseChange.md),
[AdelicFrameCoherence](AdelicFrameCoherence.md),
[AdelicBaseChangeCoherence](AdelicBaseChangeCoherence.md), and the generic
[OrbitEquiv](../../Shimura/PEL/OrbitEquiv.md) and
[OrbitTransport](../../Shimura/PEL/OrbitTransport.md) constructions.
Harris–Taylor (2001), printed p.18 / PDF p.26, gives the full and away
Tate rationalizations; Section III.1, printed pp.91–92 / PDF pp.99–100,
gives the pairing-compatible frames, invariant-orbit interpretation and right
Hecke convention motivating these comparisons. The relative coherence
equations here are deductions from the Library constructions, rather than
separately quoted assertions of that source.

This module establishes frame and right-orbit coherence. It does not assert
frame existence, nondegeneracy or alternation of an arbitrary `ψ`, a
polarization predicate for an arbitrary `lam`, compact-open topology,
coherence on monodromy-fixed level orbits, or canonical independence from
an unpointed base point.
