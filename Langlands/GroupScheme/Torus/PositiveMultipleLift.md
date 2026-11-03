# Positive-multiple lifts of actual cocharacters

This is an internal derived construction by Worker 146.

Let `k : Type u` be any field, let `T` and `U` be commutative group schemes over
`Spec k`, and assume that their underlying group schemes are split tori. Let
`p : T ⟶ U` be an actual homomorphism such that its underlying group-scheme map
`CommGroupScheme.groupHom p` is a categorical epimorphism. Then every actual
integral cocharacter `ν' : cocharacterLattice U` admits

```text
∃ d : ℤ, 0 < d ∧ ∃ ν : cocharacterLattice T, ν ≫ p = d • ν'.
```

The theorem is `IsSplitTorus.exists_positive_multiple_cocharacter_lift`.
Both cocharacters take values in the given tori over the original field.
The conclusion is an equality of actual homomorphisms, not an equality obtained
only after tensoring or after evaluating on field-valued points.

`PositiveMultipleCocharacterLift p ν'` retains a positive integer multiplier,
an actual source cocharacter and this composite equality. The definition
`IsSplitTorus.positiveMultipleCocharacterLift hT hU p ν'` constructs such data
under the preceding hypotheses, by choosing witnesses from the proved
existence theorem. This choice is not claimed to be canonical or natural.
`PositiveMultipleCocharacterLift.groupHom_comp` records the same equality
between the underlying group-scheme homomorphisms.

The corollary
`IsSplitTorus.exists_positive_multiple_cocharacter_lift_of_flat_surjective`
applies to every flat surjective underlying scheme map `CommGroupScheme.hom p`.
It imposes no finiteness or finite-kernel hypothesis on `p`. In particular it
allows positive-dimensional kernels. No assumption asserts surjectivity on
`k`-points. All fields, including imperfect fields and positive characteristic,
and all finite torus ranks, including rank zero, are included.

The multiplier can depend on `ν'`. This unit does not assert that the original
cocharacter itself lifts integrally, that a lift is primitive or unique, or that
the map on integral cocharacters has finite cokernel.

## Implemented proof

`characterRestrict_injective_of_epi` first proves, over an arbitrary base scheme,
that a categorical epimorphism of group schemes induces an injective map on
actual characters. Equality after restriction is equality of composites with
the epimorphism, so categorical cancellation gives equality of characters.

The actual character restriction is extended from `ℤ` to `ℚ` by the published
`rationalCharacterRestrictRat`. Its injectivity follows from
`RationalSpan.rationalization_injective`, which uses flatness of `ℚ` over `ℤ`.
The target cocharacter `ν'` defines a rational linear functional on
`ℚ ⊗[ℤ] characterLattice U`: scalar extension of its integral lattice pairing,
followed by the standard identification `ℚ ⊗[ℤ] ℤ ≃ ℚ`.
At the image of an integral character `α` this functional has value
`(latticePairing U α ν' : ℚ)`.

Mathlib's `LinearMap.dualMap_surjective_of_injective` extends this functional
across the injective rationalized restriction map to a rational functional `F`
on the full character space of `T`. The published theorem
`IsSplitTorus.exists_positive_multiple_pairing` supplies `d > 0` and an actual
integral source cocharacter `ν` whose pairings are `d` times `F`.
That theorem realizes rational functionals in finite split-torus coordinates
and clears their denominators with a positive multiplier; it has no geometric
classification premise.

Evaluating on every restricted target character gives

```text
latticePairing U α (ν ≫ p) = latticePairing U α (d • ν').
```

This uses associativity of actual morphism composition, bilinearity of the
published integer pairing and injectivity of the integer-to-rational map.
The published `IsSplitTorus.cocharacter_eq_zero` detects cocharacters by all
character pairings, so their difference is zero. It proves the required
equality in the original integral Hom group.

For the flat surjective corollary, splitness makes both tori affine. The map
between their underlying affine schemes is quasi-compact, hence its flatness
and surjectivity make it an effective epimorphism by the fpqc theorem. It is
therefore an epimorphism of schemes, then of schemes over the base, then of
group schemes by the faithful forgetful functor. The preceding construction
applies.

## Provenance and remaining scope

The content is derived from the imported actual lattice, rationalization,
pairing-realization and fpqc constructions, together with linear dual
extension. No separate original-source assertion is invoked. It supplies a
positive-multiple lift that can be combined with a separately proved positive
scaling theorem in a central-quotient route to parabolic classification.
It does not construct a reductive quotient, compare dynamic parabolics along
that quotient, or prove `SplitParabolicCocharacterStatement`.
