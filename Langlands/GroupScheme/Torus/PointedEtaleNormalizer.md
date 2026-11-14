# Affine pointed etale normalizer lifts

This is an internal derived construction from the published
`Torus.RelativeTransporterEtaleLift`, `Torus.TransporterFunctoriality` and
`Torus.HenselianNormalizerLifting` interfaces, together with the affine-open
basis of a scheme. It introduces no additional original-literature claim.
The construction applies over any commutative ring `R`, in the full common
universe `u`. The ambient group `G` must be affine over `Spec R` and have
smooth structural morphism. The source `T` is a split torus, supplied as a
commutative group scheme, and `i : T.toGrp ⟶ G` is a supplied homomorphism.
Neither a closed-immersion condition on `i` nor reductivity of `G` is needed.

## Prescribed integral action

Fix an actual automorphism `σ : T ≅ T`, a point `s : Spec R`, and a
residue-valued point
`n₀ : Over.mk ((Spec R).fromSpecResidueField s) ⟶ G.X`.
`PointedEtaleNormalizerData i σ s n₀` records an affine scheme `U`, an
etale morphism `p : U ⟶ Spec R`, a morphism `b : Spec κ(s) ⟶ U`, and an
actual section `n` of `G_U`. Its equations are

```text
b ≫ p = (Spec R).fromSpecResidueField s,
IsNormalizingPoint (baseChange p i) n (baseChange p σ),
b ≫ n.left ≫ pullback.fst G.X.hom p = n₀.left.
```

The normalizing predicate is an equality of actual group-scheme
homomorphisms: conjugation by `n` on `i_U` equals the specified
automorphism followed by `i_U`.

`pointedEtaleNormalizerOfTransporter` constructs these data from the
all-refinement transporter premise
`PointwiseSchemeAction.IsTransporter (groupHom σ.hom ≫ i) i n₀`.
It chooses a diagonalizable presentation `eD : D ≅ T.toGrp`, precomposes
both homomorphisms with `eD.hom`, and invokes `pointedEtaleTransporter`.
It then chooses an affine open about the image of the residue point.
Every point of `Spec κ(s)` is the same, so its map factors through this
affine open. Restricting the transporter preserves its all-refinement
equations and exact residue recovery, while composition with the open
immersion preserves etaleness. The resulting neighbourhood is explicitly
the spectrum of the affine open's section ring.

The pullback point equivalence yields the actual section of `G_U`.
Precomposing its transporter equation with the base change of `eD.inv`
cancels the presentation. Finally,
`isNormalizingPoint_of_isTransporter` gives the exact normalizing equation.
This argument uses actual scheme tests throughout, including tests with
nilpotents.

## Supplied residue-fibre normalizer

`residueNormalizerPoint s n₀` regards a supplied section of the actual
residue fibre `G_κ(s)` as a point of `G` over the canonical residue-field
map. Its underlying scheme map is
`n₀.left ≫ pullback.fst G.X.hom ((Spec R).fromSpecResidueField s)`.

`pointedEtaleNormalizerOfNormalizing` accepts an actual residue-fibre
normalizing point whose action is the base change of the prescribed `σ`.
It converts the normalizing equation to the transporter equation, carries
that equation through the pullback point equivalence, and invokes the
preceding construction. Consequently its recovery equation compares the
lift with exactly the supplied residue point through these projections.

## Arbitrary residue action

`PointedEtaleResidueNormalizerData` additionally records an automorphism
`action : T ≅ T` whose base change is a supplied residue automorphism `σ₀`,
and the corresponding `PointedEtaleNormalizerData`.
`pointedEtaleNormalizer` constructs these data from a specified actual
residue normalizer `n₀` and its actual normalizing automorphism `σ₀`.
It first uses
`IsSplitTorus.automorphism_fieldBaseChange_surjective` to lift `σ₀` to
`action`, then applies `pointedEtaleNormalizerOfNormalizing`.

No locality, Henselian, reducedness, noetherian or characteristic
hypothesis is imposed on `R`. The conclusion is over a pointed affine
etale neighbourhood; it does not assert a section over `R` itself.
The residue normalizer is an input. Constructing a reflection normalizer
with normalized root coordinates, the required rank-one identities, and
the arbitrary-local-ring Isomorphism Theorem remain separate obligations.
