# Rectangular Haar measure under JPSS character change

Author: Worker 99.

This internal statement unit connects the existing JPSS inverse row scaling to
the residue-normalized rectangular Haar law. It defines propositions; it does
not prove either change-of-measure identity.

## The general Haar target

`Langlands.RankinSelberg.CharacterChangeRectangularHaarStatement` is a closed
`Prop` definition with the independent field-carrier universe `uF`. It quantifies
over every natural prime `p`, its `Fact p.Prime` instance, every
`F : PadicField.{uF} p`, supplied `T : F.TopologicalData`, and all natural `j,n`.
It installs exactly `T.topology`. The matrix topology is the existing entrywise
product topology on `Matrix (Fin j) (Fin (n + 1)) F.Carrier`.

For every measurable structure on that matrix space, every instance certifying
that it is the Borel structure of this topology, every additive Haar measure
`ν` on the matrix space, and every field unit `a`, the proposition states

```text
HasCharacterChangeRectangularMeasureLaw
  (normalizedAbsoluteValue T) a j n ν.
```

Unfolding the existing predicate gives precisely

```text
Measure.map (characterChangeRectangular a j n) ν =
  (characterChangeRectangularModulus
    (normalizedAbsoluteValue T) a j n : ENNReal) • ν.
```

There is no independently chosen scalar measurable structure, regularity
assumption, countability assumption, normalization, determinant-scaling
assumption, or measure-law premise in this target. The `IsAddHaarMeasure`
hypothesis is the existing Mathlib property of the quantified measure.

The map is the published linear equivalence from `CharacterChangeBlocks`.
For zero-based row `i`, its entry formula is

```text
(S x) i l = a^(-(i.val + 1)) * x i l.
```

The unit inverse and natural power in the actual definition make every row
factor nonzero. `UnequalRankCharacterTransport` already supplies the continuous
linear equivalence `characterChangeRectangularContinuous`; consequently `S`
is measurable for any of the quantified Borel structures. The pushforward is
therefore the ordinary measure pushforward along this map.

## The canonical product target

`Langlands.RankinSelberg.CharacterChangeRectangularProductStatement` quantifies
over the same `p,F,T,j,n`. It installs `T.topology`, `T.valuativeRel` and
`T.localField`, and the already proved `T.secondCountableTopology`. The scalar
measurable structure is `borel F.Carrier` with its reflexive `BorelSpace`
instance. The matrix measurable structure is the existing nested product
structure inherited from the scalar field, not a new choice of measure or
measurable space. Second countability supplies the Borel property of these
finite products.

For every existing `HarmonicAnalysis.AdditiveHaarMeasure F.Carrier` bundle `η`
and every unit `a`, the conclusion is the same predicate evaluated at

```text
rectangularMeasure η j (n + 1).
```

This is the actual nested product
`Measure.pi (fun _ : Fin j => Measure.pi (fun _ : Fin (n+1) => η.measure))`
from `RankinSelberg.Measures`. The shared scalar bundle already contains its
additive Haar and regularity properties, with no prescribed normalization.
No self-duality or chosen mass on the integer ring is required. The proposition
adds no measure hypothesis to that bundle.

Local finiteness of `η.measure` follows from its Haar instance. Sigma
compactness follows from the published `T.sigmaCompactSpace`, so its local
finiteness gives sigma finiteness. Measurable addition follows from the actual
topological ring structure and scalar Borel structure. The existing
`rectangularMeasure_sigmaFinite` and `rectangularMeasure_isAddHaar` instances
then apply to the nested product. These are intrinsic instance derivations,
not additional assumptions or claims of a Haar scaling proof.

The conclusion uses exactly the predicate consumed by
`integral_characterChangeRectangular` and the unequal-rank integral,
convergence, rational-continuation and Laurent-span transport interfaces.
Those interfaces remain conditional until a proof supplies this conclusion
and any other hypotheses they require, including their separate quotient law.

`Langlands.RankinSelberg.CharacterChangeRectangularMeasureStatement` is the
conjunction of the two named propositions, in general-then-product order. It
provides one exact target for a subsequent proof.

## Exponent and boundary cases

The existing definitions in `UnequalRankCharacterIntegrals` give

```text
E(j,n) = (n + 1) * ∑ i : Fin j, (i.val + 1),
c(j,n,a) = |a|^E(j,n).
```

Here `|a| = normalizedAbsoluteValue T a` is the existing residue-normalized
absolute value, packaged from `T.normalizedAbs` in `AnalyticStatement`.
The existing `characterChangeRectangularModulus` is a nonzero `NNReal`;
its coercion to `ENNReal` is finite and positive.

No dimension is required to be positive except the built-in column count
`n+1`. At `j=0`, the matrix space is a singleton, the sum is empty, and the
modulus is one. The existing `rectangularMeasure_zero_rows` identifies the
product measure with `Measure.dirac 0`, including its mass-one normalization.
At `n=0` there is one column, and the same row formula and exponent apply.

## Internal provenance and later proof

This unit transcribes no new literature theorem. Its objects and normalization
are those already published in `CharacterChangeBlocks`,
`UnequalRankCharacterTransport`, `UnequalRankCharacterIntegrals`, `Measures`,
`HarmonicAnalysis.Basic`, and `AnalyticStatement`. The only additional import,
`HarmonicAnalysis.PadicScalarHaarScalingProof`, supplies the intrinsic
second-countability result for the supplied p-adic topology.

The intended derivation specializes the existing
`HarmonicAnalysis.PadicRectangularHaarScalingStatement` to dimensions
`r=j`, `s=n+1`, the diagonal matrix
`A=diag(a^(-1),...,a^(-j))`, and `B=1`. In field-unit notation,

```text
det(A) = a^(-∑ i : Fin j, (i.val + 1)).
```

Left multiplication by this `A` is the existing row map `S`. The general
rectangular determinant law has pushforward factor
`(|det A|^(n+1) / |det B|^j)^(-1)`. Substitution gives `|a|^E(j,n)`.
The sign is positive because pushforward evaluates preimages: the inverse
Jacobian reverses the negative exponent in the row dilation. It is not the
volume factor of the row dilation itself.

The general determinant theorem is already proved in the separately published
`HarmonicAnalysis.PadicRectangularHaarScalingProof`. A future focused proof
must apply it to the actual diagonal, establish the determinant and modulus
identities in Lean, and specialize to the actual product measure using the
intrinsic instances above. This explanation records the internal derivation;
this statement file performs none of those Haar-law proof steps. Neither
publication of these propositions nor creation of that proof task establishes
the JPSS character-change Haar identity.
