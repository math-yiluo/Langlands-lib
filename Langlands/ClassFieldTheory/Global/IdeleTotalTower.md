# Total idele invariants under inflation and descent to the quotient-map image

This is an internal derived construction on the actual idele and idele-class
cohomology. All fields lie in an arbitrary common universe. Write
`j = ideleQuotientCohomologyMap F E 2`, whose source is
`H²(Gal(E/F), J_E)` and whose target is `H²(Gal(E/F), C_E)`.

For number fields `F` and `E`, an algebra structure `F → E`, and `E/F` Galois,
fix one finite and one infinite place of `E` above every corresponding place of
`F`. Supply an arbitrary local invariant family `I` and its `RelativeImages`
law at every rational prime. Assuming explicitly that
`Reciprocity.SumOfInvariantsVanishes I x` holds for every field-unit cohomology
class `x` of `E/F`, `ideleClassInvariantOnQuotientRange` is an additive map
from the image subgroup of `j` to `ℚ/ℤ`. Its value at `j(a)` is exactly
`totalIdeleInvariant I hI wf wi a`. Consequently any two idele cohomology
classes with equal images under `j` have equal total invariants.

The construction applies `FiniteInvariantDescent.onRange`. The published
`totalIdeleInvariant_eq_zero_of_ideleQuotient_eq_zero` supplies the required
kernel inclusion: the cohomology exactness theorem expresses a class in the
kernel of `j` as a principal class, and the explicit reciprocity hypothesis
makes its total invariant vanish. This construction needs neither finiteness
of idele-class cohomology nor a cardinality bound.

For a scalar tower of number fields `F → E → L`, with both `E/F` and `L/F`
Galois, `totalIdeleInvariant_relativeIdeleInflation` preserves total invariants.
It assumes the same family's `RelativeImages` and `InflationCompatibility`
laws at every rational prime, and compatible chosen places: each chosen
finite place of `L` lies over its chosen place of `E`, and each chosen
infinite place has the chosen place of `E` as its comap. The proof adds
`finiteIdeleInvariantSum_relativeIdeleInflation` and
`archimedeanIdeleInvariantSum_relativeIdeleInflation`.

`ideleQuotientRangeInflation` restricts the actual idele-class inflation map
to the images of the two quotient cohomology maps. Membership follows from
the existing quotient/inflation square. On the image of `a` it is the image
of the actual idele inflation of `a`.
`ideleClassInvariantOnQuotientRange_inflation` says that the descended maps
commute with this inflation, under the preceding tower and local-law
hypotheses and explicit reciprocity hypotheses for both `E/F` and `L/F`.
Its proof chooses an idele representative, evaluates both descended maps,
and applies total-invariant preservation.

The provenance is internal: `IdeleTotalInvariant` supplies the sum and its
kernel vanishing, `IdeleCohomologyTower` supplies the actual inflation and
quotient square, the finite and archimedean tower modules supply preservation
of their summands, and `FiniteInvariantDescent` supplies descent to an image.
No original-literature theorem is newly assumed implicitly. This pair does
not prove reciprocity, surjectivity of `j`, injectivity of the descended map,
independence of arbitrary place choices, restriction scaling, or
`GlobalInvariantStatement`. Its invariant has domain exactly the image of
`j`, not all idele-class cohomology.
