# Representability and smoothness of actual finite-algebra units

`Langlands.AlgebraicGeometry.FiniteAlgebraUnits.representability.{u}` proves the
unchanged Library proposition `RepresentabilityStatement.{u}`. For every field
`k : Type u`, commutative `k`-algebra `A : Type u`, and supplied basis
`b : Module.Basis (Fin n) k A`, it proves both `IsIso (candidateMap b)` and
`AlgebraicGeometry.Smooth (candidate b).hom`.

The proof combines three internal constructions derived from the published
determinant-open candidate and its actual universal unit. Their provenance and
individual arguments are documented in the paired
[algebraic-coordinate helper](FiniteAlgebraAffine.md),
[affine comparison](FiniteAlgebraAffineComparison.md), and
[relative-unit gluing helper](RelativeGlobalUnitsGluing.md).

First, the base-changed basis identifies tensor elements with their coefficients.
For a unit, the determinant of multiplication is a unit, so the coefficient
homomorphism extends uniquely to the determinant's away-localization. This
constructs `algebraicPointEquiv` for every commutative coefficient algebra.
The affine comparison identifies the actual fibre-product pullback of
`universalUnit b` with this algebraic map, using both pullback projections and
naturality of global functions. Transport across an affine scheme's `isoSpec`
then gives `candidateMap_affine_bijective` for every affine test over `Spec k`.

Next, `RelativeGlobalUnits.fromUniversalUnit_isIso_of_affine` extends that
bijectivity to every scheme test. Injectivity is checked on an affine open cover.
Local preimages of a unit agree on overlaps by this already established global
injectivity, so they glue to a scheme morphism over the base. Equality of its
pulled-back unit with the given unit is checked on the induced open cover of the
actual fibre product. Componentwise bijectivity gives an isomorphism of the
lifted presheaves. In the final application, `candidateMap b` is definitionally
`fromUniversalUnit (algebraSchemeMap k A) (candidate b) (universalUnit b)`.
Thus the isomorphism concerns precisely the specified natural transformation.

Finally, `candidate_smooth b` proves smoothness of the actual structure map:
the candidate ring is an away-localization of a finite polynomial algebra, and
the two smooth algebra maps compose. The spectrum criterion for smoothness
gives the required scheme morphism property.

The proof preserves the arbitrary universe `u`. The finite basis is the only
finiteness input on `A`. Empty, nonreduced, and non-quasi-compact tests, zero
algebras, rank zero, nilpotents, imperfect fields, and inseparability are all
retained. No comparison of proper-scheme global functions with the ground field
is used. Worker 74 supplied the algebraic, affine-comparison, smoothness, and
final assembly arguments; Worker 416 supplied the arbitrary-scheme gluing
argument.
