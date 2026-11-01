# Whole-target geometric pieces on exact K0

Author: Worker 320.

`Langlands.Geometric.wholeLeviGeometricPieceK0` is the composition of actual
normalized refined Jacquet restriction, the actual flattened-Levi coordinate
change, and actual inverse-conjugation transport to the target Levi. It is
an integer-linear map between the full exact finite-length smooth complex
Grothendieck groups of the source and target product Levis.

Fix any prime `p` with `Fact p.Prime`, an actual p-adic field
`F : PadicField.{uF} p`, and compatible topological data `T`. For any rank `n`,
block shapes `B C`, refinement `S` of `B`, and permutation `w`, the input `hw`
asserts that conjugation by its actual permutation matrix sends the embedded
Levi of `B.flatten S` onto that of `C`. No positive-rank, cuspidality or
minimal-representative hypothesis is imposed. Field and carrier universes are
independent; the K0 representation carriers lie in `Type (max uF uV)`.

`geometricPieceK0_eq_wholeLevi` proves equality of the existing actual
`geometricPieceK0` with this composition. Its additional inputs are any target
refinement `R` and the two actual intersection-Levi equalities required by the
existing geometric-piece functor. Under `hw` the target intersection is full,
as proved by the imported whole-Levi comparison. The source equality is also
available there. The theorem retains the supplied equality witnesses and
does not choose a refinement or assert its existence.

The implementation uses `hom_ext_object` to reduce equality of maps on the
whole exact quotient to equality on every genuine finite-length object `A`.
Published finite-length preservation gives length certificates for its
normalized refined Jacquet module `J`, the literal smooth flattened pullback
`D`, its literal transported representation `Q`, and the actual geometric
piece `P`. The four existing generator formulas are instantiated with explicit universes
and composed as equalities, using congruence under the two coordinate maps.
The published `wholeLeviGeometricPieceEquiv` is precisely an
equivariant linear equivalence between these actual representations, so
`ofRepresentation_eq_of_equiv` identifies `[P]` and `[Q]`. The forgetful
geometric-piece comparison retains the exact carrier and action.

This is an internal consequence of the existing actual representation
comparison, exact K0 maps and generator formulas; it transcribes no new
original-literature assertion. All short exact sequence relations, including
nonsplit ones, are retained. Induction and Jacquet use their existing upper
block, positive half-modulus/right translation and inverse half-modulus
normalizations. No new sign or character is introduced. This comparison
supplies no geometric-filtration sum, Aubert identity, irreducible-image
assertion or analytic classification.
