# Distance-additive composition at an arbitrary compact Haar scale

Let the ambient group be connected reductive over a nonarchimedean local field.
For a distance-additive triple with common centralizer, the ordered radical
charts give the structural premise of the published composition theorem.
`exists_splitsAlong_of_distanceAdditive` constructs a compact open subgroup with
both splittings used by that theorem. The construction cuts first along the
middle cocharacter and then along the first. The resulting subgroup splits the
final radical along the first cocharacter. It also splits the first opposite
radical along the middle. The part of the middle radical in that opposite
radical belongs to the final radical by distance additivity. Factoring the
first opposite component and multiplying its middle part into the first
component gives the required splitting of the final radical along the middle.

`ScaledPairComposition` states the existence of a uniform positive scalar for
composition at the input compact Haar normalization. Its proof,
`exists_pairFamily_comp_smul`, applies composition at the auxiliary compact open
and transfers the full domains and three integral operators to the input compact
open using the quotient measure comparison. The resulting scalar is the product
of the two consecutive quotient Haar scales divided by the direct quotient Haar
scale. It is strictly positive and depends on the compact opens and the three
cocharacters. The identity applies to the actual normalized induction maps
with squared-modulus compatibility for each ordered pair, namely the two
consecutive pairs and the direct pair. The parameter must lie in the full
integral domains of all three maps.
The proof is derived from the Library's composition, compact splitting,
ordered radical factorization and Haar scaling results.
