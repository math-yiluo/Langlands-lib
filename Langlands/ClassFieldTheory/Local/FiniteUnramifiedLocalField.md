# Spectral local-field structures on finite unramified stages

The named topology and valuative relation in
`Langlands.LocalField.FiniteExtension` equip the actual finite
extension \(X/K\) with a compatible local-field structure.
The algebra map is continuous for the chosen spectral topology.
The intrinsic integer ring for the chosen relation is identified
with the spectral valuation subring by an identity-on-elements
ring equivalence.

If \(X\) is a finite arithmetic-unramified stage in the separable
closure of \(K\), the spectral residue degree is its field degree.
The integer-ring equivalence identifies the residue cardinalities,
so this is also the intrinsic residue degree. The degree formula
for the actual finite extension then gives intrinsic ramification
factor one.

For algebraic embeddings between finite extensions over compatible
local bases, integrality and nonunits are preserved by the induced
local homomorphism on spectral integer rings. If the image of a
nonintegral element were integral, the image of its integral
inverse would become a unit. This contradicts locality. Applying
preservation and reflection of integrality to a quotient proves
compatibility with both chosen valuative relations. This applies
to the embedding into the actual unramified compositum.

The comparison is derived from the Library's spectral local-field
construction and residue maps. It implements the arithmetic of
unramified stages and compatible valuations used in Serre,
*Local Fields* (1979), Chapter III, §5, Theorem 2, printed p. 54,
and Chapter XIII, §3, Proposition 7, printed pp. 193–194.
