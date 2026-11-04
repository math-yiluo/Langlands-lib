# Contracted compact-open index and Haar modulus

For a continuous group automorphism taking a compact open subgroup into itself,
the image remains open and has finite index in the original compact subgroup.
Use a Haar measure normalized to give the original subgroup measure one.
The actual `mulEquivHaarChar_smul_preimage` identity gives the image measure
as the Haar modulus. The finite-index measure formula then says the index
times this modulus is one, hence the index is its reciprocal. The argument
uses the actual Haar character and its orientation; it assumes no ambient
unimodularity or right-invariance property.

`contractedIntersection_relIndex` applies this formula to the preimage of an
ambient compact open subgroup under the inclusion of a closed subgroup.
The inclusion is a closed embedding, so this preimage is compact as well as
open. Mapping the subgroup and its contracted image through the injective
inclusion preserves their relative index. The two ambient images are exactly
the literal intersection and its actual conjugate. The result therefore uses
the Library's closed normalizer Haar character with the same orientation.
