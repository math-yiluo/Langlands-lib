# Continuous complex powers of the normalized absolute value

Worker 1555 derives this internal construction from the existing continuous
unramified character and spectral parameter. No external assertion is added.
The inputs are an arbitrary finite p-adic field and its specified topological
data; the prime and field universe remain unrestricted.

`normalizedAbsPowerCharacter T s` is the existing
`unramifiedCharacterContinuous` with uniformizer value `q^(-s)`, where `q`
is the specified residue cardinality. The existing constructor supplies
both multiplication and continuity, using the actual normalized order.

`normalizedAbsPowerCharacter_apply` proves that its value at a field unit
is `exp(s * log(|a|))`, where the logarithm is real and the absolute value is
the residue-normalized one. The absolute value is strictly positive on
units. The proof substitutes `|a| = q^(-ord(a))`, uses the real logarithm of
an integer power, and rewrites the integer power of an exponential as an
exponential. The remaining exponent identity is polynomial arithmetic.

The zero and addition laws follow by character and unit extensionality and
the corresponding exponential laws. At parameter one the character is the
existing `normalizedAbsCharacter`, by the real exponential-logarithm
identity on positive values. No reciprocity, epsilon system or harmonic
normalization is constructed.
