# Henniart's globalization from Harris's exact-stabilizer proposition

`Langlands.Global.henniartGlobalizationExactStabilizerReduction` proves
`HenniartGlobalizationExactStabilizerReductionStatement` at independent
universes `uK`, `uQ`, `uW`, and `uP`. It uses the five local premises of that
statement and `Harris.Proposition48ExactStabilizerStatement`. It adapts the
published generator construction in `HenniartGeneratorRealization` and
its assembly in `HenniartGlobalizationReduction`.

For one paired-place configuration, the image of the completion Weil map
at the primary place is conjugate to the specified Weil subgroup. The proof
transports the inducing character by this conjugation and uses geometric Weil
reciprocity to obtain a character of `F'ˣ`. Its values on the valuation-ring
units are prescribed using `harrisDatumCharacterRealizationExactStabilizer`.
The resulting datum is passed directly to the exact-stabilizer form of
Harris's proposition. The weak automorphic induction it returns, together
with relative regularity and conjugate inverse from the datum, gives a
witnessed generator through `exists_witnessedGenerator_inducedReciprocity`.
The two local characters agree on units. The construction twists by the
inverse of the resulting unramified discrepancy and uses the induction
projection formula to realize the original induced class.

At the common base place, `completion_ringHom_ext` identifies the two
continuous completion maps from their agreement on the number field.
For a given finite quotient `q`, the proof chooses an open normal subgroup
whose Weil preimage lies in `factoringKernelClosure K q`. Its fixed field
has finitely many intermediate extensions. The common-base field realization
supplies the paired-place configurations for them, and `familyGaloisOverfield`
puts all their primary extensions in a single finite Galois overfield. The
transported Brauer span theorem reduces coverage to the induced characters
above the transported kernel. Each inducing character has modulus one by
`norm_eq_one_of_trivial_on_finiteIndex`, and the generator construction
gives its witness. The submodule span argument then gives the desired
coverage in `RelativeGaloisGlobalization`.

This is the Library's relative form of Henniart 2000, Théorème 3.1 and
§§3.3–3.7, pp. 448–451 (`henniart-2000-simple-proof`). The invocation of
Harris 1998, Proposition 4.8, p. 201, takes the auxiliary stabilizer in
condition (4.12), p. 204 (`harris-1998-local-langlands`).
