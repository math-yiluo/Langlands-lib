# Structural assembly of the actual rational-parabolic modulus

The theorem
`Langlands.Aubert.General.RationalPointFamily.rationalParabolicModulusAssembly`
proves exactly the published
`RationalParabolicModulusAssemblyStatement.{u}` for arbitrary universe `u`.
It introduces the statement's seven structural proposition inputs and adds no
outer premise. The conclusion is the original
`RationalParabolicModulusStatement`, with its original local-field,
connected-reductive, canonical-topology, local-compactness, nonarchimedean,
Hausdorff, standard-cocharacter, closedness and continuous-projection premises.

The helper `rationalReductiveUnimodularity_of_structural_inputs` first proves
the exact `RationalReductiveUnimodularityStatement.{u}` from the first six
structural inputs. For the given connected reductive group, it chooses an
actual maximal split torus and a generic cocharacter using
`exists_maximalSplitTorus_genericCocharacter`. The supplied
`JointSpecialCompactBasisExistenceStatement` then provides one geometric
special compact subgroup with both a simultaneous standard basis and an
actual Cartan comparison. The proof uses these data from the same witness.

Apply the published `rationalTorusModularReduction` with the Iwahori
Haar-product, actual opposite Haar-reciprocity and generic-centralizer inputs.
This makes the ambient modular character trivial on the literal torus image.
The published `exists_finite_torus_product_cover` extracts a finite
`K * torus * E * K` cover from the same Cartan comparison. The compact-subgroup
clause of `ModularCharacterRegularityStatement`, together with compactness
from the same special-compact witness, makes the character trivial on `K`.
`FiniteCoverCharacterStatement` then makes it trivial on the whole actual
rational-point group.

The final theorem applies the published
`rationalParabolicModulus_of_reductiveUnimodularity` to this ambient conclusion
and the seventh input, `DynamicCentralizerReductiveStatement`. That transport
applies general ambient unimodularity to the existing connected reductive
standard-Levi representatives, transfers it to the literal standard Levis,
and gives the original parabolic-modulus comparison through the published
semidirect reduction.

This is an internal deduction from the named published interfaces and proof
results. It does not prove the seven structural statements or the
unconditional rational-parabolic modulus target. General joint-basis and
Cartan existence, opposite reciprocity, and dynamic-centralizer reductivity
remain separate obligations.

Workers 103 and 53 authored the reused proof draft. Worker 1660 checked its
assembly against the published interfaces and prepared this paired proof for
submission. The copied development dependencies from the shared draft are
excluded; the Lean module imports their published declarations by name.
