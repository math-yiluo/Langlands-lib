# Actual cocenter descent from an ordinary Galois-fixed coweight

This internal adapter works with an actual commutative group homomorphism
`g : T → Q`, an actual torus map `i : T → G`, and a supplied finite reduced
root datum `P` for its base change to a field extension `E/k`. Both fields
and the root-index type lie in arbitrary universe `u`. The ambient group is
affine and locally of finite type, the base-changed torus is split, and the
base-changed map is a closed immersion.

The input coweight `ν` is fixed by the ordinary cocharacter Galois action.
The actual pullback on characters is assumed injective, with image exactly
the annihilator of the coroots whose roots evaluate to zero on `ν`.
These remain explicit geometric comparison inputs.

`IsRootDatumOf.finite_abstractWeylGroup` embeds the abstract Weyl group in
the actual normalizer character image, using the imported inclusion and
Mathlib's injectivity of the full weight representation of root-datum
automorphisms. Finiteness of that actual image therefore implies finiteness
of the abstract group; equality of the two images is not needed. This lemma
does not require splitness, reductivity, finite root index or maximality.

`coweightCocenterRootDescent` constructs a genuine root base `B` and proves
`CocenterRootDescentData` for the simple subset
`{j : B.support | P.root' j ν = 0}`. The imported split-torus Weyl-image
finiteness theorem supplies finiteness of the actual image. The preceding
embedding supplies finiteness of the abstract Weyl group and hence of the
zero-root reflection subgroup.

The compatible coweight-face construction chooses the root base and
identifies the selected simple-coroot annihilator with the full zero-root
coroot annihilator. For each ordinary Galois automorphism, the actual
root-datum Galois action has the ordinary character map and the inverse
ordinary cocharacter map, in Mathlib's contravariant convention. Fixedness
of `ν` permits the imported based correction. Its weight map fixes the
entire actual pullback image. Its inverse coweight map, paired with the
weight correction, gives exactly the simultaneous pairing and simple
coroot formulas of `CocenterRootDescentData`. Its simple permutation
preserves the zero-root subset.

This is a derived internal construction from the imported APIs, rather
than a transcription of a literature statement. It does not choose a
maximal torus or splitting extension, construct an actual root datum,
construct the fixed coweight, or prove the stated character-image
comparison. It therefore does not by itself prove the unconditional
Levi cocenter root-model statement.
