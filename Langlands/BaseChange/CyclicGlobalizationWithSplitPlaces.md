# The distinguished completions and two split finite places

`CyclicGlobalizationWithSplitPlacesStatement` takes a cyclic extension
of characteristic-zero nonarchimedean local fields with the relative
module topology. It gives a cyclic Galois extension of number fields
of the same degree. All lower infinite places and two distinct lower
finite places split, with the global generator acting by a cyclic
shift. Both finite split places are distinct from the distinguished
finite place. At that place there is a unique upper completion, and
the given local fields identify bicontinuously with the two
completions. These identifications respect the scalar embeddings
and the action of the upper generator.

Apply `cyclicFieldGlobalization` with the given degree and generator.
The field structure on the local tensor product determines the unique
upper place by `distinguishedCompletionGlobalization`, which also
transports the generator. Choose the two split places successively by
avoiding the distinguished place and then the first split place. The
order of the global generator equals the size of the Galois group,
giving cyclicity, and the adelic quotients are compact by
`compactSpace_adeleQuotient`.

The number-field choice is used in Arthur–Clozel, Chapter 1, proof of
Proposition 6.9(ii), printed p. 69 (PDF p. 83), literature ID
`arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
