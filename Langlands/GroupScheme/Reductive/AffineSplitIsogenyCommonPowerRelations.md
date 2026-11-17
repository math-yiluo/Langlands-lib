# Common-power transport of word commutator relations

This internal construction reindexes annotated reflection-word terms while
retaining their coefficients, degrees and order. It connects literal target
commutator identities to the actual powered source word maps when every
input and output term uses the same root factor.

`reindexWordData` applies the inverse root bijection to each word letter and
its initial root. `wordCommRel_of_equalFactors` transports any supplied
target relation with these terms. The source and target word families use
the compatible words already constructed. On each affine test, the proof
evaluates the target relation at the powered arguments. Actual word
transport supplies the prescribed power for every input and term. A
root-power ring homomorphism fixes integer coefficients, so multiplication
of powers identifies the full ordered products. The target maps are not
assumed to be immersions, and no geometric target hypothesis is needed
for this transport.

The pair version permits every input and term to start at either of two
roots with equal root factors. The A2, B2 and G2 specializations use genuine
normalized target data. Equality of the relevant source and target Cartan
entries forces equality of the two root factors; the genuine target formulas
then transfer to the actual powered source maps. The B2 specialization gives
both standard word relations, and the G2 specialization gives all five.

The coefficient ring is arbitrary for the transport lemmas and the A2
specialization. The normalized B2 and G2 specializations are over a local
ring. The module constructs no
normalized families or ambient homomorphism and proves no global isogeny
theorem.
