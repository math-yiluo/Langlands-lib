# Detecting monomorphisms of group schemes on residue-field fibres

`kernelBaseIsoOfResidueFieldMonos` constructs the canonical isomorphism from the
full kernel to the base, and its forward-map formula identifies it with the
kernel structure map. It uses the same hypotheses as the detection theorem
below.

`mono_of_residueField_fibres` proves the global monomorphism detection criterion
for any locally finitely presented source group scheme over a base scheme `S`.
It assumes that `S` is locally noetherian or that the target is locally of finite
type, and that every canonical residue-field fibre of the homomorphism is
monomorphic. It concludes that the homomorphism is monomorphic. The theorem
assumes neither separatedness nor flatness, smoothness, commutativity or
multiplicative type of either group.

The proof is an internal composite of the kernel presentation and triviality
APIs and the trivial-fibres lemma. The full kernel is locally of finite
presentation under the stated hypotheses. Kernel base change converts each
fibrewise monomorphism hypothesis to triviality of the corresponding kernel
fibre. The unit-section argument of `isIso_hom_of_residueField_fibres` then
makes the full kernel trivial. The all-test kernel criterion makes the
original homomorphism a monomorphism.

The isomorphism construction applies `residueFieldTrivialityIso` to this same
full kernel; the forward-map equation is definitional. All three prerequisite
APIs are imported from the Library.

This supplies the global assertion 6.7 of
`MultiplicativeTypeMonomorphismSpreadingStatement` once its multiplicative-type
source is known locally of finite presentation. The separate local spreading
assertion 6.6 and the exact two-part statement remain outside this module.
