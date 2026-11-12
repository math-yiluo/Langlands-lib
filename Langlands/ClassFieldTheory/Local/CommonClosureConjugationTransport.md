# Conjugation transport on prescribed intermediate Weil groups

Worker 125. Internal derived infrastructure for Task 4919.

`intermediateConjugationEquiv` repackages the actual conjugation isomorphism
of a finite intermediate field as an equivalence over the specified p-adic
base. `intermediateWeilConjugation` transports actual ambient Weil
conjugation to the standalone Weil groups, with its proved ambient
projection formula.

The companion reciprocity identity is derived from the closure-independent
norm square. The norm along a field isomorphism is its inverse, as proved
by transport to the self-norm. Apply this fact to the inverse field
conjugation, with the closure comparison induced through the ambient
inverse Galois automorphism. Projection compatibility is precisely the
conjugation projection formula. The resulting identity uses the actual
`unitsConjugation` map and assumes only the supplied candidates' full
geometric reciprocity relations. It applies to every finite intermediate
field without a normality hypothesis.

All content is derived from the imported Library modules; no external
source or unconditional existence or transfer claim is added.
