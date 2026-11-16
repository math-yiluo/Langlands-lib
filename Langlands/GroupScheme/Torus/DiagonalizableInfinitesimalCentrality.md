# Centrality of a diagonalizable homomorphism through a nilpotent reduction

Worker 626. This internal prerequisite combines the existing Hopf-spectrum
point API, the scheme/Hopf centrality comparison, and character-projector
rigidity. All rings, algebras and the character group lie in any common
universe u. It uses no additional literature assertion.

Let R be a commutative ring, A a commutative Hopf R-algebra, N an additive
commutative group, and π : A → R[N] a Hopf algebra map. Its spectrum is a
homomorphism from the standard diagonalizable group to Spec A.
`isCentral_of_nilpotent_quotient` proves that this homomorphism is central
if its actual scheme base change along Spec(R/I) → Spec R is central,
where I is a nilpotent ideal of R. Centrality is the existing predicate
on every test scheme and every restriction of a test scheme. No
finiteness, flatness, smoothness or immersion hypothesis is imposed.

`specPoint_commute_of_quotient_central` first treats any Hopf map A → C.
If its quotient base change is central, then for any commutative R-algebra
Y on which I acts by zero, any C → Y point image commutes with every
A → Y point. The R-algebra structure map factors through R/I. The
pullback-adjunction point equivalence transports the two points to the
base change; centrality there gives their commutation. Its multiplicative
compatibility transports that equality back. Nilpotence is unnecessary
for this step.

`coeff_eq_of_test_commute` takes a commutative R-algebra B and an algebra
map q : A → B. Use the test algebra B[N], the source point R[N] → B[N]
obtained by scalar extension, and the ambient point A → B → B[N], with
B in degree zero. If these points commute, the Hopf point multiplication
formula identifies their convolution products. Expand comultiplication
of a in A as a finite sum of pure tensors and extract the coefficient at
n in N. The resulting equality is

`q(lact(coeffForm π n)(a)) = q(proj π n(a))`.

For `coeff_sub_mem_of_quotient_central`, set J = I A, B = A/J, and let q
be the quotient map. I acts by zero on B[N], so the first lemma provides
the commutation needed for the coefficient lemma. Equality of quotient
images says that each difference of left and right character coefficients
lies in J. The ideal identity `Ideal.smul_top_eq_map` identifies J with
I times the underlying R-module A. This congruence conclusion itself
requires no nilpotence assumption.

For nilpotent I, `GroupAlgebraCoaction.isCentral_of_coeff_sub_mem` now
equates each pair of commuting idempotent character endomorphisms and
therefore the two tensor coactions. The existing
`HopfSpecCentrality.isCentral_of_rTensor_comul_eq` returns actual
scheme-theoretic centrality.

If the spectrum map is monomorphic,
`commGroupSchemeOfNilpotentQuotient` bundles its unchanged source as a
commutative group scheme using this lifted centrality. The accompanying
`toGrp` lemma is reflexive equality, retaining the standard source and
all its operations.

This unit handles a source already presented by its standard group
algebra and an affine Hopf-spectrum target. It does not provide descent
for an arbitrary multiplicative-type source, lift multiplicative type
from a special fibre, or prove the host arbitrary-base fibrewise
central-isogeny criterion.
