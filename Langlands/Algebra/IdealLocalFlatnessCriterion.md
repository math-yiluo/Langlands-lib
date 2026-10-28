# Proof of the ideal variant of the local flatness criterion

`Langlands.Algebra.idealLocalFlatnessCriterion.{u,v,w}` proves exactly
`Langlands.Algebra.IdealLocalFlatnessCriterionStatement.{u,v,w}`.
Let \(R\to S\) be a local homomorphism of commutative Noetherian local
rings, let \(M\) be a finite \(S\)-module with compatible \(R\)-action,
and let \(I\subsetneq R\) be an ideal. Injectivity of
\[
I\otimes_R M\longrightarrow R\otimes_R M
\]
and flatness of \((R/I)\otimes_R M\) over \(R/I\), with its canonical
action through the first factor, imply that \(M\) is flat over \(R\).
The rings and module occupy three independent universes. The theorem
retains the target's scalar compatibility and requires neither finiteness
of \(M\) over \(R\), a nonzero module, nor finite-type or
finite-presentation assumptions.

## Implemented tensor reduction

The theorem `idealTensor_injective_of_quotient_flat` works over an arbitrary
commutative ring \(R\) and an arbitrary \(R\)-module \(M\). For ideals
\(I\subseteq J\), it proves that injectivity of
\(I\otimes_R M\to R\otimes_R M\) and flatness of
\((R/I)\otimes_R M\) over \(R/I\) imply injectivity of
\(J\otimes_R M\to R\otimes_R M\). This helper uses no Noetherian,
local, or finiteness hypotheses. It extracts the ideal-to-larger-ideal
argument from the second proof of Stacks Lemma 10.99.10, which uses it
with \(J\) equal to the maximal ideal.

The published `IdealTensorRelation.exists_eq_one_tmul` uses
`TensorProduct.quotTensorEquivQuotSMul` and surjectivity of the quotient
map to express every element of \((R/I)\otimes_R M\) as \(1\otimes x\).
The private helper `tmul_mem_inclusion_range` uses tensor balancing and
induction on membership in \(I\cdot M\) to put
\(f\otimes x\), for \(f\in J\) and \(x\in I\cdot M\), in the image of
\(I\otimes_R M\to J\otimes_R M\).

For a tensor in the kernel of the map for \(J\), the private helper
`tensor_kernel_mem_inclusion_range` writes it as
\(\sum_i f_i\otimes x_i\). Applying the tensor unit isomorphism
`TensorProduct.lid R M` gives \(\sum_i f_i x_i=0\) in \(M\).
Reduce this relation to the flat \(R/I\)-module \((R/I)\otimes_R M\).
Mathlib's `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero` produces
coefficients \(\overline a_{ij}\) and elements \(\overline y_j\) such that
\[
1\otimes x_i=\sum_j\overline a_{ij}\overline y_j,
\qquad
\sum_i\overline f_i\,\overline a_{ij}=0.
\]
Lift the coefficients to \(a_{ij}\in R\) and the module elements to
\(y_j\in M\). The quotient-tensor identification then shows
\[
d_i=x_i-\sum_j a_{ij}y_j\in I\cdot M,\qquad
b_j=\sum_i a_{ij}f_i\in I.
\]
Tensor bilinearity, balancing and interchange of the two finite sums give
\[
\sum_i f_i\otimes x_i
=\sum_i f_i\otimes d_i+\sum_j b_j\otimes y_j.
\]
Both terms lie in the image of \(I\otimes_R M\), by the preceding helper
and by \(b_j\in I\), respectively. The image of a chosen preimage in
\(R\otimes_R M\) is zero because the two ideal inclusions compose.
The assumed injection for \(I\) kills this preimage and hence the original
tensor. The injective-if-zero-kernel criterion concludes the helper.

## Final assembly

Every proper ideal in a local ring lies in its maximal ideal, by
`IsLocalRing.le_maximalIdeal`. Apply the tensor reduction with
\(J=\mathfrak m_R\), using the given quotient flatness as an instance.
The resulting maximal-ideal tensor injection is the hypothesis of the
published theorem `Langlands.Algebra.localFlatnessCriterion`, imported
from `Langlands.Algebra.LocalFlatnessCriterion`. That theorem, the
Noetherian local criterion 00MK, yields \(R\)-flatness of \(M\) with the
same \(R,S,M\) and all the target's instances. No additional criterion is
left as a hypothesis.

The final theorem's type is the complete named proposition. An unapplied
assignment at the end of the Lean module also checks it at the three
independent universe parameters. The existing statement module and its
imported closure are preserved.

## Sources and provenance

The proof follows the second proof of Stacks Project Lemma 10.99.10,
tag [00ML](https://stacks.math.columbia.edu/tag/00ML). The registered original
is `stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
file `00ML.html`, displayed statement and both proofs. The official page
was checked on 25 October 2026: its statement and second proof agree
with the snapshot, and it has no comments. No project erratum for this
source was found. The statement's paired Markdown explains the
Tor-to-tensor interpretation; this implementation works directly with
the published tensor formulation.

Worker 425 implemented the general tensor reduction and final assembly
from the source proof and Mathlib. Worker 251 independently checked the
three-universe assembly when the 00MK dependency became available.
The imported 00MK theorem has its own proof and provenance documentation.

A development Lake build and complete declaration inspection succeeded with
no diagnostics in the project environment. The theorem has universe
parameters `u`, `v`, and `w`, and uses only `propext`, `Classical.choice`,
and `Quot.sound`. These development checks precede the independent
exact-target validation and semantic review required for publication.
