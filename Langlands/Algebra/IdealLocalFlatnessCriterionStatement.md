# The ideal variant of the Noetherian local flatness criterion

`Langlands.Algebra.IdealLocalFlatnessCriterionStatement` states Stacks
Project Lemma 10.99.10, tag **00ML**, using an equivalent tensor-injectivity
form of its Tor-vanishing hypothesis. This module defines a proposition;
it does not prove the criterion or formalize the Tor comparison.

Let \(R\to S\) be a local homomorphism of commutative Noetherian local
rings. Let \(M\) be a finite \(S\)-module and \(I\subsetneq R\) an ideal.
If the canonical map
\[
I\otimes_R M\longrightarrow R\otimes_R M
\]
is injective, and \((R/I)\otimes_R M\) is flat over \(R/I\), then \(M\)
is flat over \(R\).

The source instead writes \(\operatorname{Tor}_1^R(M,R/I)=0\).
For a commutative ring, symmetry of Tor and the exact sequence associated
with \(0\to I\to R\to R/I\to0\) identify this vanishing with injectivity
of \(I\otimes_R M\to R\otimes_R M\). The second proof of 00ML explicitly
uses injectivity of \(I\otimes_R M\to M\), referring to Remark 10.75.9.
The tensor unit isomorphism \(R\otimes_R M\simeq M\) identifies that map
with the one in Lean.

In the declaration, `LinearMap.rTensor M I.subtype` is precisely the
tensor of the ideal inclusion with the identity on \(M\). No abstract
Tor object or additional Tor-comparison assumption is used.
The module \((R/I)\otimes_R M\) has its canonical \(R/I\)-action through
the first factor. It identifies with \(M/IM\), with its quotient action;
thus its flatness is the source's quotient-module flatness condition.
Mathlib's `TensorProduct.quotTensorEquivQuotSMul` provides the underlying
quotient-tensor identification.

`I ≠ ⊤` expresses the proper-ideal condition. `Module.Finite S M`
means finiteness over \(S\), with no finiteness over \(R\) required.
The two module structures and `IsScalarTower R S M` specify the
restriction of the \(S\)-action along the given algebra map.
`IsLocalHom (algebraMap R S)` asserts that this map is local.
The rings and module use three independent universes; no equality of
universes, nonzero-module condition, or finite-type condition is imposed.

This is a prerequisite for the Noetherian fibrewise criterion 00MP.
The source offers a proof using Tor and a second proof using the
equational flatness criterion to reduce to the maximal-ideal criterion
00MK. These proof routes are not implemented in this statement module.

The registered original is
`stacks-algebra-flatness-criteria-2026-10-22`, folder SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
file `00ML.html`, Lemma 10.99.10, displayed statement and second proof.
The tensor formulation is an internal presentation of that source
statement, with its translation explained above.
