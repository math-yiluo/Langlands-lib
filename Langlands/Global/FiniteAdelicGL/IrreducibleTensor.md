# Irreducible finite-adelic tensors and their local embeddings

For a family of irreducible admissible complex representations of the completed-local
matrix groups, fix integral-invariant nonzero reference vectors outside a finite set.
`tensorRepresentation_isIrreducible` uses admissible Schur to obtain scalar
self-intertwiners at each place, applies restricted tensor irreducibility, and
pulls back along the finite-adelic matrix equivalence with the restricted product.

`localTensorEmbedding` fixes a complementary tensor vector \(y\) and sends \(x\)
to \(x \otimes y\) under the existing equivariant separation of the local factor.
If \(y\) is nonzero, the pure tensor of a nonzero \(x\) and \(y\) is nonzero, so the
map has zero kernel. When each local carrier is nontrivial, the complementary
restricted tensor is nontrivial and provides such a \(y\) at each place.

These are the finite-adelic irreducibility and local recovery steps for the
restricted tensor described in R. P. Langlands, *On the notion of an automorphic
representation* (1979), Lemma 1 and its proof, printed p. 203, PDF p. 198 of
Corvallis Part I (`langlands-1979-notion-automorphic-representation`). The Lean
proof uses the Library's irreducibility and separation results for the algebraic
restricted tensor.
