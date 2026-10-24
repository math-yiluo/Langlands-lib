# Galois transport in the embedding-labelled matrix algebra

This internal construction uses the actual complex algebra splitting in
`ComplexEmbeddingMatrices`. It retains all its inputs: totally real `E`, a
quadratic totally complex number field extension `K/E`, the algebra structures
and rational scalar tower on `A`, actual Harris signature charts `C`, a CM
section with proof `hΦ`, and a finite `E`-basis `b` of `A`.

For any rational algebra automorphism `s` of the complex numbers,
`ComplexMatrix.coefficientEquiv s` is the rational algebra equivalence
`s ⊗ identity` on `ℂ ⊗[ℚ] A`. Its pure-tensor formula is
`z ⊗ a ↦ s(z) ⊗ a`; it is exactly the existing `changeCoefficients` map when
viewed as a function. Tensor induction proves its identity and composition
laws and its semilinearity for the complex scalar action. The generic
construction needs only a ring `A` with a rational algebra structure.

Write `F = C.embeddingMatrixEquiv hΦ b` for the constructed splitting into
matrices labelled by all embeddings `i : K →+* ℂ`.
`embeddingMatrixGaloisEquiv s` is the ring equivalence

\[
  T_s = F \circ (s\otimes\mathrm{id}) \circ F^{-1}.
\]

`embeddingMatrixGaloisEquiv_apply` proves `T_s(F(x)) = F((s⊗id)(x))`
by cancellation of `F` and its inverse. Surjectivity of `F` reduces the
identity and multiplication laws to the corresponding tensor identities.
These laws are packaged as the monoid homomorphism
`embeddingMatrixGaloisAction`, with `T_(s*t) = T_s ∘ T_t`.
The semilinearity theorem states

\[
  T_s(z\,x)=s(z)\,T_s(x).
\]

It follows from complex linearity of `F` and the tensor semilinearity formula.
The result is a ring equivalence, with a separate semilinearity identity;
there is no assumption that `s` fixes every complex or every real scalar.

`embeddingMatrixGaloisEquiv_evaluation` proves that the function
`i ↦ C.embeddingEvaluation hΦ b i a` is fixed for every `a : A`. It writes
that function as `F(1⊗a)`, using the pure-tensor formula, then uses `s(1)=1`.
Specializing to the center element `algebraMap K A k` gives
`embeddingMatrixGaloisEquiv_center`: the entire function
`i ↦ Matrix.scalar (Fin n) (i(k))` is fixed by `T_s`. This follows from the
existing center-evaluation theorem and does not assert that each scalar
`i(k)` is individually fixed by `s`.

The provenance is the existing scalar-extension algebra, tensor congruence,
and constructed embedding matrix splitting; no new source theorem is assumed.
This module constructs transport on the full product. Deriving its permutation
of individual factors, comparing the individual charts by inner automorphisms,
and the scheme-cocharacter reflex-stabilizer comparison remain separate steps.
