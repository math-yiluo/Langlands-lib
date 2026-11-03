# Finite regular subspaces

This internal construction implements the finite regular subrepresentation step
in Milne, *Algebraic Groups* (2017), Theorem 4.27, using the finite-translation
lemma already proved in `AffineLinearEmbedding.Comodule`.

For a finite subset `S` of a coalgebra over a field, `regularSpan S` is the
linear span of all its right translates by linear functionals. The file proves
that this subspace contains `S`, is finite dimensional, and is stable under
right translation. Finiteness uses the existing finitely generated bound for
the translates of each generator and takes their finite sum.

`tensorSubspace V A` is the actual image of `V ⊗ A` in `B ⊗ A`.
`exists_subspace_coaction` proves that a subspace stable under all functional
translations admits a coaction lifting the ambient comultiplication. The proof
chooses a linear retraction onto the subspace and checks the required equality
by contraction with every linear functional. Finally,
`translate_mem_tensorSubspace` shows that translation evaluated at any
coefficient-valued linear map lands in this scalar extension. The coefficient
module is arbitrary; no reducedness or field condition is imposed on it.

These are algebraic ingredients for the later stabilizer construction, rather
than a claim that the scheme quotient or the projective orbit has been
constructed.
