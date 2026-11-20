# Block constant terms in the ordered block matrix model

The weight of an original matrix coordinate equals the negative index of its
ordered block. The interior cuts before a coordinate are in bijection with the
positive boundary indices up to the block containing that coordinate. The
composition's prefix sizes identify that block with `BlockShape.index`.

With these weights, the prescribed identity entries of the block unipotent
matrix give precisely the parabolic condition below the block diagonal and
the identity condition on each diagonal block.
`blockShapeConstantTerm` uses the existing adelic-points equivalence to
evaluate the normalized integral on the original adelic matrix group.
The comparison makes the term invariant under left multiplication by the
original radical and equivariant for right translation on the ambient group.

This comparison identifies the matrix block parabolics for the constant
terms in Langlands (1979), Lemma 4 and the proof of Proposition 2, printed
p. 204 (Corvallis Part I, PDF p. 199). The registered source is
`langlands-1979-notion-automorphic-representation`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
