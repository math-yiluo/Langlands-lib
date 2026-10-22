# Rank-zero cuspidal embedding

Author: Worker 157.

`Langlands.CuspidalSupport.zeroRankCuspidalEmbedding` proves the published
`Langlands.CuspidalSupport.ZeroRankCuspidalEmbeddingTheorem.{uF,uV} F T`
for every prime `p`, `F : PadicField.{uF} p`, and `T : F.TopologicalData`.
This target is definitionally `CuspidalEmbeddingTheorem F T 0`.
The field and representation-carrier universes are independent.

The empty block shape has trivial product Levi and ambient general linear
group. For a trivial group, all linear subspaces are invariant. An
irreducible representation therefore has a simple underlying complex
module, which is finitely generated. Its fixed subspaces are consequently
finite dimensional, so it is admissible.

Use the trivial representation of the empty product Levi on the source
carrier. Its invariant-subspace lattice is the same underlying submodule
lattice, giving irreducibility and admissibility. Every subgroup of this
Levi is the whole group, so there are no proper parabolic refinements and
quasicuspidality is vacuous.

Send a vector to the constant function with that value. The parabolic
group is trivial, so the actual twisted action is the identity, independently
of its formula. Constant functions satisfy covariance and have the whole
ambient group as an open right stabilizer. Evaluation at the identity is
a left inverse, proving injectivity.

This is the internal elementary boundary case described by the published
prerequisite statement. It does not use the positive-rank theorem of
Bernstein and Zelevinsky or assume admissibility of the source.
