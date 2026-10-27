# Full upper-unipotent orbit classification and ordering

Authors: Worker 179 (Lean proof and documentation), Worker 330 (interface
and algebraic reduction plan).

This module proves the unchanged, closed proposition
`Langlands.Whittaker.UnipotentOrbitStatement.{uF}` as
`Langlands.Whittaker.unipotentOrbit`. The field universe is arbitrary; the
theorem has no additional parameters or hypotheses.

The proof first establishes algebraic adapters over any commutative ring.
A Levi element for the singleton block shape is diagonal. The published
permutation-conjugation entry formula shows that its conjugate by a
permutation matrix is still diagonal and therefore lies in every standard
block parabolic. For an actual singleton-parabolic element `b`, the published
Levi projection and its section give `b = d * u`: the element `d⁻¹ * b`
lies in the projection kernel, and the singleton radical equivalence
identifies that kernel element with the actual full upper-unipotent group.

The published `Geometric.padicParabolicBruhat` supplies the bijection for
the singleton parabolic on the right. Its injectivity gives injectivity for
full upper-unipotent double cosets, because this unipotent subgroup lies in
the singleton parabolic. For surjectivity, write
`g = a * w⁻¹ * b`, split `b = d * u`, and absorb `w⁻¹ * d * w` into the
left parabolic. The resulting representative is precisely the inverse of
the original minimal permutation matrix.

The bijection makes the actual double-coset quotient finite. Canonical
p-adic topology certificates from `GL.Padic`, `GL.CompactOpen` and
`GL.CountabilityProof`, together with closedness of the block parabolic
and full upper-unipotent subgroup, discharge the hypotheses of
`Geometric.closedSubgroupOrbitOrdering`. Finally the published
`OrderedDoubleCosets.classifiedRepresentatives` replaces its representatives
by the exact permutation matrices and supplies the finite equivalence.
That adapter preserves every actual orbit, and hence coverage, disjointness
and all open initial unions. Stored representatives are `w`; their orbits
are `P * w⁻¹ * U`.

This is an internal algebraic and topological derivation of the interface
whose source convention is documented in the unchanged
`UnipotentOrbitStatement.md`. It reuses the published parabolic Bruhat
proof and finite closed-subgroup orbit ordering, rather than formalizing
Rodier's distribution argument anew. It proves no character criterion,
distinguished orbit index, stabilizer equivalence, vanishing assertion or
representation-theoretic heredity theorem.
