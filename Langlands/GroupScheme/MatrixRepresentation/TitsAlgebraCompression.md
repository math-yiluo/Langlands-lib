# Tits algebras of compressed representations

This module identifies the Tits algebra of a subquotient representation with
a compression of a descended algebra. It is the representation-theoretic
part of Tits's simple-weight comparison (*Représentations linéaires
irréductibles d'un groupe réductif sur un corps quelconque*, J. reine angew.
Math. 247 (1971), Proposition 3.4, pp. 204–205).

- `titsAlgebra_eq_compressed`: suppose
  - `ρ` is a representation of `G_K` on `K^N` whose Tits algebra lies in a
    twisted-fixed `k`-form `B ≤ twistedFixed P` (invertible `P σ`);
  - `F : K^N → K^r` and `E : K^r → K^N` satisfy `F E = 1` and `E F ∈ B`;
  - `ρ'` is an irreducible representation of `G_K` on `K^r`, with scalar
    self-intertwiners and invertible intertwiners `ρ' → ρ'^σ`;
  - the coefficient matrices of `ρ'` are the compressions
    `X_φ(ρ') = F X_φ(ρ) E`.

  Then `titsAlgebra ρ' = compressed B F E`. The generators of the Tits algebra
  of `ρ'` lie in the compression, which is a subalgebra
  (`Algebra.GaloisTwistedMatrix.compressed`). The Tits algebra has dimension
  `r²` (`finrank_titsAlgebra`). The compression lies in a twisted-fixed algebra
  (`compressed_le_twistedFixed`, `isUnit_compressed_twist`), so its dimension
  is at most `r²` (`finrank_twistedFixed_le`). The two subalgebras are therefore
  equal.

In this development's proof of additivity (`Reductive/TitsAdditivity`),
`E` parametrizes a complement of `Y` in `X`, cut out by an adapted
idempotent `f ∈ B`, and `F` is the corresponding projection. The
compression identity expresses that `X/Y ≅ ρ'`. Combined with the Brauer
equivalence between the corner `f B f` and `B`
(`Algebra/GaloisTwistedCorner`), this gives `[A_{X/Y}] = [B]`. The choice of
a complement through an adapted idempotent is this development's own. Tits's
proof of Proposition 3.4 instead descends the invariant flag `Y ⊆ X` to `k`
and passes to the quotient through the submodule correspondence of §1.4
(pp. 197–198).
