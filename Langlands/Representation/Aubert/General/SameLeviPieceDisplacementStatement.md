# Strict displacement of the split component on non-identity same-Levi pieces

`SameLeviPieceStrictDisplacementStatement` is an internal intermediate proposition. It
isolates the geometric input of Renard's generic `PQ`-regularity argument (Renard,
*Représentations des groupes réductifs p-adiques*, VII.3). The proposition is proved
unconditionally by `sameLeviPieceStrictDisplacement` in
`Aubert.General.SameLeviPieceDisplacementProof`.

## Statement

The data are a connected reductive group `G` over a nonarchimedean local field `k`, and
represented parabolics `P = MN` (`p, l, r`) and `Q = MU` (`q, lQ, rQ`) with the same Levi
scheme, so `l ≫ p = lQ ≫ q`. Further data are a split component `a : A → M`, a point
`z ∈ G(F)` whose double coset `P(F) z Q(F)` differs from the identity double coset
`P(F) Q(F)`, and a geometric-lemma intersection datum `D` at `z` (Renard VI.5.1). The datum
supplies the parabolic `P' = M ∩ zQz⁻¹` of `M` with Levi `M' = M ∩ zMz⁻¹`, the parabolic
`Q' = M ∩ z⁻¹Pz` of `M` (the Levi of `Q`) with Levi `L' = M ∩ z⁻¹Mz`, and the isomorphism
`φ : L' ≅ M'` given by conjugation by `z`. The last datum is a factorization
`b ≫ D.lQ' ≫ D.q' = a` of `a` through `L'`.

The conclusion is that some `t ∈ A(F)` separates the images of `a(t)` and of its transport
`(b ≫ φ ≫ l' ≫ p')(t)` under the valuation map `Plancherel.rationalValuationImageProjection M`,
from `M(F)` into the valuation lattice of rational characters of `M`. In group terms,
conjugation by `z` does not preserve the valuations of the split component modulo
`M(F)^1`.

## Use

This separation is what makes a polynomial in the unramified coordinates distinguish the
central character of `σψ` on `A(F)` from every generalized character of `A(F)` on the
piece of `σψ` at `z`. See `exists_generic_piece_separation` in
`Aubert.General.RepresentedSameLeviGenericRegularity`.
