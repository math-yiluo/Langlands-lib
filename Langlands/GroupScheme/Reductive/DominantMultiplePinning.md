# Realized characters from top weight lines for a split pinning

Worker 1161. This module is internal and derived. It specializes the top-weight
coefficient of `DominantMultipleCoefficients` to an actual group `G` over a field
with a supplied `p : SplitPinning G`, written `T = p.torus`,
`incl = p.inclusion` and `P = p.rootDatum`. The data `nu`, `i`, `tH`, `j` below
are hypotheses, not constructions:

- `nu` is a cocharacter of `T` pairing positively with every simple root;
- `i : H → G` represents the dynamic parabolic of the opposite of `nu ≫ incl`;
- `tH : T → H` satisfies `tH ≫ i = incl`;
- `j : U → G` has range inside the dynamic unipotent subgroup of `nu ≫ incl`,
  and `U` is unipotent.

## Root signs and parabolic inclusions

- `pairing_eq`: the datum's pairing is the actual lattice pairing
  (`IsRootDatumOf`).
- `exists_root_of_mem_relativeRoots`: actual roots are roots of the datum.
- `parabolic_le_of_dominant`: if `nu` is strictly dominant and `mu` dominant,
  then `P(nu) ≤ P(mu)` and `P(-nu) ≤ P(-mu)` for the dynamic parabolics of the
  composites with `incl`, as subgroup functors on every test scheme. This
  combines `root_sign` with the published root-sign criterion
  `RelativeRoot.parabolic_le_iff_nonnegative_rootSupport`, whose dynamic
  connectedness input is the published `dynamicConnected`.

## Weyl orthogonality

- `cocharacter_comp_eq_of_pairing_eq_zero`: let `σ` be an automorphism of `T` whose
  character action is the reflection of a root `r`. Then `σ` fixes every
  cocharacter `mu` orthogonal to `r`. Invariance of the pairing
  (`latticePairing_characterAut_cocharacterAut`) and the perfect pairing prove it.
- `pairing_coroot_eq_zero`: let `mu` be orthogonal to the root `r`, let `iP`
  represent the dynamic parabolic of the opposite of `mu ≫ incl`, and let
  `tP ≫ iP = incl`. Then every character `ψ` of `P` restricts to a torus character
  orthogonal to the coroot of `r`.

  `IsRootDatumOf` supplies a rational point `n` normalizing `incl` through an
  automorphism acting on characters by the reflection. By the previous lemma, `n`
  fixes `mu ≫ incl` under conjugation. So `n` lies in the dynamic centralizer,
  which is the centralizer of the opposite cocharacter and lies in its parabolic.
  Hence `n` lifts to `P`. Then `characterAut_characterRestrict_eq` shows that the
  reflection fixes the restricted character `x`. Pairing `x - ⟨x, α^∨⟩α = x` with
  `α^∨` gives `2⟨x, α^∨⟩ = 0`.

This is the formal version of the argument that `s_α` fixes the weight of a line
stabilized by a parabolic subgroup containing a representative of `s_α`. Compare
the proof of Milne (2017), Lemma 22.24. Here the parabolic is a dynamic parabolic,
and no root groups are used.

## The construction

- `characterEval_eq_one_of_isUnipotent`: characters of any group, restricted to a
  unipotent group, are trivial on points (`IsUnipotent.comp_eq_one_of_isSplitTorus`).
- `exists_mem_realizedSet_of_diagonal`: let `mu` be dominant and let `ρ` be a
  representation with `(mu ≫ incl) ≫ ρ` diagonal of weights `e ≤ M`. Then some
  `x ∈ realizedSet tH i j` has `⟨x, mu⟩ = topCard e M * M`, and `x` is orthogonal
  to the coroot of every root orthogonal to `mu`.

  The representatives of `P(mu⁻¹)` and `P(mu)` are the published closed
  representatives `Dynamic.Affine.parabolicHom`. The parabolic inclusions above
  factor `i` through `P(mu⁻¹)` and `j` through `P(mu)`. The latter uses the
  inclusion of the contracting subgroup into its parabolic.
  `exists_topWeight_coefficient` then gives the realized coordinate. Its pairing
  with `mu` comes from `latticePairing_eq_of_points`, and its orthogonality from
  `pairing_coroot_eq_zero`.
- `comp_dual_eq_diagonalCocharacter`: the dual of a representation diagonal along
  a cocharacter is diagonal with negated weights.
- `latticePairing_eq_zero_of_diagonal_zero`: if a monomorphic representation is
  trivial along `mu ≫ incl`, then `mu` pairs trivially with every character. The
  points of `mu` become trivial after cancelling the monomorphisms `ρ` and `incl`.
  The latter is a closed immersion by maximality.
- `exists_diagonal_pos`: suppose `mu` pairs nontrivially with some character. Then
  in some actual representation, `mu ≫ incl` is diagonal with a positive largest
  weight. The published `affineLinearEmbeddingStatement` gives a closed embedding
  `ρ₀`. Conjugation by a rational point diagonalizes the cocharacter
  (`exists_innerIso_comp_eq_diagonalCocharacter`). By the previous lemma some
  weight is nonzero. If no weight is positive, the dual representation is used.
- `exists_mem_realizedSet_pos`: for dominant `mu` pairing nontrivially with some
  character, there is a realized `x` with `⟨x, mu⟩ > 0`, orthogonal to the coroots
  of the roots orthogonal to `mu`.
- `exists_neg_mem_realizedSet_of_central`: suppose `mu` is orthogonal to every root
  and pairs nontrivially with some character. Then both dynamic parabolics of
  `mu ≫ incl` are the whole group (`Dynamic.parabolic_eq_top_of_nonnegative_relativeRoots`),
  represented by the identity. The top weight character `ψ` is therefore a
  character of `G`. Its restriction `x` is realized, and so is `-x`, through the
  coordinate of the inverse character
  (`isRealizedCoordinate_characterCoordinate`). Also `⟨x, mu⟩ > 0`, and `x` is
  orthogonal to all coroots.
