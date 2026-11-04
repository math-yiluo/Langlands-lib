# Standard parabolic structure from the dynamic statements

Author: Worker 923.

This module turns facts about the dynamic subgroups `P(χ)(k)`, `Z(χ)(k)`,
`U(χ)(k)` of a cocharacter into facts about the actual standard subgroups
`P_I(k)`, `L_I(k)`, `U_I(k)` indexed by a set `I` of simple relative roots.
It does this for the closedness of the standard parabolic and for
finite-length preservation by the actual standard functors. Every result
assumes the published `StandardCocharacterStatement`, together with a
connected reductive `G`, a maximal split torus `i` and a generic
cocharacter `ν`. The topology on `G(k)` is the canonical `pointTopology`,
which is by definition `rationalPointTopology k G.X`.

This is internal, derived content with no literature source of its own.
It only transports existing Library results and statements along subgroup
equalities. It gives the inputs that the standard family needs in order to
build the actual alternating operator `D_G` (Aubert, Theorem 1.7), as
recorded in the hypotheses of `standardParabolicFiniteLength` and
`RationalInvolutivityStatement`.

## Declarations

All declarations are in the namespace
`Langlands.Aubert.General.RationalPointFamily`.

- `exists_standard_eq_dynamic hStandard hG hi hν I` gives a cocharacter
  `χ : 𝔾_m ⟶ G` such that the actual standard parabolic, Levi and unipotent
  point subgroups for `I` equal the rational points of `Dynamic.parabolic χ`,
  `Dynamic.centralizer χ` and `Dynamic.unipotent χ`. The published
  `exists_parabolic_eq_dynamic` gives only the parabolic equality.
- `isClosed_standard_parabolic hStandard hG hi hν I` proves that
  `parabolic i ν I` is closed in `G(k)` for `pointTopology`.
- `standard_induction_preservesFiniteLength hStandard hG hi hν hDyn` takes
  `hDyn : DynamicInductionFiniteLengthStatement.{u, uV}`. For every
  locally compact nonarchimedean `G(k)`, every `I` and every closedness proof
  `hU` of `unipotent i ν I`, it proves that the actual normalized induction
  functor `normalizedInductionFunctor.{u, uV}` of the standard semidirect
  decomposition `isSemidirectDecomposition_of_standardCocharacterStatement`
  preserves finite length.
- `standard_jacquet_preservesFiniteLength hStandard hG hi hν hDyn` is the
  same statement for the normalized Jacquet functor `jacquetFunctor.{u, uV}`.
  It takes `hDyn : DynamicJacquetFiniteLengthStatement.{u, uV}`.

The finite-length lemmas are conditional: their dynamic inputs are
published statements that are not yet proved (Renard VI.6.2 and VI.6.4).
The lemmas do not prove those statements. The universe `uV` of the
representation carriers is arbitrary. The rational Aubert statements use
`uV = max (u + 1) v`.

## Proofs

`exists_standard_eq_dynamic` applies `hStandard` to the root set
`rootSet i ν I`. That gives a standard cocharacter `ζ`, together with
equalities of the standard parabolic, Levi and unipotent subgroup schemes
with the dynamic ones of `χ = groupHom ζ ≫ i`. Taking carriers at the
identity point `Over.mk (𝟙 _)` gives the three rational-point equalities.

`isClosed_standard_parabolic` rewrites `parabolic i ν I` by the published
`exists_parabolic_eq_dynamic` and applies the published
`isClosed_dynamic_parabolic`. The `T2Space k` instance it needs comes from
`Langlands.BruhatTits.localField_t2Space`. Affineness of `G.X.left` comes
from `isAffine_of_isAffineHom`.

Both finite-length lemmas follow one pattern. They obtain `χ` and the three
equalities from `exists_standard_eq_dynamic`, and transport the closedness
proof `hU` to `Dynamic.unipotent χ`. They then apply `hDyn` to `χ`. The
semidirect-decomposition proof and `hU` are generalized and reverted, and
the goal is rewritten by the three equalities. After the rewrite the goal
is the dynamic instance up to proof irrelevance of these two proofs. The
continuity half of the standard-family topology input is not reproved here.
It is the published `continuous_standard_projection`, which uses the same
generalize/rewrite pattern.
