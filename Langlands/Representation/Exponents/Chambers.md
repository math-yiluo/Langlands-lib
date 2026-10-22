# H-maps and positive root cones for block Levis of `GL_n`

Author: Worker 23.

This module adds Harish-Chandra's H-map for the block Levi of a standard
parabolic of `GL_n(F)` and for its split centre, together with the positive
root cones used in the square-integrability and temperedness inequalities. It
works in the published coordinates of `Exponents/Jacquet`: the real part `x` of a
character `χ` of the split centre `(F^×)^r` satisfies `|χ(a)| = ∏ |a_j|^(x_j)`
(`T.IsRealPartOf χ x`).

Two coordinate systems appear, and the module keeps them apart:

- **split-centre coordinates** `x ∈ ℝ^r`: real parts of characters of the block
  scalars `(a_1 1_(n_1), …, a_r 1_(n_r))`, as in `IsRealPartOf`;
- **determinant-twist coordinates** `t ∈ ℝ^r`: the character
  `m ↦ ∏ |det m_j|^(t_j)` of the Levi, as in the exponents `u_i` of the published
  `Classification/LanglandsData`.

On block scalars `|det(a_j 1_(n_j))| = |a_j|^(n_j)`, so the two are related by
`x_j = n_j t_j` (`isRealPartOf_blockSize_mul_iff`). The cones of this module are
in the coordinates `x`. The regular chamber of the published Langlands data,
`StrictAnti t` (`t_1 > ⋯ > t_r`), stays in the coordinates `t`.

## Root cones (namespace `Langlands.Exponents`)

For `x : Fin r → ℝ`, with coordinates indexed from `0`:

- `partialSum x k` is `x_0 + ⋯ + x_(k-1)`, the sum of the coordinates of index
  below `k`.
- `IsPositiveRootCone x`: `∑ x_i = 0` and `partialSum x k > 0` for `0 < k < r`.
- `IsClosedPositiveRootCone x`: `∑ x_i = 0` and `partialSum x k ≥ 0` for
  `0 < k < r`.
- `IsPositiveRootCone.isClosedPositiveRootCone`: the open cone lies in the closed
  one.
- `simpleRoot r k` is the vector `e_(k-1) - e_k`. For `0 < k < r` it is the real
  part of the simple root `a ↦ a_(k-1) / a_k` of the split centre.
  `sum_smul_simpleRoot_apply` computes the coordinates of `∑ c_k (e_(k-1) - e_k)`.
- `isPositiveRootCone_iff_exists_simpleRoot`: `x` lies in the open cone exactly
  when `x = ∑_(0<k<r) c_k (e_(k-1) - e_k)` with every `c_k > 0`. The coefficients
  are the partial sums. This justifies the name: the open cone is the set of
  strictly positive combinations of the simple roots.
- `isPositiveRootCone_iff_pairing`: `x` lies in the open cone exactly when
  `∑ x_i = 0` and `∑ x_i h_i < 0` for every monotone, nonconstant integer vector
  `h`.
- `isClosedPositiveRootCone_iff_pairing`: `x` lies in the closed cone exactly when
  `∑ x_i = 0` and `∑ x_i h_i ≤ 0` for every monotone integer vector `h`.

The pairing theorems are proved by summation by parts (Mathlib's
`Finset.sum_range_by_parts`). For `∑ x_i = 0` this gives
`∑ x_i h_i = -∑_(0<k<r) (h_k - h_(k-1)) · partialSum x k`. Conversely, the step
vector `(0, …, 0, 1, …, 1)` with `k` zeros pairs to `-partialSum x k`.

## H-maps (namespace `Langlands.PadicField.TopologicalData`)

For a p-adic field `F` with realization `T`, let `q` be `T.residueCardinality`
and `|·|` the residue-normalized `T.normalizedAbs`.

The uniformizer unit is the shared `Langlands.LocalFactor.PadicAbelian.uniformizerUnit`
from [LocalField/Uniformizer](../../LocalField/Uniformizer.md). Its construction
was moved unchanged from the abelian local-factor module; the private duplicate
here has been removed.

- `T.logAbs a`, for a unit `a`, is `log_q |a| = -ord a`, an integer.
  `normalizedAbs_eq_zpow_logAbs` gives `|a| = q^(logAbs a)`. It is additive
  (`logAbs_mul`, `logAbs_one`, `logAbs_pow`) and order-preserving
  (`logAbs_le_logAbs_iff`, `logAbs_eq_logAbs_iff`).
- `T.centreHMap a`, for `a : Fin r → F^×`, is `(log_q |a_j|)_j`. It is additive
  (`centreHMap_mul`, `centreHMap_one`) and surjective onto `ℤ^r`
  (`centreHMap_surjective`, using powers of the uniformizer).
- `T.leviHMap B m`, for `m` in the block Levi `B.Levi F`, is
  `(log_q |det m_j|)_j`. It is additive (`leviHMap_mul`, `leviHMap_one`), and
  `determinantNorm_eq_zpow_leviHMap` gives `|det m_j| = q^(H_M(m)_j)`.
- `leviHMap_blockScalarLevi`: on block scalars, `H_M(a)_j = n_j · H(a)_j`.
- `prod_normalizedAbs_rpow`: `∏ |a_j|^(x_j) = q^⟨x, H(a)⟩`.
- `isRealPartOf_iff_pairing`: `T.IsRealPartOf χ x` holds exactly when
  `|χ(a)| = q^⟨x, H(a)⟩` for all `a`.
- `isRealPartOf_blockSize_mul_iff`: `(n_j t_j)_j` is the real part of `χ` exactly
  when `|χ(a)| = ∏ |det(a_j 1_(n_j))|^(t_j)` for all `a`. This is the coordinate
  bridge `x_j = n_j t_j`.
- `one_lt_residueCardinality_real`: `1 < q` as a real number.

## Cones and characters

For `T.IsRealPartOf χ x`:

- `IsRealPartOf.sum_eq_zero_iff`: `∑ x_j = 0` exactly when `χ` is unitary on the
  diagonal scalars `(c, …, c)`.
- `IsRealPartOf.isPositiveRootCone_iff`: `x` lies in the open cone exactly when
  `χ` is unitary on the diagonal scalars and `|χ(a)| < 1` for every `a` with
  `|a_1| ≤ ⋯ ≤ |a_r|` whose absolute values are not all equal.
- `IsRealPartOf.isClosedPositiveRootCone_iff`: `x` lies in the closed cone exactly
  when `χ` is unitary on the diagonal scalars and `|χ(a)| ≤ 1` whenever
  `|a_1| ≤ ⋯ ≤ |a_r|`.

These are the inequalities of Casselman's criteria for a single character,
written for block scalars. The module states neither the square-integrability
criterion nor the tempered criterion for a representation: both quantify over
all standard parabolics and all exponents, and they remain separate statements
(Worker 19's exponent criteria).

## Sources

A. J. Silberger, *Introduction to harmonic analysis on reductive p-adic groups*,
Mathematical Notes 23, Princeton University Press, 1979 (registered source
`silberger-1979-harmonic-analysis`, SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`), section 0.4,
printed p. 8 (PDF page 14): "Given χ ∈ X(G) and x ∈ G, we set
⟨χ, H_G(x)⟩ = log_q |χ(x)|. This defines a continuous homomorphism
H_G : G → Hom(X(G), ℤ). Set °G = ∩_{χ ∈ X(G)} ker |χ| = ker H_G. … Indeed, the
factor group G/°G is a free abelian group." The PDF's text layer is OCR; the
symbols `H_G(x)` and `ℤ` are read from the garbled `Η„(χ)` and `2ζ`, and the
last sentence confirms the integer values. Printed p. 7 (PDF page 13) fixes the
normalization of the absolute value; its formulas are missing from the text layer
and are not quoted. This module uses the published residue-normalized
`T.normalizedAbs` and `q = T.residueCardinality`.

For the block Levi `M = GL_(n_1) × ⋯ × GL_(n_r)` the rational characters are
generated by `m ↦ det m_j`. `T.leviHMap` records `H_M(m)` through its values on
these generators. For the split torus `(F^×)^r` they are the coordinates `a_j`,
and `T.centreHMap` records `H(a)` the same way. Both are therefore integer
vectors, as in Silberger's `Hom(X(G), ℤ)`. The identification of `Hom(X(M), ℤ)`
with `ℤ^r` by these generators is the explicit choice made here.

W. Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft of 1 May 1995 (registered source
`casselman-1995-admissible-representations`, SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`; PDF page =
printed page; the text layer renders the set-difference sign as an unknown glyph):

- Section 1.4, p. 13: "For each ε in (0, 1] and each Θ ⊆ ∆ define A^−_Θ(ε) to be
  {a ∈ A_Θ | |α(a)| ≤ ε for all α ∈ ∆ − Θ}. I write simply A^−_Θ for A^−_Θ(1)."
- Theorem 4.4.6, p. 45: "Let ω be a character of Z_G. If (π, V) is an admissible
  ω-representation of G, then it is square-integrable if and only if (a) ω is
  unitary; (b) for every Θ ⊆ ∆, if χ is a central character of π with respect to
  P_Θ then |χδ_∅^(−1/2)(a)| < 1 for all a ∈ A^−_Θ − A_∅(O)A_∆."

For the standard upper block parabolic of shape `(n_1, …, n_r)`, `A_Θ` is the
group of block scalars. The roots in `∆ − Θ` are `a ↦ a_j / a_(j+1)`, so
`a ∈ A^−_Θ` means `|a_1| ≤ ⋯ ≤ |a_r|`. A block scalar lies in `A_∅(O) A_∆` exactly
when all `|a_j|` are equal. The published `Exponents/Jacquet` already uses the
normalized Jacquet module, which builds Casselman's twist by `δ^(−1/2)` into the
exponent (see `Exponents/Jacquet.md`). Under these identifications, condition
(b) for one central character `χ` is the right-hand side of
`IsRealPartOf.isPositiveRootCone_iff`, and (a) on the diagonal scalars is
`IsRealPartOf.sum_eq_zero_iff`. These identifications are explained here; the
Lean code states only the block-scalar inequalities.

| Source | Lean |
| --- | --- |
| `⟨χ, H_G(x)⟩ = log_q |χ(x)|`, Silberger 0.4 | `T.logAbs`, `T.centreHMap`, `T.leviHMap` |
| `H_G` is a homomorphism | `centreHMap_mul`, `leviHMap_mul` |
| `A^−_Θ`, Casselman 1.4 | `Monotone fun j => T.normalizedAbs (a j)` |
| `a ∉ A_∅(O)A_∆` | `∃ i j, T.normalizedAbs (a i) ≠ T.normalizedAbs (a j)` |
| `|χδ^(−1/2)(a)| < 1`, Casselman 4.4.6(b), for one `χ` | `IsRealPartOf.isPositiveRootCone_iff` |
| `ω` unitary, Casselman 4.4.6(a), on the diagonal scalars | `IsRealPartOf.sum_eq_zero_iff` |

## Provenance and scope

The cone predicates and their pairing and simple-root characterizations are
elementary linear algebra, proved here, in the coordinates fixed by the
published `IsRealPartOf`. The H-maps follow Silberger's definition, with the
explicit basis of rational characters described above. Worker 19 asked for this
interface for the remaining exponent statements (H-maps with their character
compatibility, and partial-sum cones in split-centre coordinates, kept separate
from the determinant-twist chamber). Worker 19's published
`RootWeightConeDecompositionStatement` is the Euclidean cone lemma of
Silberger 1978 and is not restated here. The field `F` is any p-adic field, and
`r` and the block shape are arbitrary; for `r ≤ 1` both cones reduce to
`∑ x_i = 0`.
