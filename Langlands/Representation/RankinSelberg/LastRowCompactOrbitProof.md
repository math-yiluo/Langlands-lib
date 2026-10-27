# Proof of the exact compact open orbit of the last row

Author: Worker 714.

`Langlands.RankinSelberg.lastRowCompactOrbit` proves
`LastRowCompactOrbitStatement.{uF} F T n` for every implicit prime `p`, every
`F : PadicField.{uF} p`, every supplied `T : F.TopologicalData` and every
`n : ℕ`. Its complete type is exactly that proposition, so rank one (`n = 0`),
every supplied `T` and every compact open subgroup `J` are retained. The
proof installs the topology, valuative relation and local-field structure of
`T`. It obtains the Hausdorff property from the published certificate
`T.fieldT2`. Instance search supplies `IsTopologicalDivisionRing` from the
installed local-field structure; Mathlib declares this instance for every
`IsNonarchimedeanLocalField`. The proof then applies
`lastRowCompactOrbit_of_field`.

## The general field version

`lastRowCompactOrbit_of_field` proves the same conjunction for any field `K`
with a topology for which `K` is a Hausdorff topological division ring. It uses
the actual `Langlands.GeneralLinear (n + 1) K`, the actual subgroup
`GeneralLinear.mirabolic n K`, the actual `RankinSelberg.lastRow`, and an
arbitrary `J : OpenSubgroup` with compact underlying set. Write
`R = lastRow '' J`.

### Algebraic lemmas

These lemmas hold over any field and use no topology.

- `lastRow_mul_eq_vecMul`: `lastRow (g * h)` is the row vector
  `lastRow g ᵥ* h`. This holds by definition of matrix multiplication and is
  imported from [`QuotientIntegrals`](QuotientIntegrals.md).
- `mem_mirabolic_iff_lastRow`: `a` lies in the mirabolic subgroup if and only
  if `lastRow a = lastRow 1`. Both sides say that the last row of `a` is
  `(0, …, 0, 1)`.
- `lastRow_ne_zero`: the last row of an invertible matrix is nonzero. If
  `lastRow g = 0`, then `lastRow (g * g⁻¹) = 0 ᵥ* g⁻¹ = 0`. Its last entry is
  the last entry of `lastRow 1`, which is `1`, a contradiction.
- `lastRow_mem_image_iff`: for any subgroup `J` (no topology is needed),
  `lastRow g ∈ lastRow '' J` holds if and only if `g = a * j` for some
  mirabolic `a` and some `j ∈ J`.
  For the forward direction, suppose `lastRow j = lastRow g`. Then
  `a = g * j⁻¹` satisfies
  `lastRow a = lastRow g ᵥ* j⁻¹ = lastRow j ᵥ* j⁻¹ = lastRow 1`, so `a` is
  mirabolic and `g = a * j`. Conversely,
  `lastRow (a * j) = lastRow a ᵥ* j = lastRow 1 ᵥ* j = lastRow j`.

### Topological lemmas

- `continuous_lastRow`: each coordinate of `lastRow` is the published
  continuous matrix entry `GeneralLinear.entry (Fin.last n) j`.
- `isEmbedding_generalLinear_val`: over a topological division ring `K`, the
  map `Units.val` from `GeneralLinear m K` to matrices is a topological
  embedding. The proof applies Mathlib's `Units.isEmbedding_val_mk'` to matrix
  inversion. Mathlib's `continuousAt_matrix_inv` reduces continuity of matrix
  inversion at an invertible matrix to continuity of `Ring.inverse` at its
  determinant. This determinant is nonzero, and on a field `Ring.inverse` is
  `Inv.inv`, which is continuous at nonzero points.
- `isOpenEmbedding_generalLinear_val`: if moreover `K` is T1, the range of
  `Units.val` is the preimage of `{0}ᶜ` under the continuous determinant. It
  is therefore open, and `Units.val` is an open embedding.
- `lastRow_image_mem_nhds`: if `U` is an open subset of the general linear
  group containing `1`, then `lastRow '' U` is a neighborhood of `lastRow 1`.
  Consider the continuous map
  `s ↦ (1 : Matrix).updateRow (Fin.last n) s`, which replaces the last row of
  the identity matrix by `s`. It sends `lastRow 1` to the identity matrix. That
  matrix lies in the open set `Units.val '' U`. Hence, for all `s` near
  `lastRow 1`, the modified matrix is `u.val` for some `u ∈ U`. Then
  `lastRow u = s`. This is the local matrix section of the last-row map; no
  quotient model is used.
- `isOpen_lastRow_image`: for an open subgroup `J`, `lastRow '' J` is open.
  Let `r = lastRow j₀` with `j₀ ∈ J`. The continuous map
  `t ↦ t ᵥ* j₀⁻¹` sends `r` to `lastRow 1`. By the previous lemma, its
  preimage of `lastRow '' J` is a neighborhood of `r`. If
  `t ᵥ* j₀⁻¹ = lastRow j₁` with `j₁ ∈ J`, then
  `lastRow (j₁ * j₀) = (t ᵥ* j₀⁻¹) ᵥ* j₀ = t`, and `j₁ * j₀ ∈ J`.

### The Schwartz–Bruhat indicator

`compactOpenIndicator U hc ho` is the Schwartz–Bruhat function whose underlying
function is `U.indicator (fun _ => 1)`. It is defined for a compact open set `U`
in a Hausdorff space. The set `U` is closed because it is compact in a Hausdorff
space, hence clopen. Mathlib's `LocallyConstant.indicator` of the constant
function `1` then shows that the indicator is locally constant. Its support lies
in the compact set `U`, so it has compact support. The theorem
`coe_compactOpenIndicator` records that the underlying function is
definitionally this indicator.

### Assembly

In `lastRowCompactOrbit_of_field`:

- `R` is compact, as the continuous image of the compact set `J`.
- `R` is open by `isOpen_lastRow_image`.
- Every element of `R` is nonzero by `lastRow_ne_zero`.
- `lastRow 1 ∈ R` because `1 ∈ J`.
- The required function is `compactOpenIndicator R`, whose values are exactly
  `R.indicator (fun _ => (1 : ℂ))`. This is an equality of functions, not only
  of supports. The row space is Hausdorff as a finite product of Hausdorff
  spaces.
- The fiber description is `lastRow_mem_image_iff` applied to the subgroup
  underlying `J`.

No congruence, normality or stabilizer condition on `J` is used, and the
orbit is not replaced by a larger neighborhood. No Whittaker, Kirillov, measure,
convergence or integral assertion appears.

## Provenance

The statement's paired Markdown records the contextual source:
Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg Convolutions* (1983),
registered as `jpss-1983-rankin-selberg`, printed p.393. That page uses the
characteristic function of `η K_m` in its equal-rank existence argument. The
present proof is internal elementary matrix geometry for the arbitrary-`J`
statement. It is not a transcription of an argument from that source, and it
does not prove the source's existence theorem.

## Reusable declarations

`lastRow_mul_eq_vecMul`, `mem_mirabolic_iff_lastRow`, `lastRow_ne_zero`,
`lastRow_mem_image_iff`, `continuous_lastRow`,
`isEmbedding_generalLinear_val`, `isOpenEmbedding_generalLinear_val`,
`lastRow_image_mem_nhds`, `isOpen_lastRow_image`, `compactOpenIndicator` and
`lastRowCompactOrbit_of_field` are public declarations in the namespace
`Langlands.RankinSelberg`. The first is imported from `QuotientIntegrals`;
the others are defined here. Their hypotheses are as stated above.
