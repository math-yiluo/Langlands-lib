# Whittaker characters on the rank-one extension cells

Module `Langlands.Representation.RankinSelberg.RankOneExtensionWhittakerCells`.

This helper module records how the functions in the zeta integral of the rank-one extension
step transform under the two unipotent cells of `GL_(1+(t+1))`:

- the upper cell `u(y) = [I, y; 0, 1]`, with `y ∈ K^(t+1)`
  (`rankOneExtensionUpperCell t y`);
- the block `B(n, 0, 1) = [n, 0; 0, 1]` with `n ∈ N_(t+1)`, the upper unipotent subgroup
  of `GL_(t+1)` (`rankOneExtensionLowerBlock t n 0 1`).

Here `ι = rankInclusion (k + 1)` is the standard inclusion `g ↦ diag(g, I_(k+1))` of
`GL_(1+(t+1))` into `GL_((1+(t+1))+k+1)`. It contains no new definitions.

## Provenance

Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983),
Lemma 5.5 (printed pp. 424–426), uses these transformation rules without comment when it
unfolds the zeta integral of a section of the lower induced representation. The statements
here are elementary consequences of the definitions of the Whittaker space, the standard
character and the lower section coefficient in this Library. Their form was chosen for this
formalization.

## Contents

Entries (`section Entries`), for any field `K`:

- `rankOneExtensionUpperCell_entry`: the entry of `u(y)` at `(i, j)`, in the numeric indices
  of `Fin (1 + (t + 1))`. It is `1` on the diagonal, `y_i` at `(i, t + 1)` for `i ≤ t`, and
  `0` elsewhere.
- `superdiagonal_rankInclusion_upperCell`: the sum of the first superdiagonal of `ι u(y)` is
  the last coordinate `y_t`.
- `superdiagonal_rankInclusion_lowerBlock`: the sum of the first superdiagonal of
  `ι B(n, 0, 1)` equals that of `n`.

Whittaker functions (`section Whittaker`), for a unitary additive character `ψ` of `K` and
`W` in the Whittaker space `WhittakerFunctions ψ ((1 + (t + 1)) + k)`:

- `whittaker_rankInclusion_upperCell_mul`: `W(ι(u(y) z)) = ψ(y_t) W(ι z)`.
- `whittaker_rankInclusion_lowerBlock_mul`: `W(ι(B(n, 0, 1) z)) = θ(n) W(ι z)`, where
  `θ = standardCharacter ψ t` is the standard character of `N_(t+1)`.

Lower section coefficient (`section Coefficient`), over a `p`-adic field `F`:

- `rankOneExtensionTensorContraction_smul`: the tensor contraction is linear in the
  functional, `contr(c ℓ) = c contr(ℓ)`.
- `rankOneExtensionLowerSectionCoefficient_unipotent_mul`: for a section `f` in
  `rankOneExtensionLowerSection F t χ σ` (the smooth covariant functions carrying the lower
  induced representation), a Whittaker functional `ℓ` of `σ` for the inverse character
  (`Whittaker.glInverseFunctionals ψ t σ`), and `n ∈ N_(t+1)`,

  `c_f(B(n, 0, 1) z) = θ(n)⁻¹ c_f(z)`,

  where `c_f = rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f` and
  `θ(n)⁻¹ = inverseStandardCharacter ψ t n`.

## Proof method

`rankOneExtensionUpperCell_entry` reduces both indices through the block equivalence
`rankOneExtensionCellCoordinates t` and evaluates the four blocks of `u(y)`. The two
superdiagonal lemmas evaluate each term with `rankInclusion_entry` and the entry formulas of
the cells. For `u(y)` only the term at index `t` is nonzero (`Finset.sum_eq_single`). For
`B(n, 0, 1)` both sums are rewritten as the same sum over `Finset.range`
(`Fin.sum_univ_eq_sum_range`), and the extra terms vanish (`Finset.sum_subset`).

The Whittaker lemmas use the left `N`-equivariance of `W` (the property of
`WhittakerFunctions`) at `ι u(y)` and `ι B(n, 0, 1)`. These matrices lie in the upper
unipotent subgroup by `rankInclusion_mem_upperUnipotent`. The value of the standard character
is the first-superdiagonal sum computed above.

The coefficient lemma rewrites with `rankOneExtensionLowerSectionCoefficient_lowerBlock_mul`
from [RankOneExtensionLowerCovariance](RankOneExtensionLowerCovariance.md). For unipotent
`n`, the determinant norm and `χ(1)` are `1`, so the scalar factor is `1`. The functional
satisfies `ℓ ∘ σ(n) = θ(n)⁻¹ ℓ` by the defining property of
`Whittaker.glInverseFunctionals`, and `rankOneExtensionTensorContraction_smul` moves the
scalar out of the contraction.
