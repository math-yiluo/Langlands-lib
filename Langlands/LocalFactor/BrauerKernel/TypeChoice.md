# Admissible unramified exponents for actual Brauer relations

Author: Worker 1838. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. It supplies
the exponent choices required by `typeComponent_eq_zero`
(`BrauerKernel.TypeSplit`). Combining the two gives the unconditional type
separation `exists_typeComponent_eq_zero` of every actual Brauer relation under
the normalized reciprocity premise. No epsilon or L-factor identity is asserted.

## Field side (`Langlands.LocalFactor.PadicAbelian`)

`exists_finite_range_mul_absPower`: let `T` be a supplied topological datum of a
finite p-adic field and `χ` a continuous quasicharacter. Then for some `t ∈ ℂ` the
function `x ↦ χ(x) · exp(-t · log |x|)` has finite range on the units. The proof
takes the Library's `uniformizerUnit T` = `π` and sets
`t = -log χ(π) / log q`, with `q` the residue cardinality. Every unit is
`x = u π^k` with `k = ord x` and `u` of order zero. Since `|x| = q^{-k}`, the value at
`x` is `χ(u) χ(π)^k χ(π)^{-k} = χ(u)`. The range therefore lies in the image of the
integral units, which is finite by the published
`quasicharacter_finite_unit_image`.

## Weil side (`Langlands.LocalFactor.NonabelianBrauer`)

- `exists_twistedWeilCharacter_finite_range`: for normalized reciprocity, every
  field character has an exponent `t` for which `twistedWeilCharacter F e L χ t`
  has finite range. The published
  `CommonClosureSpectralAnalytic.character_eq_norm_exp` identifies the base-degree
  twist `character F L (-t)` at `w` with `exp(-t · log |rec_L(w)|)`. So the twisted
  character is the function of the field-side lemma, composed with the reciprocity
  map.
- `twistedWeilCharacter_add`: changing the exponent by `a` multiplies the twisted
  character by `character F L (-a)`.
- `rationalExponents F` is the additive subgroup `(2πi / log q_F) ℚ` of `ℂ`.
  `character_neg_finite_range`: for `a` in it, `character F L (-a)` takes values in the
  powers of the root of unity `exp(2πi r)`, so its range is finite.
  `twistedWeilCharacter_finite_range_add` combines this with the previous lemma.
- `typeRepresentative F t` is the chosen representative (`Quotient.out`) of the class
  of `t` in `ℂ ⧸ rationalExponents F`. `typeRepresentative_sub_mem` shows the
  representative differs from `t` by a rational exponent.
  `typeRepresentative_separated` shows that distinct representatives `τ ≠ τ'`
  satisfy `exp(-(τ - τ') log q_F · m) ≠ 1` for all nonzero integers `m`. If it held,
  `Complex.exp_eq_one_iff` would put `τ - τ'` in the lattice, and the two classes
  would coincide.
- `kernelInWeil F g ψ` is the subgroup of `W_E`, inside `W_L ∩ W_E`, on which
  `ψ ∘ nestedWeilEquiv` is trivial. It has finite index when `ψ` has finite range
  (`kernelInWeil_finiteIndex`, via Mathlib's `finiteIndex_ker` and
  `Subgroup.index_map_subtype`).
- `exists_admissible_exponents`: for every presentation there are exponents
  `t₁`, `t₂` with both twisted characters of every support generator of finite
  range, and with all used exponents pairwise separated. Take the representatives
  of the exponents chosen by `exists_twistedWeilCharacter_finite_range`.
- `exists_typeComponent_eq_zero`: for an actual relation (`presentationMap F e E z = 0`)
  there are such exponents, and every `typeComponent F e z t₁ t₂ τ` vanishes on all
  of `W_E`. The subgroup `N` required by `typeComponent_eq_zero` is the normal core
  of the finite intersection of the subgroups `kernelInWeil`.

The field universe `uF` and the representation universe `uV` remain independent.

## Provenance

Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973),
registered as `deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`, §4.10
(printed page 542, PDF page 42). There every representation is trivial on a
finite-index subgroup of inertia, a power of Frobenius is central modulo it, and
irreducible representations have a type. Unramified quasi-characters of every type
exist, and twisting by them identifies each type component with the Galois part.
For characters, this module derives the corresponding concrete facts internally:
finite-order twists and separated type representatives. All other inputs are
published Library theorems named above.
