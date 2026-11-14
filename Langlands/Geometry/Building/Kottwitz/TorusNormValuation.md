# Integer normalization on finite extensions of the maximal unramified field

This module is a derived helper for the proof of Kaletha–Prasad, *Bruhat–Tits
theory: a new approach* (2023), Proposition 11.1.1 (printed pp. 421–422, PDF
pp. 452–453), source `kaletha-prasad-2023-bruhat-tits-new-approach`. That
proposition uses, for each finite Galois splitting field `L` of a torus over `K`,
"the valuation on `L` normalized so that `L^×` maps onto `ℤ`" (printed p. 421).
Its proof compares two splitting fields `L₁ ⊂ L₂` by noting that `L₂/L₁` is
totally ramified (printed p. 421). The last theorem of this module,
`normalizedIntermediateValuation_norm`, is the precise form of that remark used
in the Lean proof.

In the Library this valuation is `normalizedIntermediateValuation F L`, selected
by classical choice from the characterization
`IsNormalizedIntermediateValuation`. This module proves the facts about it that
the norm characterization needs. It also proves the published statement
`NormalizedIntermediateValuationStatement`.

Notation: `F` is a nonarchimedean local field, `K = UnramifiedClosure F` is the
inertia fixed field inside `E = SeparableClosure F`, and `w = sepClosureValuation F`
is the spectral valuation of `E`. For an intermediate field `L` of `E/K`,
`intermediateValuation F L` is `w` restricted to `L`. No local-field instance on
`K` or on `L` is used.

## Generic part (`IntegerNormalization`)

These statements hold for any field `R`.

- `exists_intValuation_of_zpow`: take a real valuation `w` and a real `e > 1` such
  that every nonzero value of `w` is an integer power `e ^ m`. Then
  `w = toNNReal e ∘ v` for some valuation `v` with values in `ℤᵐ⁰`, where
  `WithZeroMulInt.toNNReal e` is Mathlib's map `ofAdd m ↦ e ^ m`, `0 ↦ 0`. The
  proof chooses the unique preimage of each value. That map is strictly monotone
  (`toNNReal_strictMono`), hence injective, so the valuation axioms of `v` follow
  from those of `w`.
- `valuationOfLeIff`: a multiplicative map `f` that compares elements exactly as a
  valuation `w` does (`f x ≤ f y ↔ w x ≤ w y`) is itself a valuation, equivalent
  to `w` (`valuationOfLeIff_isEquiv`). The ultrametric inequality of `f` follows
  from that of `w` by comparing `w (x + y)` with the larger of `w x` and `w y`.
- `eq_of_isEquiv_of_surjective`: two equivalent, surjective `ℤᵐ⁰`-valued
  valuations are equal. Let `π` have first value `g = ofAdd (-1)`. Its second
  value is also `g`: otherwise it, or the first value of an element with second
  value `g`, would lie strictly between `g` and `1`, which no element of `ℤᵐ⁰`
  does (`not_ofAdd_neg_one_lt_lt_one`). Every nonzero value is a power `g ^ m`
  (`exists_eq_zpow_ofAdd_neg_one`). So for `x ≠ 0` the first values of `x` and
  `π ^ m` agree, and by equivalence so do the second values.

## The extensions of `K`

- `unramifiedClosure_hasDimensionLEOne`: the published theorem
  `henselianDiscreteDimensionLEOne` applied to the integer-normalized valuation
  `MaximalUnramified.valuation F` of `K`. Its hypotheses are surjectivity, a
  Henselian valuation ring and an algebraically closed residue field, and the
  Library proves each of them for this valuation. The conclusion is the
  dimension-one norm criterion `HasDimensionLEOne K`: norms of finite Galois
  extensions of finite separable extensions of `K` are surjective on units.
- `sepClosureValuation_algEquiv`: `w` is invariant under every automorphism of `E`
  over an intermediate field `L` of `E/K`. This is the field `inv_of` of the
  published `ambientHyp_sepClosureValuation`, which comes from the
  automorphism-invariance of the spectral norm.
- `intermediateValuation_norm`: for `L/K` finite and `x ∈ L`, the `w`-value of
  `N_{L/K}(x)` is `w(x) ^ [L : K]`. This is the published `val_norm_eq`, applied
  with the invariant valuation `w` on the normal extension `E/K`.
- `exists_intermediateValUniformizer`: `w` restricted to a finite extension `L` of
  `K` has a uniformizer, in the sense of the published `ValUniformizer`.
  `ambientHyp_sepClosureValuation` gives a uniformizer `π_K` of `K`, with value
  `q ∈ (0, 1)`. If `x ∈ L` is nonzero with `w(x) ≤ 1`, then `N_{L/K}(x)` is a
  nonzero element of `K` of value at most `1`. Its value is therefore `q ^ k`, so
  `w(x) ^ [L : K] = q ^ k`. The published lemma `exists_valUniformizer` turns this
  discreteness, together with the element `π_K` of value in `(0, 1)`, into a
  uniformizer of `L`.
- `exists_isNormalizedIntermediateValuation`: let `π` be such a uniformizer with
  `γ = w(π)`. Every nonzero value of `w` on `L` is an integer power of `γ⁻¹ > 1`:
  for `w(x) ≤ 1` use the uniformizer property for `x`, and otherwise use it for
  `x⁻¹`. The generic construction yields `v` with `toNNReal γ⁻¹ ∘ v = w`. Strict
  monotonicity of `toNNReal` makes `v` equivalent to `w`. `v` is surjective because
  `v (π ^ (-m)) = ofAdd m`, which is checked after applying the injective map
  `toNNReal`.
- `normalizedIntermediateValuationStatement`: existence as above, together with
  uniqueness from `eq_of_isEquiv_of_surjective`. This proves the published
  statement `NormalizedIntermediateValuationStatement`, the target of the
  separate task on integer normalization.
- `normalizedIntermediateValuation_spec'` and `eq_normalizedIntermediateValuation`:
  the selected valuation `ν_L = normalizedIntermediateValuation F L` has the
  defining property, and any normalized valuation equals it.
- `normalizedIntermediateValuation_algEquiv`: `ν_L(σ x) = ν_L(x)` for
  `σ ∈ Gal(L/K)`. The automorphism `σ` extends to `E` (`AlgEquiv.liftNormal`, as
  `E/K` is normal), so `w(σ x) = w(x)` by invariance. Equal `w`-values give equal
  `ν_L`-values, because `ν_L` is equivalent to `w`.
- `exists_norm_eq_of_le`: for finite extensions `L ≤ M` of `K` inside `E`, every
  nonzero `y ∈ L` is a norm `N_{M/L}(x)` with `x ∈ M`. The field
  `M' = normalClosure K M E` is finite and Galois over `K`, hence Galois over `L`.
  `L` is finite and separable over `K`, so the dimension-one criterion makes
  `N_{M'/L}` surjective on units. The element `x = N_{M'/M}(z)`, where `z` is a
  preimage of `y`, then works by transitivity of norms (`Algebra.norm_norm`).
- `normalizedIntermediateValuation_norm`: for finite extensions `L ≤ M` of `K`
  and `x ∈ M`, `ν_L(N_{M/L}(x)) = ν_M(x)`, with the algebra `L → M` given by the
  inclusion. No Galois hypothesis is needed. Put `d = [M : L]`. By `val_norm_eq`
  over `L`, `w(N_{M/L}(x)) = w(x) ^ d`, and `t ↦ t ^ d` is strictly monotone on
  `ℝ≥0`. So the map `x ↦ ν_L(N_{M/L}(x))` compares elements of `M` exactly as `w`
  does, and `valuationOfLeIff` makes it a valuation equivalent to
  `intermediateValuation F M`. It is surjective: `ν_L` is surjective and every
  nonzero element of `L` is a norm from `M`. Uniqueness identifies it with `ν_M`.
  In valuation-theoretic terms, this says that `M/L` is totally ramified, as KP
  remark. The proof obtains this from the dimension-one norm criterion rather
  than from the fundamental identity `e f = n`.
