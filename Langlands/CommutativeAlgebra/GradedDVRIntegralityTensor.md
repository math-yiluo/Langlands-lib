# Integrality of contracting points, tested after extending the scalars

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6. Its statements are
derived here and are not quoted from the source. It restates
`GradedDVRIntegrality.integral_of_contracting` (module
`Langlands.CommutativeAlgebra.GradedDVRIntegrality`) so that the test set lives
in `Ω ⊗[k] B` for a `k`-vector space `Ω`. In the intended application `Ω` is an
algebraic closure of `k`.

The notation (`IsGrading`, `IsContracting`, counit `ε`, coaction `c`) is that of
`GradedDVRIntegrality`.

## `equivFinsuppOfBasisLeft_lTensor`

For a basis `ℬ` of `Ω` over `k` and a `k`-linear map `f : N → P`, the
`i`-th coordinate of `(Ω ⊗ f) x` equals `f` applied to the `i`-th coordinate of
`x`. The coordinates are those of Mathlib's
`TensorProduct.equivFinsuppOfBasisLeft ℬ : Ω ⊗[k] N ≃ (ι →₀ N)`. The proof is by
induction on `x`. On a pure tensor `ω ⊗ n` both sides are
`ℬ.repr ω i • f n`; sums are additive.

## `weightPart`

For a grading `hc : IsGrading k c` and `n : ℤ`, `weightPart hc n : B →ₗ[k] B`
is `b ↦ (c b).coeff n`. Additivity comes from additivity of `c`. For
`k`-linearity, `c (r • b) = C (algebraMap k B r) * c b`, because `c` maps
scalars to constants, and multiplying by a constant scales every coefficient.
`weightPart_apply` unfolds the definition.

## `integral_of_contracting_tensor`

Hypotheses. These are those of `integral_of_contracting`, except for the test
set:

- `B` is a finitely generated `k`-algebra, `IsGrading k c`, and `ε : B →ₐ[k] k`
  satisfies `ε ((c b).coeff n) = if n = 0 then ε b else 0`.
- `Ω` is a `k`-vector space and `M ⊆ Ω ⊗[k] B` is stable under every
  `(weightPart hc n).lTensor Ω`.
- (`hker`) If `a : B →ₐ[k] k` is contracting and `(Ω ⊗ a) m = (Ω ⊗ ε) m` in
  `Ω ⊗[k] k` for all `m ∈ M`, then `a = ε`.
- `A : Type u` is a DVR and a `k`-algebra whose residue field is geometrically
  reduced over `k`.
- `hrat` is the rational-point hypothesis of `integral_of_contracting`.
- `ξ : B →ₐ[k] FractionRing A` is contracting.
- For every `m ∈ M`, `(Ω ⊗ ξ) m` lies in the range of
  `Ω ⊗ (A → FractionRing A)`.

Conclusion: `ξ b` lies in the image of `A` for every `b ∈ B`.

Proof as implemented. Choose a `k`-basis `ℬ` of `Ω`
(`Module.Free.chooseBasis`). Let `Mk ⊆ B` be the set of all coordinates
`equivFinsuppOfBasisLeft ℬ m i` for `m ∈ M` and `i` an index of the basis. Then
apply `integral_of_contracting` with test set `Mk`. Its three hypotheses on
`Mk` follow from `equivFinsuppOfBasisLeft_lTensor`:

- Stability: the weight-`n` part of the `i`-th coordinate of `m` is the `i`-th
  coordinate of `(Ω ⊗ weightPart n) m`, which lies in `M`.
- Kernel condition: if `a = ε` on `Mk`, then for `m ∈ M` the elements
  `(Ω ⊗ a) m` and `(Ω ⊗ ε) m` have the same coordinates `a (m_i) = ε (m_i)`.
  They are therefore equal, because `equivFinsuppOfBasisLeft ℬ` is injective.
  So `hker` gives `a = ε`.
- Integrality: if `(Ω ⊗ ξ) m = (Ω ⊗ ι) z` with `z ∈ Ω ⊗[k] A` and
  `ι : A → FractionRing A`, then taking `i`-th coordinates gives
  `ξ (m_i) = ι (z_i)`.

## Intended role in C.1.6

In the C.1.6 argument (with `k` separably closed and `Ω` an algebraic closure),
`M` is the image in `Ω ⊗[k] O(G)` of the coordinate ring of the reductive
quotient `G''` of `G_Ω`. It is stable under weight parts because
`G_Ω → G''` is compatible with the cocharacters. The integrality hypothesis
expresses that the image in `G''` of the `K`-point `u` extends over the DVR
`Ω ⊗[k] A`. `hker` expresses that a `k`-point of `U_G(λ)` that becomes trivial
in `G''` is trivial.
