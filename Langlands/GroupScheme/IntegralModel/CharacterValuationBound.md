# Rational characters have valuation one on the integral image

Let `R` be a domain, `K` its specified fraction field, and
`M : IntegralModel R K G` a supplied model of the group scheme `G` over
`Spec K`, with `IsAffine G.X.left`. All rings and schemes use one arbitrary
universe `u`. Let `v : Valuation K Γ₀` be a valuation into a linearly ordered
commutative group with zero, with `v (algebraMap R K r) ≤ 1` for every `r : R`.
This module proves that the integral image `M.integralPoints` lies in the
common kernel of the valuations of the rational characters,
`characterValuationKernel v G`. This is one of the two inclusions in a
comparison of a model image with `G(K)^1 ∩ G(K)_y`.

`exists_valuation_bound` proves that each global function
`a : Γ(G.X.left, ⊤)` has bounded valuation on the integral image. There is a
`B : Γ₀` with
`v (G.affinePointEvaluation (CommAlgCat.of K K) (rationalCoeffEquiv K G g) a) ≤ B`
for every `g ∈ M.integralPoints`. The proof first works with the `K`-algebra
map on the coordinate ring defined by a rational point, which is a private
helper. It inducts over `Algebra.adjoin` using
`adjoin_range_genericCoordinate_eq_top`. At a generic coordinate
`M.genericCoordinate b`, `mem_integralPoints_iff_genericCoordinates` writes the
value at an integral point as the image of an element of `R`, so the bound is
`1`. A scalar `c` has the constant bound `v c`. Sums are bounded by the maximum
of the bounds by the ultrametric inequality, and products by the product of
the bounds.

The definition `rationalCharacterCoordinate χ : Γ(G.X.left, ⊤)` is the global
function of an actual rational character `χ`. It is the pullback, along the
character's underlying morphism to the multiplicative group, of the universal
unit coordinate `Gm.universalUnit`. It needs no affineness.
`rationalCharacterEval_val_eq_evaluation` also holds without affineness. It
identifies the value of `χ` at `g` with the evaluation of this function at `g`.
The proof rewrites `rationalCharacterEval` through the existing affine unit
equivalence of `𝔾_m` and `rationalCoeffEquiv_eq`.

`integralPoints_le_characterValuationKernel` additionally assumes
`MulArchimedean Γ₀`. Fix an integral `g` and a character `χ`, and let `B` bound
the valuation of `rationalCharacterCoordinate χ` on the integral image. Since the
image is a subgroup, every power `g ^ n` and every power `g⁻¹ ^ n` is
integral. So the value `a = v (χ g)`, which is nonzero because `χ g` is a
unit, has every power `a ^ n` and every power `a⁻¹ ^ n` at most `B`. A private
helper shows that such an `a` equals `1` in a multiplicatively archimedean
group with zero. If `1 < b` and all powers of `b` are at most `B`, then
`B ≤ b ^ n` for some `n`, so `b ^ (n + 1) ≤ b ^ n`, which forces `b ≤ 1`.
This is applied to `a` and to `a⁻¹`.

The final section specializes to a nonarchimedean local field `F` and a group
`G` with `IsAffineHom G.X.hom`.
`baseChangeUnramified_integralPoints_le_characterValuationKernel` proves that
the integral image of `M.baseChangeUnramified` lies in
`characterValuationKernel (MaximalUnramified.valuation F)
(baseChanged F (inertiaFixedField F) G)`. Here `M.baseChangeUnramified` is the
existing base change of a model over `𝒪[F]` to the integers of the separable
inertia fixed field. The fixed-field integers are the valuation subring of
`fixedFieldValuation F`, and `MaximalUnramified.valuation_isEquiv` shows that
the normalized valuation is equivalent to it, so the normalized valuation is at
most one on these integers. The value group `WithZero (Multiplicative ℤ)` is
multiplicatively archimedean. Two private instances record that the
base-changed structure morphism is affine, by base change of affine morphisms,
and that the base-changed group is therefore affine over the affine base.

These are internal consequences of the `IntegralModel` definitions, the
generic-coordinate generation and integral-point coordinate criterion, the
definition of `characterValuationKernel`, and the existing normalized
maximal-unramified valuation. They prove only the inclusion of the integral
image in the character valuation kernel. They prove neither the reverse
inclusion nor any comparison with building stabilizers, and they do not use
any existence of buildings or good models.
