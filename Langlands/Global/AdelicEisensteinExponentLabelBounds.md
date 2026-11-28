# Norm bounds for affine Eisenstein exponent labels

`StandardParabolicFamily.EisensteinExponentLabelBoundStatement` is a criterion on
the positive split component of a standard parabolic `Q = P_J`. Write `a` for the
image in `Q(𝔸)` of a dominant positive point `s` of `A_J`, and `ρ_Q` for
`halfModulusParameter`. The criterion bounds the raw affine exponent by
`‖a^(L(i x) + μ + ρ_Q)‖ ≤ ‖a^ρ_Q‖` for every real parameter `x`. It assumes that
`L(i x)|_{A_J}` has zero real part for each `x` and that
`Re(μ|_{A_J}) = ∑ᵣ cᵣ βᵣ|_{A_J}`, with finitely many positive ambient relative
roots `βᵣ` and real coefficients `cᵣ ≤ 0`. The empty sum covers zero normalized
offset, including the offset of the leading constant-term labels.

`characterLog_restrict_nonneg_of_isDominantSplitPoint` gives a nonnegative logarithm
for every positive relative root restricted to `A_J`. For simple roots outside `J`,
this follows by taking the logarithm of the defining dominant inequality. Simple
roots in `J` vanish on `A_J`. Induction on positive relative roots gives the result
by additivity of the logarithmic functional.

`norm_parameterPower_add_halfModulus_eq` factors the norm of `a^(μ + ρ_Q)` using
the additivity of exponent parameters, naturality of character evaluation, and
`Complex.norm_exp`. The two factors are `‖a^ρ_Q‖` and the exponential of the real
normalized pairing on `A_J`.

`parameterRealPart_restrict_slope_imaginary` uses commutation of character pullback
with real part. If the restriction of `L` to `A_J` agrees with pullback along a
morphism `A_J → P`, then `L(i x)` has zero real part after restriction to `A_J`.

`norm_parameterPower_affine_imaginary_le_halfModulus` proves the criterion.
The slope vanishes in the real pairing, and each summand in the pairing of the
offset with `H_{A_J}(s)` is nonpositive by the dominance lemma. The real exponential
therefore contributes a factor at most one.

This is the norm comparison in Lapid (2011), Lemma 6, printed p. 322, and
Delorme (2023), §2 p. 6 and §4.1 pp. 16–17. In Lapid's argument the coefficients
come from Mœglin–Waldspurger (1995), I.4.11, printed pp. 74–75, and the positive
roots are the Weyl images of the relevant Levi roots. The coefficient expression
and its identification with the normalized offset enter as hypotheses.
