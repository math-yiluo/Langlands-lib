# Vectors with a scaled essential identity are multiples of the essential vector

This internal auxiliary isolates the last step of the proof of Theorem (5.1)
in Jacquet, Piatetski-Shapiro and Shalika, *Conducteur des représentations du
groupe linéaire*, Math. Ann. 256 (1981), printed page 214: "D'après l'unicité
dans le théorème (4.1) la fonction W₁ est alors un multiple de W". Suppose a
Whittaker function `v` in the model has restriction to `diag(GL_(n+1), 1)` that
is right `GL_(n+1)(O)`-invariant. Suppose also that its corank-one integrals
continue to `C ∏ i, P(x_i X)⁻¹`. If `w` is the only essential vector, then
`v = C • w`. Uniqueness of the essential vector and the scaled identity remain
hypotheses. Nothing here proves either of them.

The module imports only the published `Langlands.Representation.Conductor.Essential`.

## Rational continuations of scaled combinations

The published `HasRationalContinuation q f R` says that on some right
half-plane `a < Re s`, the denominator of `R` does not vanish at `q^(-s)` and
`f s` equals the value of `R` there.

- `ratFunc_eval_smul` proves that evaluating `C • R` at a point where the
  denominator of `R` does not vanish gives `C` times the value of `R`.
- `HasRationalContinuation.congr_eventually` proves that if `f` continues to
  `R` and `g s = f s` whenever `b < Re s`, then `g` continues to `R`.
- `HasRationalContinuation.const_mul` proves that if `f` continues to `R`,
  then `fun s => C * f s` continues to `C • R`. The denominator of `C • R`
  divides the denominator of `R`, so it does not vanish where the latter does
  not.
- `HasRationalContinuation.add_sub_const_mul` proves that if `f` continues to
  `R` and `g` to `C • R`, then `fun s => f s + (g s - C * f s)` continues to
  `R`. Both continuations hold on the larger of the two half-planes.

## Linearity of the corank-one integral

These results need only a topological field `F`, a unitary additive character
`ψ`, a real absolute value `abv` and, for the integral, a measure `μ` on the
published quotient `LeftUnipotentQuotient n F`.

- `corankOneIntegrand_add`, `corankOneIntegrand_sub` and
  `corankOneIntegrand_smul` prove that the published corank-one integrand is
  additive, subtractive and complex-homogeneous in its
  `WhittakerFunctions ψ (n + 1)` argument. The integrand is checked at each
  coset representative.
- `CorankOneConverges.add`, `CorankOneConverges.sub` and
  `CorankOneConverges.smul` prove that the published convergence predicate
  (integrability of the integrand for `μ`) is preserved by these operations.
- `corankOneIntegral_add` and `corankOneIntegral_sub` prove additivity and
  subtractivity of the published integral when both integrands converge.
  `corankOneIntegral_smul` proves `I(C • W) = C * I(W)` without a convergence
  hypothesis.

## The scaled essential identity

Assume also `ValuativeRel F`. Let `hψ` say that `ψ` is trivial on the integer
ring and let `ϖ` be a uniformizing element.

`SatisfiesScaledEssentialIdentity q ψ abv μ hψ hϖ P C W` is the Prop-valued
predicate obtained from the published `SatisfiesEssentialIdentity` by
replacing `essentialFactor P x` with `C • essentialFactor P x`. For every
parameter `x : Fin (n + 1) → ℂˣ`, two conditions hold:
- the corank-one integral of `W` against the published
  `inverseSphericalWhittaker hψ hϖ q x` converges on some right half-plane;
- this integral has the rational continuation `C • essentialFactor P x`.

- `satisfiesScaledEssentialIdentity_one_iff` proves that the case `C = 1` is
  the published `SatisfiesEssentialIdentity`.
- `SatisfiesEssentialIdentity.smul` proves that if `W` satisfies the published
  identity, then `C • W` satisfies the identity scaled by `C`.
- `SatisfiesEssentialIdentity.add_sub_smul` proves that if `W` satisfies the
  published identity and `W₁` the identity scaled by `C`, then
  `W + (W₁ - C • W)` satisfies the published identity. Convergence and the
  continuation are combined by the linearity results above.

`IsIntegralInvariantOnRestriction.add_sub_smul` proves that the published
restriction invariance of `w` and `v` gives that of `w + (v - C • w)`. Here
`w` and `v` lie in the coefficient model of a standard Whittaker functional
`ℓ` of a representation `π` of `GeneralLinear ((n + 1) + 1) F`.

## Multiples of the essential vector

Assume now that `F` is a nonarchimedean local field, that the measurable
structures of the published `IsEssentialVector` are present, and that
`h : IsJacquetNormalization q ψ abv ϖ μ`. Let `P` satisfy the published
`IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P`. In the scaled
identity below, `hψ` is `h.conductor.1` and the uniformizer is
`h.uniformizer`.

- `IsEssentialVector.add_sub_smul` proves the following. Let `w` be essential
  and `v` restriction invariant with the identity scaled by `C`. Then
  `w + (v - C • w)` is essential. Its identity uses `P` and the published
  `IsEssentialVector.satisfiesEssentialIdentity` for `w`.
- `eq_smul_of_satisfiesScaledEssentialIdentity` is the source step. Let `w`
  be essential and let every essential vector of the model equal `w`. Let `v`
  be restriction invariant with the identity scaled by `C`. Then `v = C • w`.
  The essential vector `w + (v - C • w)` equals `w`, so `v - C • w = 0`. With
  `C = 0` this gives `v = 0`.
- `eq_smul_essentialVector_of_satisfiesScaledEssentialIdentity` states the
  same conclusion for the published `essentialVector h π ℓ hu`. Here `hu` is
  unique existence of an essential vector.
- `IsEssentialVector.smul` proves the converse direction: for essential `w`,
  the vector `C • w` satisfies the identity scaled by `C` and is restriction
  invariant. So, under uniqueness, the hypotheses of the source step describe
  exactly the multiples of `w`.
- `exists_eq_smul_of_mem_levelFixedVectors` proves the following line clause.
  Let `w` be essential and the only essential vector. Suppose every vector of
  the published `levelFixedVectors (modelRepresentation π ℓ) a` satisfies the
  identity scaled by some complex constant. Then every such vector is
  `C • w` for some `C`. Restriction invariance of level-fixed vectors is the
  published `isIntegralInvariantOnRestriction_of_mem_levelFixedVectors`.

## Provenance and remaining obligations

The unit has internal provenance. Its steps are linearity of the Bochner
integral, elementary facts about scalar multiples of rational functions, and
uniqueness of the essential vector, which is supplied as a hypothesis.
The cited step of JPSS 1981, printed page 214, is the only source content
here. In the source, the scaled identity for a `K(m)`-fixed `W₁` comes from
the functional equation and the support argument of printed pages 212–214,
with `C` constant because the polynomial there is constant. Those arguments
are not formalized here: the scaled identity for level-fixed vectors is a
hypothesis. Existence and uniqueness of the essential vector, the epsilon
factor, and the vanishing below level `m` are not proved. This unit does not
prove `EssentialConductorStatement`.
