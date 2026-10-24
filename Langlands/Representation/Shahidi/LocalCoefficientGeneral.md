# Shahidi's local coefficient over a general nonarchimedean local field

This module defines the relation "`C` is the local coefficient
`C_χ(s, π₁ ⊗ π₂)`" for the actual induced representation `I(s, π₁ ⊗ π₂)`
over any nonarchimedean local field `F`, including fields of positive
characteristic. The source is F. Shahidi, *Fourier transforms of intertwining
operators and Plancherel measures for GL(n)*, American Journal of Mathematics
106 (1984), 67–111, printed pages 72–73:

\[
\lambda^{-s}_{\pi'}\bigl(A(s,\pi,w_{m,n})f\bigr)=C_\chi^{-1}(s,\pi)\,\lambda^s_\pi(f)
\qquad (0.3)
\]

for all `f ∈ I(s,π)`, where `π = π₁ ⊗ π₂` and `π' = π₂ ⊗ π₁`.

The registered original is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
Printed page `p` is index `p - 66` of the scan. The author of this unit,
Worker 33, read printed pages 67, 70–73, 78 and 84 directly.

The unit restricts the published function-level relation `IsLocalCoefficient`
of `Langlands.Representation.Shahidi.LocalCoefficient` to the actual
general-field induction of `Langlands.Representation.Shahidi.Induction`. It
follows the published p-adic specialization
`Langlands.Representation.Shahidi.LocalCoefficientPadic`, whose declarations
it does not change. Where that unit uses a `PadicField` realization and its
residue cardinality, this unit uses a field with Mathlib's
`IsNonarchimedeanLocalField` and keeps `q` and the absolute value as explicit
parameters.

## Setting in the source

The introduction (page 67) takes "`F` a nonarchimedean local field". Printed
page 70 (§0) works over "a nonarchimedean field" `F` with ring of
integers `O`, maximal ideal `P`, `q = [O : P]` and a uniformizer `ϖ` with
`|ϖ| = q⁻¹`. No restriction on the characteristic is stated there. The
character `χ` of the upper unipotent radical `N_r` of `G_r = GL_r(F)` is
`χ(n) = ψ(n₁₂ + ⋯ + n_{r-1,r})` for a nontrivial additive character `ψ`, and
`π` is non-degenerate if some functional `λ` satisfies
`λ(π(n) v) = χ(n) λ(v)` (pages 70–71). On page 71, `P` is the standard
parabolic of `G_r`, `r = m + n`, with Levi `G_m × G_n` and unipotent radical
`U`.

On page 72, `V = w_r U w_r⁻¹` and `U' = ᵗV`, `π₁` and `π₂` are irreducible
admissible representations of `G_m` and `G_n`, and `I(s, π)` is the space of
`K_r`-finite functions `f` from `G_r` to the space of `π` with

\[
f\!\left(\begin{pmatrix} g_1 & 0 \\ 0 & g_2 \end{pmatrix} u g\right)
= |\det g_1|^{1/2(s+n/2)} / |\det g_2|^{1/2(s+m/2)}\,
\pi_1(g_1) \otimes \pi_2(g_2) f(g).
\]

Then:

- (0.1) `A(s, π, w_{m,n}) f(g) = ∫_{U'} f(w_{m,n} u' g) du'` for
  `Re(s) ≫ 0`; "As a function of `s`, it has a meromorphic continuation to a
  rational function of `q^{-s}` on `C`";
- (0.2) `λ^s_π(f) = ∫_{U'} ⟨f(w_{m,n} u'), λ₁ ⊗ λ₂⟩ \overline{χ(u')} du'`,
  for two fixed `χ`-Whittaker functionals `λ₁` and `λ₂` of the
  non-degenerate `π₁` and `π₂`;
- (0.3) above, where `λ^{-s}_{π'}` is the Whittaker functional of
  `I(-s, π')` given by
  `λ^{-s}_{π'}(f) = ∫_U ⟨f(w_{m,n}⁻¹ u), λ₂ ⊗ λ₁⟩ \overline{χ(u)} du`.

Page 73 says that "`λ₁ ⊗ λ₂` denotes the map induced by `λ₁ × λ₂` on the
tensor product of the spaces `V₁` and `V₂`", and that `C_χ(s, π)` depends on
the measures defining `A(s, π, w_{m,n})`, `λ^s_π` and `λ^{-s}_{π'}`. Page 78,
(1.1)–(1.2), explains that the Whittaker integrals may be taken over a
sufficiently large compact open subgroup. The Library's `HasJacquetIntegral`
and `HasSwappedJacquetIntegral` are these stabilized integrals; the published
Markdown of `LocalCoefficient` explains them.

## The induction-exponent display

Read literally, the display on pages 67 and 72 has exponents `s/2 + n/4` on
`|det g₁|` and `-(s/2 + m/4)` on `|det g₂|`. The published general-field
`Shahidi.source` implements the normalized exponents `(s + n)/2` and
`-(s + m)/2`: the positive half of the modulus
`δ_P(diag(g₁, g₂)) = |det g₁|^n / |det g₂|^m` together with the twists `s/2`
and `-s/2`. `Shahidi.target`, the space `I(-s, π₂ ⊗ π₁)`, is the same
normalized construction for the blocks `(n, m)` and the parameter `-s`. The
published Markdown of `Induction` explains this choice. It rests on Lemma 2.2
on printed page 84, for `m = n`: there `A(s, π, w₀) f(g)` is a limit of
integrals of `π₁(-a) ⊗ π₂(a⁻¹) |det a|^{s-n} f(v_a g) ψ_m(a) da`. The proof
starts from Lemma 2.1, whose integrand carries `|det a|^{-n} d*a`, and uses
`w₀ (1, a⁻¹; 0, 1) = (-a, 1; 0, a⁻¹)(1, 0; a, 1)`. With `d*a = |det a|^{-n} da`,
the normalized exponents give `|det a|^{s+n}` for the diagonal factor and the
total `|det a|^{s-n}` of the lemma; the literal exponents would give
`|det a|^{s-3n/2}`. That reading is an interpretation of the source's
computations, not a published erratum. This unit adds no
induction of its own. It inherits that interpretation through `sourceEval`,
`targetEval` and `intertwiningInduced`.

The source uses `K_r`-finite functions. The Library's induction consists of
smooth functions, and `Induction` leaves the comparison open. This unit does
not prove it.

## Compact open cofinality of the Levi

- `generalLeviCompactOpenCofinal F B`: for every block shape `B`, every open
  subgroup of the actual Levi `B.Levi F = ∏ᵢ GL_{rᵢ}(F)` contains an open
  subgroup with compact underlying set. This is `CompactOpenCofinal` of
  `Langlands.Representation.Category.Contragredient`.

It is proved from the local-field hypotheses alone and is not a premise of
any declaration here. The proof:

1. `GL_r(F)` is a nonarchimedean group for the valuative topology, by the
   published `valuativeGeneralLinearNonarchimedean`.
2. `GL_r(F)` is locally compact. `F` is locally compact by
   `IsNonarchimedeanLocalField` and Hausdorff, through its additive uniform
   structure. So the matrix ring is locally compact and Hausdorff, and so is
   its unit group.
3. A private lemma pulls the nonarchimedean property back along a group
   homomorphism that is a topological inducing map. It is applied first to
   the inclusion of the block-diagonal subgroup `B.leviSubgroup F` in
   `GL_r(F)`, then to the published topological group isomorphism
   `B.leviEquivContinuous F` from the Levi product to that subgroup. So
   `B.Levi F` is nonarchimedean, and it is locally compact as a finite
   product.
4. The published `compactOpenSubgroupBasis` gives, inside the given open
   subgroup, an open subgroup with compact underlying set.

The p-adic `TopologicalData.leviCompactOpenCofinal` of `IntertwiningPadic`
was the template.

## The family of source functions

All remaining declarations lie in `Langlands.Shahidi`. Here
`F : Type uF` has `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`. `abv : AbsoluteValue F ℝ` is an absolute
value with `hopen : IsOpenNormOne abv`. The published
`isOpenNormOne_of_valuation` supplies `hopen` for an absolute value equal to
`1` on valuation units. The ranks are `m+1` and `n+1`, so all ranks are
positive. `π₁` is a complex representation of `GL_{m+1}(F)` on `V₁`, and
`π₂` is one of `GL_{n+1}(F)` on `V₂`. `V₁` and `V₂` are arbitrary complex
vector spaces. No norm, finite dimensionality, unitarity, smoothness,
admissibility or irreducibility is assumed in the definitions.

- `generalSourceFunctions abv hopen π₁ π₂ s` is the set of functions
  `g ↦ f(g)`, with values in `V₁ ⊗ V₂ = PiTensorProduct ℂ (pairCarrier V₁ V₂)`,
  for `f` in the actual `I(s, π₁ ⊗ π₂) = SourceSpace abv hopen … s π₁ π₂` on
  `GL_{(m+1)+(n+1)}(F)`. It is the range of the published `sourceEval`.
- `generalSourceFunctions_eq_range_sourceFunction`: it is also the range of
  the published linear map `sourceFunction` (by `rfl`).

## The relation for fixed functionals

The relations use the Borel structure `borel F` of `F`, installed by
`letI := borel F` as in the published general-field statements
`GeneralJacquetStatements` and `GeneralIntertwiningStatements`. The three
measures are measures on matrix spaces for the measurable structure induced
by `borel F`. `ψ` is a unitary additive character of `F`, and `q` is a
natural number. The definitions place no condition on `q`; `1 < q` enters
only the uniqueness results. A statement about the actual field must
constrain `q`, `abv`, `ψ` and the measures; this unit does not.

- `IsGeneralLocalCoefficientFor q abv hopen π₁ π₂ ψ μ μJ μJ' ℓ₁ ℓ₂ C` is the
  published `IsLocalCoefficient m n ψ ρ ℓ ℓ' μ μJ μJ' q S C` with:
  - `ρ` the published `pairRepresentation` of the Levi
    `GL_{m+1}(F) × GL_{n+1}(F)` on `V₁ ⊗ V₂`, acting by `π₁ ⊗ π₂`;
  - `ℓ = ℓ' = pairFunctional ℓ₁ ℓ₂`, the published functional `λ₁ ⊗ λ₂`
    induced by `λ₁ × λ₂`, as on page 73;
  - `S s = generalSourceFunctions abv hopen π₁ π₂ s`;
  - `μ` the measure `du'` of (0.1) on the `(n+1)` by `(m+1)` matrices, `μJ`
    the measure `du'` of (0.2) on the same matrices, and `μJ'` the measure
    `du` of `λ^{-s}_{π'}` on the `(m+1)` by `(n+1)` matrices.

  `ψ` defines the Whittaker character `χ` of the published Jacquet integrals,
  the standard character `u ↦ ψ(Σᵢ u_{i,i+1})`. The three measures are
  independent arguments. No Haar property or normalization is assumed, as
  page 73's remark on measure dependence requires.

This is a derived restriction: it introduces no new analytic condition.
Unfolding `IsLocalCoefficient`, there is a real `a` such that for every `s`
with `a < Re s`:

1. the denominator of `C` does not vanish at `q^(-s)`;
2. some `f ∈ I(s, π₁ ⊗ π₂)` has a nonzero Jacquet integral for `λ₁ ⊗ λ₂`;
3. every `f ∈ I(s, π₁ ⊗ π₂)` satisfies (0.3) with `c = C(q^(-s))`: `c ≠ 0`,
   the intertwining integral `A` of `f` against `μ` exists at every `g`, the
   Jacquet integral of `f` stabilizes to some `z`, the swapped Jacquet
   integral of `A` stabilizes to some `z'`, and `z' = c⁻¹ z`.

The convention is Shahidi's: `c` is `C_χ(s, π)`, and its inverse multiplies
`λ^s_π(f)`. The witness `C : RatFunc ℂ` is a genuine rational function,
evaluated at `q^(-s)` through the published `spectralPoint`. The relation does
not select a coefficient; it holds or fails for a given `C`.

**Why `ℓ' = λ₁ ⊗ λ₂`.** In the generic relation, the intertwining integral
`A` takes values in `V₁ ⊗ V₂`. The actual operator `intertwiningInduced`
takes values in `I(-s, π₂ ⊗ π₁)`, whose functions take values in
`V₂ ⊗ V₁`. By `hasIntegral_intertwiningInduced`, the generic `A` is
`flip⁻¹` of `intertwiningInduced f`, with `flip` the published `pairFlip`.
By the published `pairFunctional_pairFlip`, `λ₁ ⊗ λ₂` after `flip⁻¹` is
`λ₂ ⊗ λ₁`. So the generic swapped integral with `ℓ' = λ₁ ⊗ λ₂` is
`λ^{-s}_{π'}`, built from `λ₂ ⊗ λ₁`, applied to `A(s, π, w_{m,n}) f`.
`satisfiesLocalCoefficientEquation_sourceEval_iff` below proves this.

## The relation quantified over admissible choices

The standard Whittaker functionals of `π₁` form the Library submodule
`glFunctionals ψ m π₁` of `Module.Dual ℂ V₁`: the `λ` with
`λ(π₁(u) v) = χ(u) λ(v)` for the standard character `χ` of the upper
unipotent subgroup of `GL_{m+1}(F)`. On a block-diagonal unipotent matrix,
the superdiagonal entry joining the two blocks is `0`. So the standard
character of `GL_{(m+1)+(n+1)}(F)` restricts on the Levi to the product of
the standard characters of the two blocks. With this observation, which is
not formalized here, these are the source's `χ`-Whittaker functionals.

`IsGeneralLocalCoefficient q abv hopen π₁ π₂ ψ μ μJ μJ' C` means:

1. existence clause: some `λ₁ ∈ glFunctionals ψ m π₁` and some
   `λ₂ ∈ glFunctionals ψ n π₂` are both nonzero;
2. for all nonzero `λ₁ ∈ glFunctionals ψ m π₁` and nonzero
   `λ₂ ∈ glFunctionals ψ n π₂`,
   `IsGeneralLocalCoefficientFor q abv hopen π₁ π₂ ψ μ μJ μJ' λ₁ λ₂ C`.

The source fixes one pair of functionals. Condition 2 asks for every pair, so
the relation does not depend on a choice. Condition 1 is the source's
non-degeneracy and makes condition 2 nonvacuous. Under multiplicity one the
two readings agree, by
`IsGeneralLocalCoefficientFor.isGeneralLocalCoefficient` below and by
definition.

## Results

Let `π₁` and `π₂` be smooth, in the Library's sense `IsSmooth`.

- `IsGeneralLocalCoefficientFor.unique`: if `1 < q`, then for fixed `λ₁` and
  `λ₂` at most one rational function `C` satisfies
  `IsGeneralLocalCoefficientFor`. The proof is the published
  `IsLocalCoefficient.unique`, with compact open cofinality from
  `generalLeviCompactOpenCofinal` and smoothness of `π₁ ⊗ π₂` from
  `isSmooth_pairRepresentation`.
- `IsGeneralLocalCoefficient.unique`: if `1 < q`, at most one rational
  function satisfies `IsGeneralLocalCoefficient`. The existence clause
  supplies a nonzero pair, and the previous result applies to it.

The next results need no smoothness.

- `IsGeneralLocalCoefficientFor.smul`: if `C` is the local coefficient for
  `λ₁` and `λ₂`, it is the local coefficient for `a λ₁` and `b λ₂` whenever
  `a ≠ 0` and `b ≠ 0`. By `pairFunctional_smul_left` and
  `pairFunctional_smul_right`, `(a λ₁) ⊗ (b λ₂) = (b a)(λ₁ ⊗ λ₂)`, and the
  published `IsLocalCoefficient.smul` applies with the scalar `b a`.
- `isGeneralLocalCoefficientFor_smul_iff`: for `a ≠ 0` and `b ≠ 0`, `C` is
  the local coefficient for `a λ₁` and `b λ₂` if and only if it is the local
  coefficient for `λ₁` and `λ₂`. The converse direction rescales by `a⁻¹`
  and `b⁻¹`.
- `IsGeneralLocalCoefficientFor.isGeneralLocalCoefficient`: let `C` be the
  local coefficient for nonzero `λ₁ ∈ glFunctionals ψ m π₁` and
  `λ₂ ∈ glFunctionals ψ n π₂`. Assume every standard Whittaker functional of
  `π₁` is a multiple of `λ₁`, and every one of `π₂` is a multiple of `λ₂`.
  Then `IsGeneralLocalCoefficient q abv hopen π₁ π₂ ψ μ μJ μJ' C` holds. A
  nonzero functional is a nonzero multiple, so the rescaling result applies.
  The multiplicity-one hypotheses are explicit; the module does not prove
  multiplicity one.

## The literal reading of (0.3)

This result is stated for an arbitrary measurable structure on `F` with
`MeasurableAdd₂ F` and `MeasurableMul F`, a measure `μ` invariant under left
translation, and `hμ : IsModulusScaling … abv μ`, the hypotheses of the
published `intertwiningInduced`. With `borel F` it reads the clause of
`IsGeneralLocalCoefficientFor` at one section.

- `satisfiesLocalCoefficientEquation_sourceEval_iff`: let `π₁` and `π₂` be
  smooth, `ℓ₁` and `ℓ₂` arbitrary linear functionals, `f` a section in the
  convergence domain `sourceDomain` of (0.1), and `c ∈ ℂ`. Then the generic
  `SatisfiesLocalCoefficientEquation` at `sourceEval f`, with `λ₁ ⊗ λ₂` on
  both sides, holds if and only if `c ≠ 0` and, for some `z` and `z'`:
  - the Jacquet integral of `f` for `λ₁ ⊗ λ₂` stabilizes to `z`;
  - the swapped Jacquet integral of
    `A(s, π, w_{m,n}) f = intertwiningInduced f ∈ I(-s, π₂ ⊗ π₁)` for
    `λ₂ ⊗ λ₁` stabilizes to `z'`;
  - `z' = c⁻¹ z`.

  Here `intertwiningInduced` receives its cofinality input from
  `generalLeviCompactOpenCofinal`. The proof identifies the generic
  intertwining integral with `flip⁻¹ ∘ intertwiningInduced f`, using
  `hasIntegral_intertwiningInduced` and the published
  `HasIntertwiningIntegral.unique`, whose inputs are the cofinality and
  smoothness above. It then rewrites the swapped integrand with the published
  `swappedJacquetIntegrand_pairFlip_symm`, which is `pairFunctional_pairFlip`
  at each point. No integral is constructed anew.

## What is not claimed

This unit does not claim, prove or assume:

- that a local coefficient exists for any `π₁` and `π₂`;
- that the intertwining or Jacquet integrals converge or stabilize on
  `I(s, π₁ ⊗ π₂)`, that the Jacquet functional is nonzero there, or that
  (0.1) continues rationally;
- multiplicity one of Whittaker functionals;
- any normalization of `q`, `abv`, `ψ`, `μ`, `μJ` or `μJ'`;
- the comparison of the Library's smooth induction with Shahidi's
  `K_r`-finite functions;
- any gamma-factor comparison, including Theorem 5.1.

These are obligations of the general-field analytic statements of the parent
task.
