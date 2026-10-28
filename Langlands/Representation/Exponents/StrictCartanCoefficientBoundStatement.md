# Strict exponential Cartan coefficient bound from normalized Jacquet bounds

Author: Worker 693.

`Langlands.GLStrictCartanCoefficientBoundStatement` is a `Prop`-valued
definition specifying an estimate. This pair proves neither the estimate nor
integrability. It is a **derived specialization** of the coefficient
asymptotic and finite spectral arguments in Casselman [C95], §4.3.4 and §4.4,
and Waldspurger [W03], I.4.3, p.245, and the proof of III.1.2, pp.263–264.
The exact coordinate weight and uniform estimate below are not quoted
verbatim from either source. In the retained C95 draft, 4.3.4 is labelled
**Corollary**, following Theorem 4.3.3.

## Exact statement and scope

Quantify every prime `p`, every finite p-adic field `F : PadicField.{uF} p`,
every supplied compatible `T : F.TopologicalData`, and every positive rank
`n`. Independently quantify `V : Type uV` with `AddCommGroup V` and `Module ℂ V`,
a representation `ρ` of the actual `GeneralLinear n F.Carrier` on `V`, and a
homomorphism `ω : F.Carrierˣ →* ℂˣ`. All smoothness and admissibility use the
topology supplied by `T`, installed by the `letI` in the proposition.

The hypotheses are precisely:

1. `IsAdmissible ρ`, which includes smoothness.
2. For every `a : F.Carrierˣ` and every `v : V`,
   `ρ (GeneralLinear.scalar a) v = (ω a : ℂ) • v`.
3. `‖(ω a : ℂ)‖ = 1` for every `a`.
4. For every standard ordered block shape `B`, every character
   `χ : (Fin B.length → F.Carrierˣ) →* ℂˣ` satisfying
   `T.IsJacquetExponent B ρ χ`, and every block scalar `a`, if
   `i ↦ T.normalizedAbs (a i : F.Carrier)` is monotone and two of these
   absolute values differ, then `‖(χ a : ℂ)‖ < 1`.

Hypothesis 4 is exactly the strict exponent test in
`GLSquareIntegrableExponentCriterionStatement`. The criterion is a
specification comparison only; its module is not imported and its conclusion
is not used. The exponent is the published generalized eigencharacter of the
**normalized** upper Jacquet module, with its published open-kernel
condition. For one block, the unequal-absolute-values premise is impossible.
This empty test is retained, and unitarity of `ω` remains a separate premise.

There is no irreducibility, finite length, finite-dimensionality, nonzero
carrier, or globally finite exponent spectrum assumption. In particular,
the zero representation is included: its coefficient is zero. Unitarity of
the supplied `ω` is explicitly assumed even when the action cannot determine
`ω` on a zero space.

For each `v : V` and `ℓ : SmoothDual ρ`, the conclusion supplies
`C : ℝ`, `d : ℕ`, and `r : ℝ` with
`0 < C`, `0 < r`, and `r < 1`. They are uniform in every normalized integer
tuple `lam : Fin n → ℤ` and both
`k₁,k₂ ∈ GeneralLinear.CartanQuotient.maximalCompact T n`:

```text
‖ℓ.1 (ρ (k₁ * representative T lam * k₂) v)‖
  ≤ C * Real.sqrt (delta T lam) * (height lam)^d
      * Real.rpow r (height lam - 1).
```

Here all three named functions are the existing
`GeneralLinear.CartanQuotient` definitions. The compact subgroup is the
actual image of `GL_n(O_F)` in `GL_n(F)`, and `representative T lam` is the
actual diagonal matrix with entries `ϖ^(lam i)` for the specified
uniformizer. `Normalized lam` means decreasing nonnegative integer
coordinates with some coordinate zero. With `q = T.residueCardinality`,

```text
degree lam = ∑_{i<j} (lam i - lam j),
delta T lam = q^(-degree lam),
height lam = 1 + ∑_i |lam i|.
```

The power defining `delta` has an integer exponent; `Real.rpow` is used for
the strict decay factor. Constants can depend on `p,F,T,n,ρ,ω,v,ℓ`; there
is no claim of uniformity in these inputs. The formula supplies the positive
half modulus, not its inverse. At rank one, normalization forces `lam = 0`,
so `degree = 0`, `delta = 1`, `height = 1`, and the decay factor is
`r^0 = 1`. No extra noncentral test is inserted in this case.

## Original sources and reading

[C95] W. Casselman, *Introduction to the theory of admissible
representations of p-adic reductive groups*, draft of 1 May 1995.
Literature ID `casselman-1995-admissible-representations`; SHA256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
Retained original:
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
Printed and PDF page numbers coincide.

Read pp.41–45. Theorem 4.3.3, p.42, identifies a fixed coefficient with
its Jacquet pairing when the simple roots outside a prescribed Levi are
sufficiently small. Corollary 4.3.4, p.43, takes a common threshold over
the finitely many standard parabolics and partitions the full chamber
into the corresponding strata. Section 4.4, pp.43–44, uses the finite
translation span of a function, its associated generalized characters,
and finite translates of lattice cones. The passage before Theorem
4.4.6, pp.44–45, describes generalized central-character components.
Theorem 4.4.6 and its integrability conclusion are not inputs to this
statement or the proposed proof route. C95 leaves the elementary
lattice results 4.4.1–4.4.3 without proofs; the source citation alone
does not discharge them.

[W03] J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003),
235–333, DOI `10.1017/S1474748003000082`.
Literature ID `waldspurger-2003-plancherel`; SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Retained original:
`/home/taskhub/central-library/Waldspurger--La formule de Plancherel pour les groupes p-adiques d'apres Harish-Chandra--2003.pdf`.
Read printed p.245 and pp.263–264 (PDF pages 11 and 29–30).

Proposition I.4.3 applies to an admissible representation and a fixed
pair of vectors, choosing the relevant parabolic from the chamber
point. On p.264 the proof of III.1.2 reduces by compact translates and
chamber strata to a finite sum
`δ_P(a)^(1/2) ∑_{χ∈E} χ(a) Q_χ(H_M(a))`, with `E` finite and each `Q_χ`
a polynomial. It obtains `q^(-ε σ(a))` with `ε > 0` from strict positivity
of the real parts of those characters. III.1.2 itself assumes square
integrability, and the printed proof obtains strict positivity through
III.1.1. Here strict exponent bounds are a direct hypothesis instead.
Neither III.1.1 nor III.1.2, their analytic hypotheses, their conclusions,
or their classification consequences are used as proved inputs.

A bounded filename search in the project literature and central library
located no erratum for these passages. The first pages of the retained
March and June 2026 Savin addenda were checked: they concern intertwining
operators and reducibility of induced representations, rather than these
coefficient passages. This is a record of the search scope, not a claim
that no correction can exist.

## Derived GL identifications and the intended proof bridges

The following explains the mathematical route and its remaining formal
obligations. None of these bridges is proved by this proposition
definition.

1. **Actual compact factors and smooth vectors.** The integral image
   `K = maximalCompact T n` must be shown compact for the supplied
   topology. The stabilizer of a smooth vector is open, so its
   intersection with `K` is an open subgroup of the compact group `K`
   and has finite index. Consequently the set of actual translates
   `ρ(k)v`, for `k ∈ K`, is finite, not just finite dimensional.
   The same argument applies to `ℓ`, since it belongs to the smooth
   part of the algebraic dual. More precisely,
   `ℓ(ρ(k₁ a k₂)v) = (ρ.dual(k₁⁻¹)ℓ)(ρ(a)(ρ(k₂)v))`.
   Thus finitely many pairs of vectors suffice for both compact
   factors. This observation uses smoothness and compactness; it does
   not require a finite-dimensional representation carrier.

2. **Signs, strata, and bounded offsets.** For the upper Borel,
   `|ϖ^(lam i)| = q^(-lam i)`. Decreasing integer coordinates therefore
   give increasing absolute values, exactly the monotone chamber in
   the hypothesis. Use a common asymptotic threshold for the finitely
   many translated vector pairs and standard parabolics, as in C95
   4.3.4. Write `s_i = lam i - lam(i+1) ≥ 0`. A stratum declares each
   gap small or large relative to this threshold. Adjacent coordinates
   joined by small gaps form contiguous blocks. Within each block,
   subtract its last coordinate to obtain an offset with bounded
   nonnegative integer coordinates. There are finitely many offsets.
   The remaining tuple is constant on each block and is a block-scalar
   lattice point. This gives finitely many strata and fixed offset
   translates on which the normalized Jacquet asymptotic applies.
   An interior-chamber assertion alone does not cover these faces.

3. **Only coefficient-relevant finite spectra.** For each of the
   finitely many block shapes, vector pairs, and bounded offsets,
   take the image of the translated vector in the corresponding
   Jacquet module. Jacquet admissibility and smoothness are needed
   to put that image in a finite-dimensional space fixed by a
   suitable compact open Levi subgroup. The split centre commutes
   with that subgroup and hence preserves the fixed space. Its
   orbit span is therefore finite dimensional. Simultaneous
   generalized-character decomposition on this space yields
   finitely many spectral components for this coefficient.
   One must identify every occurring character with the published
   `T.IsJacquetExponent B ρ χ`, including its open kernel and a
   uniform nilpotence power. Evaluation by the Jacquet pairing then
   yields finite sums of characters times polynomials on the block
   valuation lattice. Admissibility does **not** assert a globally
   finite exponent spectrum for an arbitrary admissible carrier.
   Only the finite sets just constructed are used.

4. **Positive uniform decay from finitely many tests.** For a block
   shape with at least two blocks, let `z_j` be the block scalar
   equal to `ϖ` on the first `j` blocks and `1` on the remaining
   blocks. It satisfies the monotone and unequal absolute value
   premises. Hence each relevant character satisfies
   `0 < ‖χ(z_j)‖ < 1`. Its norm is a product of these values to
   nonnegative gap powers. If `m_j` is the total size of the first
   `j` blocks, choose
   `r = max_{χ,j} ‖χ(z_j)‖^(1/m_j)` over the finitely many relevant
   characters and noncentral generators. This maximum lies strictly
   between zero and one, and gives a bound by
   `r^(∑_j m_j * gap_j)` on the normalized block-scalar lattice.
   If this finite set is empty, choose any `0 < r < 1`.
   For the full normalized tuple,
   `height lam - 1 = ∑_{i=0}^{n-2} (i+1) * s_i`; replacing it by the
   block-scalar height changes it by a bounded amount depending on
   the offset. This bounded change is absorbed in `C`.
   This finite maximum is the essential justification for a strictly
   positive decay exponent. Pointwise strict bounds over a possibly
   infinite global spectrum would not justify a common `r < 1`.

5. **Polynomials, modulus, and central directions.** The finite
   spectral orbit spaces give a finite maximal polynomial degree
   `d`; each polynomial in the valuation variables is bounded by a
   constant times `height^d`. The normalized Jacquet action
   contributes `δ_(P_B)^(1/2)`. On block scalars this equals the
   upper-Borel half modulus, since roots within a block are trivial.
   On a stratum's bounded offset, the remaining root and modulus
   ratios are fixed positive constants. Identifying these products
   with `Real.sqrt (CartanQuotient.delta T lam)` and absorbing the
   finitely many ratios into `C` are required GL calculations.
   Common scalar multiplication acts as `ω`, already on every
   vector and hence on Jacquet images; the modulus on that scalar
   is one. Its norm is one by the separate unitarity premise.
   There is also no nilpotent polynomial growth in the scalar
   direction because the action is exactly scalar. Thus removing a
   common valuation shift introduces no growth in coefficient norm.
   Unit factors of block scalars have finite image under the smooth
   characters and have norm one. These facts account for the
   central quotient normalization without assuming integrability.

6. **Global constants and degenerate cases.** Take a maximum of
   the finitely many degrees and constants and the largest of the
   finitely many bases below one; `height ≥ 1` permits these
   comparisons. Enlarge `C` to be strictly positive and to cover
   the finite region where all gaps are bounded. The one-block
   stratum has only bounded offsets after central normalization
   and requires no strict exponent test. At rank one this is the
   whole chamber. For a zero coefficient, including a zero carrier,
   choose positive `C`, `d = 0`, and any `0 < r < 1`; positivity of
   the explicit weights still requires the corresponding algebraic
   laws. These choices must be formalized along with the preceding
   finite reductions.

W03 uses its height `σ`, a restriction to `G¹`, and a bound involving `Ξ`
in its corollary. This statement instead fixes a concrete normalized
integer chamber and its exact `height` and `delta`. The explicit gap and
offset calculations above are needed to obtain this formula; it is not
an automatic substitution into W03's conclusion. No comparison with `Ξ`,
Haar-volume estimate, lattice summability theorem, or integrability
predicate is asserted here.

## Dependencies and independence

The direct Lean imports are only
`Langlands.Group.GL.CartanQuotientDefinitions`,
`Langlands.Representation.Exponents.Jacquet`, and
`Langlands.Representation.Smooth.Contragredient.Definitions`.
They supply the actual groups, weights, generalized exponents, and smooth
functionals. Existing imported Lean/Markdown pairs are not changed.
The bridges above are proof obligations, not assumed fields or supplied
envelopes. Published statements, pending proof tasks, and literature
citations are not treated as proof certificates.

The intended proof successor must not use the strict square-integrability
criterion or its conclusion, segment analytic classification, multisegment
special-head exhaustion, ordered special-head existence, quotient
coverage, tempered block uniqueness, square-integrable Langlands
classification, square-integrable exhaustion, regular exhaustion, their
proof successors, or their transitive dependencies. This pair introduces
only the focused statement. An exact proof task is to be published
separately after this target is accepted and present in the Library.
