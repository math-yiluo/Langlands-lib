# Standard rational refinement of finite rational point covers

Author: Worker 743. The target and its scope were specified by Worker 146.

`Langlands.Analytic.StrictTestDomain.FiniteRationalRefinementStatement` is a
proposition-valued definition, not a theorem or an assumption of refinement.
It quantifies over a complete ultrametric normed field `K`, a presented strict
affinoid algebra `P` over `K`, a finite index type `I`, and a family
`D : I → RationalData K P`. The field, the carrier of `P` and `I` all live in
one arbitrary universe `u`.

The hypothesis is the actual point-cover condition
`∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus`. Here `(D i).locus` is the
existing unit-radius rational locus: the points `x` with
`x ((D i).numerator k) ≤ x (D i).denominator` for every numerator index `k`.

The conclusion asserts the existence of three pieces of data. They are a
length `n : ℕ`, a tuple `f : Fin n → P`, and a proof
`h : ∀ x : BanachSpectrum P, ∃ k, x (f k) ≠ 0` that the tuple has no common
zero on the spectrum. These must satisfy
`∀ j : Fin n, ∃ i : I, (standardRational f h j).locus ⊆ (D i).locus`.
The datum `standardRational f h j` is the published standard rational datum
with denominator `f j` and numerator tuple `f`, so by
`mem_standardRational_locus` its locus is the set of points where
`x (f k) ≤ x (f j)` for all `k`. Thus every member of the standard cover
attached to `f` lies inside some member of the given cover. Nothing is said
about which index `i` is chosen for a given `j`.

## Geometric scope

The statement concerns subsets of `BanachSpectrum P` only. It uses the
existing `standardRational` data and the existing `RationalData.locus`. It
constructs no output algebra and asserts no gluing, sheaf condition, exactness,
localization, analytic acyclicity or restriction-map compatibility.

The published theorem `standardRational_covers f h` already shows that the
standard loci cover the whole spectrum. The refinement is therefore a genuine
cover refinement: for a nonempty spectrum `n` must be positive. Also, every
spectrum point lies in a standard locus that is contained in some `(D i).locus`.

Each inclusion produced by the statement can be fed to the existing interface in
`Langlands.Geometry.Analytic.StrictTestDomain.RationalCategory`, which this
module does not import. There `RationalData.Inclusion.mk` turns `hsub` into an
inclusion `RationalData.Inclusion (standardRational f h j) (D i)`, and
`RationalData.Inclusion.restriction` yields the actual bounded restriction map
`(D i).algebra → (standardRational f h j).algebra`. That interface requires a
complete scalar field, which is one reason `[CompleteSpace K]` appears here.
The refinement argument itself does not use completeness. The quantifier list
also matches the companion target `WholeSpectrumRationalGluingStatement`.

## Edge cases

No nonempty index type, positive length, nonempty numerator tuple, nonempty
locus, nonzero or reduced algebra, or nontrivial scalar valuation is assumed.

- If `I` is empty, the hypothesis implies that `BanachSpectrum P` is empty.
  The conclusion then forces `n = 0`, since `∃ i : I` cannot be met. With
  `n = 0`, `f` is the empty tuple, `h` holds vacuously because there are no
  points, and the refinement condition is vacuous.
- If `BanachSpectrum P` is empty, for example when `P` is the zero algebra,
  the hypothesis holds trivially and `n = 0` again witnesses the conclusion.
- A datum with empty numerator tuple has the whole spectrum as its locus; its
  no-common-zero field then forces the denominator to vanish nowhere.
- Empty loci in the given family are permitted.
- The tuple `f` may contain repetitions, and distinct `j` may give equal loci.
- Nonreduced `P` is permitted. Loci depend only on the evaluations of
  elements at spectrum points.

## Source correspondence

The source is Piotr Achinger, *Introduction to non-Archimedean Geometry*
(November 22, 2020), Lemma 7.2.2 and its proof, printed/PDF pp.65–66. It is
registered as `achinger-2020-non-archimedean-geometry-nov22`, SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.
No registered errata for it were found in the Library notes on 2026-10-27.
The lemma states that every finite covering of `X = Sp A` by affinoid
subdomains is refined by a rational covering. Its proof first applies the
Gerritzen–Grauert theorem to reduce to coverings by rational domains, and then
proves that such a covering is refined by a rational covering. This target
records only the second step: its inputs are already rational data, so
Gerritzen–Grauert is not needed. A rational covering in the sense of
Definition 7.2.1, p.65, is the family of loci `|f_j| ≤ |f_i|` for `j ≠ i`. The
published `standardRational` datum keeps the redundant `j = i` inequality, which
does not change the locus.

Achinger writes each `U_i` as `X(f_{i1}, …, f_{iN} / f_{i0})` with one common
`N`. He indexes the refining cover by the maps `φ : {1, …, n} → {0, …, N}` that
take the value `0`, the denominator, at least once. The refining tuple consists
of the products `g_φ = ∏_i f_{iφ(i)}`. Two points of the source argument are
pointwise:

1. No common zero. At a point `x`, choose `i₀` with `x ∈ U_{i₀}`; then the
   denominator of `U_{i₀}` is nonzero at `x`. For every other `i`, some entry of
   the extended tuple is nonzero at `x`. The resulting product is nonzero.
2. Refinement. If `φ(i₀) = 0`, then `V_φ ⊆ U_{i₀}`. Take `x ∈ V_φ` and a
   numerator index `j`, and choose `i₁` with `x ∈ U_{i₁}`. If `i₁ ≠ i₀`, replace
   `φ` by `ψ` with `ψ(i₀) = j`, `ψ(i₁) = 0`, and `ψ = φ` elsewhere; `ψ` is
   admissible because `ψ(i₁) = 0`. Since `x ∈ V_φ`, the source has
   `|g_ψ(x)| ≤ |g_φ(x)| ≠ 0`. Cancelling the common nonzero factors with
   `i ≠ i₀, i₁` gives
   `|f_{i₀j}(x)| · |f_{i₁0}(x)| ≤ |f_{i₀0}(x)| · |f_{i₁φ(i₁)}(x)|`.
   The right factor is at most `|f_{i₁0}(x)|` because `x ∈ U_{i₁}`, and
   `|f_{i₁0}(x)| ≠ 0`. Cancelling it gives `|f_{i₀j}(x)| ≤ |f_{i₀0}(x)|`.
   The source's phrase "`x ∈ U_φ`" in this step refers to `V_φ`.

The denominator restriction matters. The refinement step assigns to each
admissible `φ` an index `i₀` at which `φ` selects the denominator. A choice made
only of numerators has no such index, so the source argument gives no
containment for its locus. Using all products without this restriction does not
establish the stated refinement. In the formal setting the data `D i` have
varying arities `(D i).arity`, so a faithful construction needs dependent finite
choices, as described below, rather than a common `N`.

## Internal extension of the source's scope

Achinger works with the maximal spectrum `Sp A` and assumes on p.6 that the
scalar field is complete and nontrivially valued. This target instead uses
the points of `BanachSpectrum P`, which are bounded multiplicative seminorms,
and permits trivially valued `K`. This is a derived extension, not a quotation
of the source. The two pointwise arguments above use only the following facts.
Spectrum points are multiplicative and nonnegative on `P`. Finite products of
positive reals are positive. Positive factors can be cancelled from a real
inequality. A point in a rational locus has nonzero denominator, by the
datum's no-common-zero field. No scalar of norm less than one, no maximal
ideal, and no Noetherian or reducedness property is used. Hence the same finite
argument applies to Banach-spectrum points over any ultrametric `K`.
Vladimir G. Berkovich, *Non-Archimedean analytic spaces* (Trieste lectures,
2009), Exercise 2.2.2(ii)–(iii), printed/PDF p.9, supplies the rational-domain
context: rational domains defined by elements without common zeros on the
spectrum, and their stability under intersection. It is registered as
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

## Remaining proof obligation

A separate proof task must prove `FiniteRationalRefinementStatement`. A route
faithful to the source is as follows. Extend each datum's numerator tuple by its
denominator, for example as `e i : Option (Fin (D i).arity) → P` with
`e i none = (D i).denominator`. Then take the finite type of dependent choices
`φ : ∀ i, Option (Fin (D i).arity)` with `∃ i, φ i = none`, and form the products
`g φ = ∏ i, e i (φ i)`. Enumerate this finite type by `Fin n` to obtain `f`,
prove `h` by step 1 above, and prove each inclusion by step 2 for an index `i₀`
with `φ i₀ = none`. The proof must cover empty `I`, an empty spectrum and empty
numerator tuples without additional hypotheses. This module proves none of
these facts; it only states the target.
