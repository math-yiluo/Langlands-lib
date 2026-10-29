# Square-integrable Whittaker functions on the torus lattice

Authors: Worker 381 (draft), Worker 906.

This module defines the closed proposition
`Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSumStatement.{uF,uV}`.
It states that, for an irreducible square-integrable representation of
`GL_(m+1)(F)`, every Whittaker function of the coefficient model is
square-summable on the uniformizer lattice of the diagonal torus modulo the
center, against the inverse upper-Borel modulus. It is a statement target,
not a proof.

## Quantifiers and hypotheses

Every prime `p`, field `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData` and `m : ℕ` is quantified, with the local instances
`T.topology`, `T.valuativeRel` and `T.localField`. No measurable structure
or measure occurs in the statement.

Every `ψ : UnitaryAdditiveCharacter F.Carrier` is quantified. The carrier
`V : Type uV` has its own universe parameter and only `AddCommGroup V` and
`Module ℂ V`. The representation is an actual
`π : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) V`, and the
hypotheses are exactly `Representation.IsIrreducible π` and the published
analytic predicate `T.IsSquareIntegrable π` of `Classification.Tempered`:
for every Borel Haar measure on the central quotient `GL_(m+1)(F) / Z`,
`IsSquareIntegrableModCenter` holds (admissibility, a unitary central
character, and `MemLp` exponent two of the norms of all smooth matrix
coefficients). There is no genericity, nonzero-functional, unitarization,
temperedness, classification or Whittaker-integrability hypothesis.

Every `ℓ : glFunctionals ψ m π` (zero included) and every
`f : (coefficientModel π ℓ).toSubmodule` (zero included) is quantified.
`glFunctionals ψ m π` consists of the algebraic functionals with
`ℓ (π u v) = θ_ψ(u) ℓ v` for upper unipotent `u`, with the standard character
`θ_ψ(u) = ψ(u_(1,2) + ⋯ + u_(m,m+1))`; the coefficient model is the image of
`v ↦ (g ↦ ℓ (π g v))`. So `f.val.val : GL_(m+1)(F) → ℂ` is the Whittaker
function `W(g) = ℓ (π g v)` of some vector `v`.

Finally every unit `ϖ : F.Carrierˣ` with
`Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ` is
quantified: `v ϖ < 1` and every nonzero valuation is an integer power of
`v ϖ`.

## Conclusion

For `λ : Fin m → ℤ` put `μ(λ) = Fin.snoc λ 0 : Fin (m + 1) → ℤ`, the exponent
vector `(λ_1, …, λ_m, 0)`, and let `a(λ) = Iwasawa.torus ϖ μ(λ)`, the
diagonal matrix `diag(ϖ^(λ_1), …, ϖ^(λ_m), 1)`. With

`δ(a) = ∏_{i < j} |a_i / a_j|`

for the normalized absolute value `T.normalizedAbs` (the upper-Borel modulus
`δ_B(a) = ∏_{i<j} |a_i/a_j|`, written exactly as the modulus `δ` in the
published `IwasawaTorusSumStatement` and `QuotientIwasawaIntegrationStatement`),
the proposition asserts

```lean
Summable (fun lam : Fin m → ℤ =>
  (∏ i : Fin (m + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (m + 1) => i < j),
    T.normalizedAbs ((ϖ ^ μ lam i / ϖ ^ μ lam j : F.Carrierˣ) : F.Carrier))⁻¹ *
    ‖f.val.val (Iwasawa.torus ϖ (μ lam))‖ ^ 2)
```

The terms are nonnegative real numbers, so `Summable` in `ℝ` is the
convergence of `∑_λ δ(a(λ))⁻¹ |W(a(λ))|²`, independently of any order of
summation.

The last exponent is fixed to `0` because the center is divided out: the
modulus is invariant under scalar matrices, and the unitary central character
gives `|W(z a)| = |W(a)|` for scalar `z`, so the fixed-last-coordinate
lattice is a set of representatives of the torus lattice modulo the central
lattice `ℤ·(1, …, 1)`. For `m = 0` the index type is a single point and the
proposition is trivial.

## Relation to the source

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg
Convolutions*, American Journal of Mathematics 105 (1983), 367–464,
registered `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
Section 8.3, printed p.449 (one-based PDF page 84, read visually; the scan
has no text layer there). There, for square-integrable `π`, the source says
"Since the elements of `W(π; ψ)` are K-finite and square-integrable mod
`N_r Z_r`, we deduce that" its formula (2),
`∫_{N_(r-1) \ G_(r-1)} |W(diag(g, 1))|² |det g|^(-1) dg = ‖W‖² < +∞`, using
the integration formula (1) on the same page. The source writes the
square-integrability only in words; in formulas (our paraphrase) it is
`∫_{Z_r N_r \ G_r} |W(g)|² dg < +∞`. No registered errata for this source
were found.

The present proposition is a derived, measure-free consequence of that
square-integrability. Write `g = n a κ` (Iwasawa decomposition, `n` upper
unipotent, `a` diagonal, `κ` in the maximal compact subgroup
`K = GL_(m+1)(𝒪)`); a Haar measure on `G` is `δ(a)⁻¹ dn da dκ`, so the
invariant measure on `N \ G` is `δ(a)⁻¹ da dκ`. In the source's setting `W`
is smooth, so it is invariant under right translation by an open compact
subgroup `K_0 ⊆ K`. Let `A(𝒪)` be the diagonal integral units. For
`u ∈ A(𝒪) ∩ K_0` and `κ ∈ K_0` one has `δ(ϖ^μ(λ) u) = δ(a(λ))` and
`|W(ϖ^μ(λ) u κ)| = |W(a(λ))|`, and the sets `ϖ^μ(λ) (A(𝒪) ∩ K_0) Z` are
pairwise disjoint because the vectors `(λ, 0)` are pairwise distinct modulo
`ℤ·(1, …, 1)`. Restricting the integral to these pieces gives

`∫_{Z N \ G} |W|² ≥ c · ∑_λ δ(a(λ))⁻¹ |W(a(λ))|²`

with `c > 0` the product of the volume of the image of `A(𝒪) ∩ K_0` in
`Z \ A` and the volume of `K_0`. Hence square-integrability of `W` modulo
`Z N` implies the proposition. Only
the lattice points are retained: this is the form used to deduce the
restriction-square estimate (7) of p.450, see below.

## Derived formulation

1. **Matrix coefficients, not Whittaker functions, in the hypothesis.** The
   hypothesis `T.IsSquareIntegrable π` concerns smooth matrix coefficients
   modulo the center. The source does not prove the passage from it to
   square-integrability of Whittaker functions; this proposition records
   that bridge in a measure-free form, as a separate proof obligation.
2. **Lattice sum instead of an integral.** No quotient measure, Haar
   normalization or measurability statement is needed; positive constants
   are irrelevant to summability.
3. **Zero functionals and vectors.** For `ℓ = 0` or `f = 0` every term is
   zero; these cases are included.
4. **Every uniformizer.** The statement is asserted for every uniformizing
   element, which avoids choosing one; the source argument above applies to
   each of them.

## Expected proof route

Not part of the statement; recorded to guide the separate proof task.
A smooth Whittaker function vanishes at `a(λ)` unless `|a_i/a_(i+1)|` is
bounded for every simple root, with a bound depending only on `W` (the
published theorem `Langlands.Whittaker.smoothSimpleRootSupport`). On that
cone, the asymptotic expansion of Whittaker functions (Library statements
`Langlands.WhittakerTypeAsymptoticStatement` and
`Langlands.WhittakerLastEntryOneAsymptoticStatement`, not yet proved) writes
`W(a(λ))` as a finite combination of finite functions of `λ`. Casselman's
square-integrability criterion
(`Langlands.GLSquareIntegrableExponentCriterionStatement`, not yet proved)
bounds the exponents of the normalized Jacquet modules strictly. Relating the
characters of the expansion to those exponents (as in Casselman's asymptotic
theory) gives geometric decay of `δ(a(λ))⁻¹ |W(a(λ))|²` on the cone, hence
summability. The published expansion statements do not themselves tie their
characters to Jacquet exponents, so that link is part of the proof
obligation. Their hypotheses also differ from the present ones: they use the
topology of `F.canonicalTopologicalData` rather than the supplied `T`, and
assume admissibility, finite generation of `ρ.asModule` over the group
algebra, and a nonzero equivariant functional unique up to scalars.
Supplying these from `Representation.IsIrreducible π` and
`T.IsSquareIntegrable π` (the case `ℓ = 0` being trivial) is part of the
proof obligation as well.

## Use

The proposition is the representation-theoretic input of the planned proof
of `Langlands.RankinSelberg.SquareIntegrableWhittakerRestrictionStatement`
(JPSS formula (7), proof task `5e33bf2f-5ef0-4456-af2b-d03e46eab364`). For
`r = m + 1 = n + k + 2` and `t = n + 1`, the weight of the target integrand
at `diag(ϖ^λ, 1_(k+1))` satisfies

`δ_t(ϖ^λ)⁻¹ |det ϖ^λ|^(-(k+1)) = δ_r(diag(ϖ^λ, 1_(k+1)))⁻¹`,

so after the Iwasawa decomposition of `N_t \ G_t` and a finite cover of the
compact factor by right translates of `W`, the target is bounded by finitely
many sub-sums of this lattice sum (exponent vectors `(λ, 0_k, 0)`).
