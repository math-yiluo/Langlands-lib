# Local finiteness of pointwise spans of holomorphic families

Module `Langlands.Analysis.SeveralComplex.PointwiseSpan`, namespace
`Langlands.Analysis.SeveralComplex`.

## Definition

- `pointwiseSpan a s z` for `a : Λ → E → F`, a set `s ⊆ Λ` and `z : E` is the complex span
  `Submodule.span ℂ {a μ z | μ ∈ s}` of the vectors `a μ z` with `μ ∈ s` (here `F` only needs
  to be a complex vector space).

## Results

- `exists_finset_span_eq` (**local finiteness of pointwise spans**). Let `E` and `F` be
  finite-dimensional complex normed spaces, `U ⊆ E` open, `Λ` an arbitrary index type and
  `a : Λ → E → F` a family of maps, each complex differentiable on `U`. Then every `x₀ ∈ U` has
  an open neighbourhood `V ⊆ U` and a finite set `s : Finset Λ` such that for every `z ∈ V` and
  every `l : Λ`, the vector `a l z` lies in the span of `{a μ z | μ ∈ s}`. Equivalently, on
  `V` the span of all `a l z` equals the span of the `a μ z` with `μ ∈ s`.
- `exists_finset_pointwiseSpan_eq`: the same conclusion written as an equality of spans,
  `pointwiseSpan a univ z = pointwiseSpan a s z` for all `z ∈ V`.
- `exists_finset_zero_iff` (**common zeros are locally finitely defined**). For
  `f : Λ → E → ℂ`, each complex differentiable on the open set `U`, every `x₀ ∈ U` has an open
  neighbourhood `V ⊆ U` and a finite `s : Finset Λ` such that for `z ∈ V`:
  `(∀ l, f l z = 0) ↔ (∀ μ ∈ s, f μ z = 0)`. In particular the common zero set of an arbitrary
  family of holomorphic functions is, near every point, the common zero set of finitely many of
  them.
- `exists_finset_span_eq_aux`: the statement of `exists_finset_span_eq` for spaces `E` with
  `finrank ℂ E = d`, proved by strong induction on `d`. The universes of `E`, `F` and `Λ` are
  arbitrary.

## Proof

`exists_finset_pointwiseSpan_eq` follows from `exists_finset_span_eq`: every generator of
the full span lies in the span over `s` (`Submodule.span_le`), and the span over `s` is
contained in the full span (`Submodule.span_mono`). `exists_finset_zero_iff` is the first
result with `F = ℂ`: if the `f μ z` with `μ ∈ s` vanish, their span is
`0`, so every `f l z` is `0`.

The first result is proved by strong induction on `d = finrank ℂ E`, for all `F` at once. Fix
`x₀ ∈ U` and `r > 0` with `B = ball x₀ r ⊆ U`.

1. `exists_det_witness` (module `RankWitness`) on `B` gives `z₁ ∈ B`, a finite `s₁` and `h`
   holomorphic on `B` with `h z₁ ≠ 0`, such that at points of `B` where `h ≠ 0` the members
   with indices in `s₁` span.
2. If `h x₀ ≠ 0`, then `V = B ∩ {h ≠ 0}` and `s = s₁` work.
3. Otherwise put `v = z₁ - x₀ ≠ 0` and `g(t) = h(x₀ + t v)`. Then `g` is holomorphic on the disc
   `|t| < r/‖v‖`, which contains `0` and `1`. Since `g(1) ≠ 0`, the identity theorem
   (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`) shows that `g` does not
   vanish near `0`, so `0` is an isolated zero
   (`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`). Choose `ρ > 0` with
   `ρ < r/‖v‖` and `g(t) ≠ 0` for `|t| = ρ`.
4. Hahn–Banach (`exists_dual_vector`) gives a continuous linear form `ℓ` with `ℓ v = 1`. Its
   kernel `Pk` has dimension `< d` (`Submodule.finrank_lt`, because `v ∉ Pk`). Coordinates
   `Φ (w, t) = x₀ + w + t • v` on `Pk × ℂ` are inverted by
   `π z = ((z - x₀) - ℓ(z - x₀) • v, ℓ(z - x₀))`.
5. `exists_powerSum_family` (module `ZeroCounting`) applied to `H = h ∘ Φ` and
   `b l = a l ∘ Φ` on `O = Φ⁻¹(B)` gives `k`, `δ` and a holomorphic family
   `T : Λ → Pk → (Fin k → F)` on `ball 0 δ`. The induction hypothesis for `Pk` and
   `Fin k → F` at `0` gives an open `V' ⊆ ball 0 δ` containing `0` and a finite `s₀`
   such that on `V'` the `T μ` with `μ ∈ s₀` span.
6. Take `V = B ∩ π⁻¹(V' × ball 0 ρ)` (open, contains `x₀`) and `s = s₀ ∪ s₁`. For `z ∈ V`: if
   `h z ≠ 0`, step 1 applies. If `h z = 0`, then `π z = (w, t)` is a zero of `H` with
   `w ∈ V'` and `|t| < ρ`, so step 5 gives that the `a μ z = b μ (w, t)` with `μ ∈ s₀` span.

## Provenance

Internal. The statement and its proof are internal derivations, used for the analyticity of
the non-uniqueness locus in Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), Theorem 3.3(1) (target
`Langlands.Analysis.Meromorphic.MeromorphicContinuationAnalyticComplementStatement`). The
local description by holomorphic determinants (Cramer's rule) comes from the proof in
Appendix A of that paper (p. 230). The Library's
`Langlands/Analysis/Meromorphic/ContinuationPrincipleStatement.md` (section "Why two parts")
explains that the complement of the unique-solution locus is then locally the common zero set
of a possibly infinite family of holomorphic functions, and that finitely many suffice by the
Noetherian property of rings of convergent power series. `exists_finset_zero_iff` supplies
this finiteness by a different, internal route that avoids Weierstrass preparation and
Noetherianity. It inducts on the dimension, using the rank witness, power sums of zeros by the
argument principle, and Lagrange interpolation, all proved from Mathlib in the modules named
above.
