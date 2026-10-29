# Proof of unique factorization of twisted product distributions

This module proves
`Langlands.HarmonicAnalysis.Distribution.characterAverageFactorization.{uG, uY}`.
Its type is exactly the published proposition
`Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationStatement.{uG, uY}`
from `Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationStatement`.
The two universes stay arbitrary and independent. The statement module and its
imports are unchanged.

So for every `G`, `Y`, `χ`, `μ` and every algebraic distribution
`D : Distribution (G × (Y × G))` satisfying the published premise

    D (Hecke.TestFunction.pullback e α) = ((χ a : ℂ) * (χ b : ℂ)) * D α,
    e (g₁, (y, g₂)) = (a * g₁, (y, g₂ * b)),

there is exactly one algebraic distribution `τ` on `Y` with
`Distribution.characterAverageDual χ μ τ = D`, i.e.
`D α = τ (SchwartzBruhat.characterAverage χ μ α)` for every test function `α`.
The average is the published one, with the inverse of both character factors
in the integrand. No continuity of `D` or `τ` is used. The argument applies `D`
only to finite sums of explicit test functions (see "Finiteness" below).

## Imports

- `Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationStatement`:
  the target proposition, and through it the published `characterAverage` and
  `characterAverageDual` (with `characterAverageDual_apply`).
- `Langlands.HarmonicAnalysis.Distribution.CharacterAverageCovarianceProof`:
  the published theorem
  `Langlands.HarmonicAnalysis.SchwartzBruhat.characterAverageCovariance`, a
  proof of the published `CharacterAverageCovarianceStatement`. For a measure
  that is s-finite, finite on compact sets, and left and right invariant,

      characterAverage χ μ (pullback e α) = ((χ a : ℂ) * (χ b : ℂ)) • characterAverage χ μ α.

  It is used as a previously proved lemma. It is not a premise of the target.
- `Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveProof`:
  the published public helpers in the namespace
  `Langlands.HarmonicAnalysis.SchwartzBruhat`:
  - `tripleTensor φ f ψ`, the test function `(g₁, (y, g₂)) ↦ φ g₁ * f y * ψ g₂`;
  - `normalizedCharacteristic_apply`: the published
    `Hecke.HeckeAlgebra.normalizedIndicator μ K hK` takes the value
    `((μ.real K : ℂ))⁻¹` on `K` and `0` off `K`;
  - `characterAverage_tripleTensor_normalizedCharacteristic`: if `μ` is an
    s-finite Haar measure, `K` a compact open subgroup and `χ` is trivial on
    `K`, then the average of `tripleTensor n_K f n_K` is `f`, where `n_K` is the
    normalized indicator of `K`.

  Its imports also supply `Langlands.isOpen_ker_of_continuous_complex_character`
  (a continuous character `G →* ℂˣ` of a nonarchimedean group has open kernel),
  `Langlands.compactOpenSubgroupBasis` (in a nonarchimedean, weakly locally
  compact group every neighbourhood of `1` contains a compact open subgroup)
  and `Hecke.HeckeAlgebra.compactOpen_complex_mass_ne_zero`
  (`(μ.real K : ℂ) ≠ 0` for a Haar measure and a compact open subgroup `K`).

No other published proposition is assumed, and no surjectivity, factorization
or invariance theorem enters as a hypothesis.

## Notation

For a compact open subgroup `K` of `G` write `c_K = (μ.real K : ℂ)`, which is
nonzero, `n_K = c_K⁻¹ 1_K`, and `A = SchwartzBruhat.characterAverage χ μ`.
The translation of the premise is written `T_{a,b} = pullback (translation Y a b)`,
so `T_{a,b} α (g₁, (y, g₂)) = α (a * g₁, (y, g₂ * b))`.

## Helper declarations

All helpers are in the namespace
`Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorization`.
They are elementary finite compact-open and normalization facts specific to
this proof.

- `sum_apply`: a finite sum of test functions is evaluated pointwise.
- `translation Y a b`: an `abbrev` for the homeomorphism
  `(Homeomorph.mulLeft a).prodCongr ((Homeomorph.refl Y).prodCongr (Homeomorph.mulRight b))`
  of the premise, so the premise applies to it verbatim.
- `IsSmooth K α`: for all `k, k' ∈ K` and all points,
  `α (g₁ * k, (y, k' * g₂)) = α (g₁, (y, g₂))`. So `α` is invariant under right
  translation of the first coordinate and left translation of the last
  coordinate by `K`, the sides opposite to the premise.
- `exists_isSmooth`: for every test function `α` and every neighbourhood `U`
  of `1` there is a compact open subgroup `K ⊆ U` for which `α` is smooth.
  Proof: let `C` be the compact support of `α`. For each `q ∈ C`, the two maps
  `(w, q') ↦ α (q'.1 * w.1, (q'.2.1, w.2 * q'.2.2))` and `(w, q') ↦ α q'` on
  `(G × G) × (G × (Y × G))` are locally constant and agree at `((1, 1), q)`, so
  they agree near it. The tube lemma
  (`IsCompact.eventually_forall_of_forall_eventually`) gives one neighbourhood
  `W` of `(1, 1)` such that `α (q.1 * w.1, (q.2.1, w.2 * q.2.2)) = α q` for all
  `w ∈ W` and `q ∈ C`. `W` contains a product `u ×ˢ v`
  (`mem_nhds_prod_iff`), and `compactOpenSubgroupBasis` gives a compact open
  `K ⊆ U ∩ u ∩ v`. Points outside `C` are handled with inverses: if
  `α (g₁, (y, g₂)) = 0` but `α (g₁ * k, (y, k' * g₂)) ≠ 0`, applying the
  identity at the second point with `k⁻¹, k'⁻¹` gives a contradiction.
- `middle α x`, for `x : G × G`: the test function `y ↦ α (x.1, (y, x.2))` on `Y`.
  It is locally constant by composition. Its support is closed, being the
  preimage of the clopen support of `α`, and lies in the compact projection of
  the support of `α` to `Y`, so `HasCompactSupport.intro'` applies.
  `middle_apply` is its evaluation law.
- `box K x = {p : G × G | x.1⁻¹ * p.1 ∈ K ∧ p.2 * x.2⁻¹ ∈ K}`, the set
  `x.1 K × K x.2`. `box_mem_nhds`: it is an open neighbourhood of `x`.
  `box_eq_of_mem`: two boxes with a common point are equal (group identities
  in `K`).
- `normalizedSection μ K hK : SchwartzBruhat Y →ₗ[ℂ] SchwartzBruhat (G × (Y × G))`,
  the linear map `f ↦ tripleTensor n_K f n_K`, written `S_K` below. Linearity
  is checked pointwise by `ring`. `normalizedSection_apply`:

      S_K f (g₁, (y, g₂)) = 1_K(g₁) c_K⁻¹ * f y * 1_K(g₂) c_K⁻¹.

- `characterAverage_normalizedSection`: if `χ` is trivial on `K` then
  `A (S_K f) = f`. This is the published
  `characterAverage_tripleTensor_normalizedCharacteristic`.
- `isSmooth_normalizedSection`: if `L ≤ K` then `S_K f` is smooth for `L`,
  because `g₁ * k ∈ K ↔ g₁ ∈ K` and `k' * g₂ ∈ K ↔ g₂ ∈ K` for `k, k' ∈ L`.
- `term_apply`: if `α` is smooth for `K` and `x : G × G`, then

      (c_K ^ 2 • T_{x.1⁻¹, x.2⁻¹} (S_K (middle α x))) (g₁, (y, g₂))
        = 1_{box K x}(g₁, g₂) * α (g₁, (y, g₂)).

  The left side is `c_K² * S_K (middle α x) (x.1⁻¹ * g₁, (y, g₂ * x.2⁻¹))`. If
  `(g₁, g₂)` is in the box, put `k = x.1⁻¹ * g₁` and `k' = g₂ * x.2⁻¹` in `K`.
  Smoothness gives `α (x.1 * k, (y, k' * x.2)) = α (x.1, (y, x.2))`, that is
  `α (g₁, (y, g₂)) = middle α x y`, and `c_K² * c_K⁻¹ * c_K⁻¹ = 1` since
  `c_K ≠ 0`. Otherwise one indicator factor vanishes.
- `exists_eq_sum`: if `α` is smooth for `K`, there is a finite set
  `u ⊆ G × G` with

      α = ∑ x ∈ u, c_K ^ 2 • T_{x.1⁻¹, x.2⁻¹} (S_K (middle α x)).

  The projection `P` of the support of `α` to the outer coordinates `(g₁, g₂)`
  is compact. The boxes `box K x` with `x ∈ P` cover it, so finitely many,
  indexed by a finite `t`, already do (`IsCompact.elim_nhds_subcover`).
  `Finset.exists_subset_injOn_image_eq_of_surjOn` picks `u ⊆ t` on which
  `x ↦ box K x` is injective with the same set of boxes. The boxes indexed by
  `u` are therefore pairwise distinct, hence pairwise disjoint by
  `box_eq_of_mem`, and still cover `P`. The identity is checked pointwise with
  `term_apply`: where `α` vanishes every term vanishes, and otherwise `(g₁, g₂)`
  lies in `P` and in exactly one box of `u`, whose term is `α (g₁, (y, g₂))`.
- `eq_normalizedSection_of_isSmooth`: assume the premise on `D`, `χ` trivial
  on the compact open subgroup `K`, and `α` smooth for `K`. Then
  `D α = D (S_K (A α))`. Proof: let `Δ = D - D ∘ S_K ∘ A`, a linear functional.
  For every translate `T_{a,b} (S_K f)`, covariance and the section identity
  give `A (T_{a,b} (S_K f)) = χ(a) χ(b) • f`, so

      D (S_K (A (T_{a,b} (S_K f)))) = χ(a) χ(b) * D (S_K f) = D (T_{a,b} (S_K f))

  by linearity of `D ∘ S_K` and the premise. So `Δ` vanishes on each scaled
  term of `exists_eq_sum`, and by linearity over that finite sum, `Δ α = 0`.
  Covariance needs left and right invariance, s-finiteness and finiteness on
  compacts of `μ`; `IsHaarMeasure` supplies left invariance and finiteness on
  compacts, and the statement supplies the rest.

## Proof of the theorem

Fix all data and the premise `hD`.

1. **A subgroup in the kernel.** The kernel of `χ` is open
   (`isOpen_ker_of_continuous_complex_character`). `compactOpenSubgroupBasis`
   (local compactness gives weak local compactness) yields a compact open
   subgroup `K₀` inside it, so `χ g = 1` for `g ∈ K₀`.
2. **Independence of the subgroup.** For a compact open `K ≤ K₀` and
   `f : SchwartzBruhat Y`, `D (S_K f) = D (S_{K₀} f)`. Indeed `S_{K₀} f` is
   smooth for `K` (`isSmooth_normalizedSection`), and `χ` is trivial on `K`, so
   `eq_normalizedSection_of_isSmooth` gives
   `D (S_{K₀} f) = D (S_K (A (S_{K₀} f))) = D (S_K f)`.
3. **Existence.** Put `τ = D ∘ S_{K₀}`, a linear functional on
   `SchwartzBruhat Y`. For a test function `α`, `exists_isSmooth` with
   `U = K₀` gives a compact open `K ⊆ K₀` for which `α` is smooth. Then

       characterAverageDual χ μ τ α = D (S_{K₀} (A α)) = D (S_K (A α)) = D α

   by `characterAverageDual_apply`, step 2 and `eq_normalizedSection_of_isSmooth`.
4. **Uniqueness.** If `characterAverageDual χ μ τ' = D`, then for every `f`,
   `τ' f = τ' (A (S_{K₀} f)) = D (S_{K₀} f) = τ f`, using `A (S_{K₀} f) = f`.

## Normalization

`τ β = D (S_{K₀} β) = c_{K₀}⁻² * D (1_{K₀} ⊗ β ⊗ 1_{K₀})`, the normalization
named in the statement's Markdown. The factor `c_K²` in `exists_eq_sum`
cancels the two factors `c_K⁻¹` of `S_K`. Step 2 shows that the value does not
depend on the compact open subgroup `K ≤ K₀`. It is proved by the comparison
lemma for `K`, not by an explicit coset decomposition of `K₀`, although
`exists_eq_sum` applied to `S_{K₀} f` is exactly such a decomposition.

## Finiteness and the algebraic dual

`D` and `τ` are arbitrary complex linear functionals. The proof uses only:

- the premise on `D`, applied to individual translates;
- linearity of `D` and `Δ` over the finite sum of `exists_eq_sum`, via `map_sum`
  and `map_smul`;
- identities between test functions: `exists_eq_sum`, the section identity
  `A (S_K f) = f` and covariance of `A`.

The integrals inside `A` occur only in the published lemmas, which compare test
functions on `Y`; no distribution is interchanged with an integral.

## Degenerate cases

No case split is needed.

- If `Y` is empty, every test function is zero. The finite sum of
  `exists_eq_sum` is still produced by the general argument, and `τ` is the
  zero functional.
- If the support of `α` is empty, the projected support is empty, `u` can be
  empty, and `α = 0` is the empty sum.
- If `G` is trivial, `K₀ = G` and every box is all of `G × G`. The argument is
  the same.
- If `χ` is trivial, step 1 still applies, with kernel `G`.

## Use of the hypotheses

The proof uses `[Group G] [TopologicalSpace G] [IsTopologicalGroup G]
[LocallyCompactSpace G] [NonarchimedeanGroup G] [MeasurableSpace G]
[BorelSpace G] [TopologicalSpace Y]` and `[μ.IsHaarMeasure] [SFinite μ]
[μ.IsMulRightInvariant]`. Local compactness and the nonarchimedean property
give the compact open subgroups. The Borel structure and the measure
hypotheses are those of the published average and of the published covariance
and section lemmas. `[T2Space G]`, `[T2Space Y]`, `[LocallyCompactSpace Y]` and
`[TotallyDisconnectedSpace Y]` are not needed by this argument: `Y` is never
decomposed, only the outer coordinates are. They remain part of the published
statement, which is unchanged.

## Source correspondence and route

The proposition is the distribution part of Proposition 1.12 of J. A. Shalika,
*The multiplicity one theorem for GLn*, Ann. of Math. (2) **100** (1974),
171–193 (printed p.177), as recorded in the statement's Markdown. Shalika omits
the proof, referring to Lemma 21 of his reference [11]. The implemented route
is internal. It follows the finite plan of the statement's Markdown with two
changes: instead of untwisting `D` by `χ ⊗ 1 ⊗ χ`, it compares `D` with
`D ∘ S_K ∘ A` directly on translates, using covariance of the average; and the
rectangles are the translates `T_{x.1⁻¹, x.2⁻¹} (S_K (middle α x))`, whose middle
factors are slices of `α`, so `Y` needs no compact open decomposition.
Uniqueness uses the explicit section `S_{K₀}` rather than surjectivity of `A`
as a separate theorem.
