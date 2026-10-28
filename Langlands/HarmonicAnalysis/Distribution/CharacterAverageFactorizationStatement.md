# Unique factorization of twisted product distributions

`Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationStatement.{uG, uY}`
is the following proposition. This module defines it and does not prove it. A
separate proof task follows publication.

## Statement

Let `G : Type uG` and `Y : Type uY`, in two independent arbitrary universes
`uG` and `uY`. These are the only parameters of the definition. Assume the
following about `G`:

- `Group G`, `TopologicalSpace G`, `IsTopologicalGroup G`;
- `T2Space G` (Hausdorff), `LocallyCompactSpace G`;
- `NonarchimedeanGroup G` (the open subgroups form a neighbourhood basis of `1`);
- `MeasurableSpace G` with `BorelSpace G`, so the σ-algebra on `G` is the
  Borel σ-algebra of its topology.

Assume the following about `Y`:

- `TopologicalSpace Y`, `T2Space Y`, `LocallyCompactSpace Y`;
- `TotallyDisconnectedSpace Y`.

`Y` carries no group, measure or countability structure.

Let `χ : ContinuousMonoidHom G ℂˣ` be any continuous character. Let
`μ : Measure G` satisfy:

- `[μ.IsHaarMeasure]`, so `μ` is a left Haar measure;
- `[SFinite μ]`;
- `[μ.IsMulRightInvariant]`, so `μ` is also right invariant.

Let `D : Distribution (G × (Y × G))` be any algebraic distribution. The single
premise on `D` is the following. For all `a b : G` and every
`α : SchwartzBruhat (G × (Y × G))`, let

    e = (Homeomorph.mulLeft a).prodCongr
          ((Homeomorph.refl Y).prodCongr (Homeomorph.mulRight b)).

Then

    D (Hecke.TestFunction.pullback e α) = ((χ a : ℂ) * (χ b : ℂ)) * D α.

The conclusion is

    ∃! τ : Distribution Y, Distribution.characterAverageDual χ μ τ = D.

In words, there is exactly one algebraic distribution `τ` on `Y` such that

    D α = τ (SchwartzBruhat.characterAverage χ μ α)   for every α.

All of `G`, `Y`, their instances, `χ`, `μ` and `D` are universally quantified
inside the proposition. The hypotheses on `D` consist of the displayed
equation alone.

## Exact meaning of the imported objects

The module imports only `Langlands.HarmonicAnalysis.Distribution.CharacterAverage`,
unchanged.

- `SchwartzBruhat X` (from `Langlands.HarmonicAnalysis.Basic`) is the complex
  vector space of functions `X → ℂ` that are locally constant and have compact
  support.
- `Distribution X` (from `Langlands.HarmonicAnalysis.Distribution.Basic`) is
  `Module.Dual ℂ (SchwartzBruhat X)`. This is the algebraic dual: every complex
  linear functional, with no topology, continuity or boundedness condition.
  Neither `D` nor `τ` is assumed continuous, bounded or positive.
- `Hecke.TestFunction.pullback e` is the complex linear equivalence
  `f ↦ f ∘ e`. Its evaluation law is `Hecke.TestFunction.pullback_apply`.
- `Homeomorph.mulLeft a` is `g ↦ a * g` and `Homeomorph.mulRight b` is
  `g ↦ g * b`. `Homeomorph.prodCongr` acts componentwise. The point of
  `G × (Y × G)` is right-associated as `(g₁, (y, g₂))`. Hence

      pullback e α (g₁, (y, g₂)) = α (a * g₁, (y, g₂ * b)).

  The left factor is translated on the left and the right factor on the right.
  `Y` is not moved.
- `SchwartzBruhat.characterAverage χ μ` is the published complex linear map
  `SchwartzBruhat (G × (Y × G)) →ₗ[ℂ] SchwartzBruhat Y` with

      characterAverage χ μ α y =
        ∫ z : G × G, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ).

  The inverse of both character factors stays in the integrand.
- `Distribution.characterAverageDual χ μ` is the dual map of `characterAverage`,
  i.e. `Distribution Y →ₗ[ℂ] Distribution (G × (Y × G))` with

      characterAverageDual χ μ τ α = τ (characterAverage χ μ α)

  (`Distribution.characterAverageDual_apply`).

`characterAverage` requires `[OpensMeasurableSpace G]`, `[SFinite μ]` and
`[IsFiniteMeasureOnCompacts μ]`. Here `BorelSpace G` supplies the first and
`IsHaarMeasure` the third.

## The sign convention

The premise has the two positive factors `χ a` and `χ b`, multiplied in the
order `(χ a : ℂ) * (χ b : ℂ)`, and then times `D α`. This is the sign that
every distribution of the form `characterAverageDual χ μ τ` satisfies:

    characterAverage χ μ (pullback e α) y
      = ∫∫ α (a * z₁, (y, z₂ * b)) * (χ z₁)⁻¹ * (χ z₂)⁻¹ dμ(z₁) dμ(z₂)
      = ∫∫ α (w₁, (y, w₂)) * (χ (a⁻¹ * w₁))⁻¹ * (χ (w₂ * b⁻¹))⁻¹ dμ(w₁) dμ(w₂)
      = χ a * χ b * characterAverage χ μ α y.

The second line substitutes `w₁ = a * z₁`, which preserves `μ` by left
invariance. It also substitutes `w₂ = z₂ * b`, which preserves `μ` by right
invariance. Applying `τ` gives the premise for `D = characterAverageDual χ μ τ`.
So the proposition says that the converse holds and that `τ` is unique. This
computation explains the sign. Neither this module nor its import proves it.
The translation covariance of the average is a separate statement in a sibling
task, and this module does not assume it.

## Role of each hypothesis

- `IsMulRightInvariant μ` is used for the right translation in the last
  factor. A left Haar measure need not be right invariant. Together the two
  invariances make `G` unimodular, as Shalika's unipotent group is.
- `SFinite μ` is needed by the published average. Mathlib's `Measure.prod`
  is controlled only for an s-finite second factor (see the
  `CharacterAverage` Markdown). In the p-adic application it is discharged
  separately.
- `NonarchimedeanGroup G` and local compactness give compact open subgroups
  of `G` and an open kernel of `χ`. Then `χ` is locally constant, which the
  intended proof needs. Its open kernel is
  `Langlands.isOpen_ker_of_continuous_complex_character`. Neither unitarity
  nor local constancy of `χ` is a separate premise.
- The Hausdorff, locally compact and totally disconnected hypotheses on `Y`
  give a basis of compact open sets. The intended proof uses it to write
  test functions on the product as finite sums of rectangles.
- No σ-compactness, second countability or other countability hypothesis is
  imposed on `G` or `Y`.
- No representation, surjectivity, factorization, cell-descent, support or
  covariance premise is added, and no structure field encodes the conclusion.
  The proposition applies to every `D` satisfying the displayed equation.

The degenerate cases are included. If `Y` is empty, both distribution spaces
are zero and the unique `τ` is `0`. If `G` is trivial, `μ` is a positive
multiple of the Dirac mass, and the statement says that `characterAverageDual`
is bijective.

## Intended proof route (not proved here)

A later proof task is expected to argue with finite compact-open/tensor
decompositions. An algebraic `D` cannot be interchanged with an integral, so
the argument stays finite.

1. **Untwisting.** `χ` has an open kernel, so multiplying a test function by
   `(g₁, (y, g₂)) ↦ χ g₁ * χ g₂` gives another test function. Put
   `D' α = D (α * (χ ⊗ 1 ⊗ χ))`. The premise then makes `D'` invariant under
   left translation of `g₁` and right translation of `g₂`.
2. **Rectangles.** Let `α` be a test function on `G × (Y × G)`. There is a
   compact open subgroup `K` of `G` inside `ker χ` such that `α` is a finite
   sum of rectangles `1_{xK} ⊗ β ⊗ 1_{Kx'}` with `β` a test function on `Y`.
   This uses compact open sets in `Y` and the open subgroups of `G`.
3. **Uniqueness of invariant functionals on the outer factors.** By invariance,
   `D' (1_{xK} ⊗ β ⊗ 1_{Kx'}) = D' (1_K ⊗ β ⊗ 1_K)`. Let `τ β` be
   `μ(K)⁻² * D (1_K ⊗ β ⊗ 1_K)`, where `χ` is trivial on `K`. Refining `K` by
   coset decomposition shows that this does not depend on `K`. Here
   `0 < μ(K) < ∞` because `K` is compact and open.
4. **Normalized tensor section.** The average of the rectangle `1_K ⊗ β ⊗ 1_K`,
   with `K ⊆ ker χ`, is `μ(K)² β`. So `β ↦ μ(K)⁻² (1_K ⊗ β ⊗ 1_K)` is a linear
   section of `characterAverage χ μ`. This gives surjectivity of the average,
   hence uniqueness of `τ`, and step 3 gives `D = characterAverageDual χ μ τ`.

This is a plan only. Nothing in this module proves any step of it.
`Langlands.HarmonicAnalysis.RowTensorDecompositionProof` contains related
finite tensor work. Its private helpers are not public interfaces, and this
module does not use them.

## Canonical upper-unipotent/diagonal specialization

The proposition is meant for Shalika's `U × H × U`. Fix a prime `p` with
`[Fact p.Prime]`, a field `F : PadicField.{uF} p` in any universe `uF`, and any
`n : ℕ`, including `n = 0`. Instantiate `CharacterAverageFactorizationStatement.{uF, uF}`
with the following data:

- `G = upperUnipotent (n + 1) F.Carrier`, with the canonical topology
  (`letI := F.canonicalNormedField`) and `letI := borel G` together with
  `BorelSpace G` by `⟨rfl⟩`, as in the published `standardCharacterAverage`;
- `Y = Fin (n + 1) → F.Carrierˣ`, the parameter space of the diagonal torus
  `H`, with the product topology of the units topology;
- `χ = standardCharacterContinuous ψ n` for any
  `ψ : UnitaryAdditiveCharacter F.Carrier`;
- `μ` any Haar measure on `G` that is s-finite and right invariant.

The group instances on `G` come from the published
`PadicField.TopologicalData.upperUnipotentTopologicalGroup`,
`upperUnipotentT2Space`, `upperUnipotentLocallyCompactSpace` and
`upperUnipotentNonarchimedean`, applied to `F.canonicalTopologicalData` and
`n + 1`. For `Y`:

- `F.Carrierˣ` is locally compact because `Units.val` is an open embedding
  of `F.Carrierˣ` into the complete field `F.Carrier`
  (`Units.isOpenEmbedding_val`), and `F.Carrier` is proper as a
  finite-dimensional normed space over `Padic p`;
- `F.Carrierˣ` is totally disconnected through the same embedding, because
  the ultrametric field `F.Carrier` is totally separated;
- Mathlib's finite-product instances give the same properties for
  `Fin (n + 1) → F.Carrierˣ`.

The author checked by compilation, in a private draft that is not part of
this submission, that the proposition yields the conclusion
`∃! τ, characterAverageDual (standardCharacterContinuous ψ n) μ τ = D` for
every such `F`, `n`, `ψ`, `μ` and every `D` satisfying the premise with
`standardCharacter ψ n a` and `standardCharacter ψ n b`. For `n = 0` the
character is trivial and `upperUnipotent 1 F.Carrier` is the trivial group.
This module contains no specialization declaration.

## Source correspondence

J. A. Shalika, *The multiplicity one theorem for GLn*, Ann. of Math. (2)
**100** (1974), 171–193, registered as `shalika-1974-multiplicity-one`.
The central file is
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`,
SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`,
re-verified. Proposition 1.12 is on printed p.177, one-based PDF page 8. It
says the following. Let `T*` be a distribution on `M₁ = U × H × U` with
`T*(L_{u₁⁻¹} R_{u₂} α) = χ(u₁u₂) T*(α)` for `u₁, u₂ ∈ U` and
`α ∈ C_c^∞(M₁)`. The inverse on `u₁` is printed as a superscript and is
visible in the page image; the PDF's extracted text loses it. Define

    β_α(h) = ∫ α(u₁, h, u₂) χ̄(u₁u₂) du₁ du₂.

Then `α ↦ β_α` is surjective, and there is a unique distribution `τ` on `H`
with `T*(α) = τ(β_α)`. Shalika omits the proof, saying it is similar to
Lemma 21 of his reference [11]. No errata for this source is recorded in the project's
literature pointers or notes.

The correspondence is as follows:

- `G`, `Y`, `μ` and `D` play the roles of `U`, `H`, Haar measure on `U`, and
  `T*`.
- `characterAverage χ μ α` is `β_α`. `χ̄(u₁u₂)` corresponds to the inverse
  weight `((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹`, which agrees with it for unitary
  `χ`.
- The premise is Shalika's bi-equivariance premise, written with the
  Library's pullback. Shalika defines the translation operators on printed
  p.174 (PDF page 5) as `(L_x f)(y) = f(x⁻¹y)` and `(R_x f)(y) = f(yx)`. On
  p.177 he lets `U × U` act on `M₁` by `(u₁, u₂)∘m = u₁ m u₂⁻¹` and on
  functions by duality, so `L` translates the first `U` coordinate and `R`
  the last one. Hence `(L_{a⁻¹} f)(y) = f(a y)` and

      (L_{a⁻¹} R_b α)(g₁, h, g₂) = α(a g₁, h, g₂ b),

  which is `pullback e α (g₁, (y, g₂))` above with `h = y`. Shalika's factor
  `χ(u₁u₂)` with `u₁ = a`, `u₂ = b` is `χ(a)χ(b)`, the Lean factor
  `(χ a : ℂ) * (χ b : ℂ)`. So the source premise and the Lean premise
  agree. This is also the sign forced by the conclusion `T*(α) = τ(β_α)`,
  by the computation in "The sign convention" above, and it is the premise
  the task specifies. Replacing `L_{a⁻¹}` by `L_a` would change the first
  factor to `χ(a)⁻¹`.
- The conclusion is the "moreover" part of Proposition 1.12: existence and
  uniqueness of `τ`.

The setting, unlike the premise, is an internal extension of Shalika's. Here
`G` is any Hausdorff, locally compact, nonarchimedean group with a two-sided
Haar measure, `Y` any Hausdorff, locally compact, totally disconnected space,
and `χ` any continuous character, not necessarily unitary. For
non-archimedean `k`, Shalika's `C_c^∞` consists of locally constant
functions of compact support (printed p.174), which is `SchwartzBruhat`.
The Lean statement takes distributions to be all complex linear functionals
on that space and imposes no continuity condition.

## What this module does not prove

The module defines the proposition and proves nothing about it. In
particular it does not prove the factorization itself. Nor does it prove
surjectivity of `characterAverage`, which is stated in a separate sibling
task, or translation covariance of the average, also stated separately.
Cell descent, support on a compatible locus (Shalika's Proposition 1.13) and
Shalika invariance of Whittaker distributions are not part of it either.
None of these is assumed as a premise. No imported published pair is changed.
