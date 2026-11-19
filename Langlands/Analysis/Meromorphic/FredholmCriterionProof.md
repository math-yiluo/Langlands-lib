# Proof of Fredholm's criterion for local finite type

Module `Langlands.Analysis.Meromorphic.FredholmCriterionProof` proves the
published statements of `Langlands.Analysis.Meromorphic.FredholmCriterionStatement`,
unchanged, with their four universes `uE, uM, uB, uC`:

- `Langlands.Analysis.Meromorphic.fredholmCriterion :
  FredholmCriterionStatement.{uE, uM, uB, uC}`. This is the Lemma (Fredholm's
  criterion).
- `Langlands.Analysis.Meromorphic.hilbertFredholmCriterion :
  HilbertFredholmCriterionStatement.{uE, uM, uB, uC}`. This is Corollary 3.4.
- `Langlands.Analysis.Meromorphic.fredholmFiniteType :
  FredholmFiniteTypeStatement.{uE, uM, uB, uC}`. This is their conjunction,
  the target of the task.

It uses the helper modules `Langlands.Analysis.Meromorphic.RieszFredholm`
(identity plus compact is Fredholm, hence left invertible modulo finite rank)
and `Langlands.Analysis.Meromorphic.WeakHolomorphy` (weakly holomorphic
operator families in a chart: norm Lipschitz bounds, and weak holomorphy of
the inverse family). Only the standard axioms `propext`, `Classical.choice`
and `Quot.sound` are used.

## Helpers in namespace `FredholmCriterion`

- `exists_injective_range_eq`: a finite-dimensional subspace `W` of `B` lies
  in the range of an injective operator `ι : ℂⁿ →L[ℂ] B`, with
  `n = dim W`. It is the inclusion of `W` composed with the coordinate
  isomorphism of a basis (`Module.finBasis`). Continuity is automatic on the
  finite-dimensional domain.
- `exists_finiteType_euclidean` is Fredholm's criterion in a chart. Its
  setting is:
  - `E` is finite-dimensional, `T ⊆ E` is open, and `B` is a Banach space;
  - `μ : E → B →L[ℂ] C` is weakly holomorphic on `T`, that is, every
    `z ↦ φ (μ z v)` is complex differentiable on `T`;
  - `z₀ ∈ T`, and `D ∘ μ z₀ - 1` is compact for some `D`.

  Then there are an open `T' ⊆ T` containing `z₀`, an `n` and a family
  `ℓ : E → ℂⁿ →L[ℂ] B` with these properties: `ℓ` is weakly holomorphic on
  `T'`; each `ℓ z`, `z ∈ T'`, is injective; and `μ z v = 0` implies
  `v ∈ range (ℓ z)` for `z ∈ T'`. The proof follows Bernstein–Lapid:
  1. `RieszFredholm.exists_leftInverse_mod_finiteRank` gives `G` and `F` with
     `G ∘ μ z₀ = 1 - F`, where `F` has finite-dimensional range.
  2. Put `X z = 1 + G ∘ (μ z - μ z₀)`. Then `X` is weakly holomorphic on `T`,
     since `φ (X z v) = φ v + (φ ∘ G)(μ z v) - (φ ∘ G)(μ z₀ v)`. It is
     norm-continuous on `T` (`WeakHolomorphy.continuousAt_of_weak`), and
     `X z₀ = 1`.
  3. `T' = T ∩ X⁻¹(units)` is open, because the units of the Banach algebra
     `B →L[ℂ] B` form an open set (`Units.isOpen`), and it contains `z₀`.
  4. Let `ι : ℂⁿ → B` be injective with `range F ⊆ range ι`
     (`exists_injective_range_eq`), and set
     `ℓ z = Ring.inverse (X z) ∘ ι`. On `T'` this is `(X z)⁻¹ ∘ ι`.
     - Weak holomorphy of `ℓ` on `T'` is
       `WeakHolomorphy.differentiableOn_inverse_apply` applied to the vectors
       `ι c`.
     - Each `ℓ z` is injective, as the composition of an invertible operator
       with `ι`.
  5. If `μ z v = 0`, then `X z v = v - G (μ z₀ v) = v - (v - F v) = F v`. So
     `v = (X z)⁻¹ (F v)`, and `F v = ι c` for some `c`; hence `v = ℓ z c`.

## `fredholmCriterion` (chart transfer)

Let `e = extChartAt 𝓘(ℂ, E) s₀` be the extended chart at `s₀`. Its target is
open, since the model `𝓘(ℂ, E)` has no boundary (`isOpen_extChartAt_target`).

Weak holomorphy of `μ` on `M` (`IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) μ univ`)
transfers to `z ↦ μ (e.symm z)` on `e.target`. To see this, compose with the
smooth inverse chart (`mdifferentiableOn_extChartAt_symm`, which uses
`IsManifold 𝓘(ℂ, E) 1 M`). Then convert manifold differentiability between
vector spaces into `DifferentiableOn` (`MDifferentiableOn.differentiableOn`).
Since `e.symm (e s₀) = s₀`, the compactness hypothesis holds at `z₀ = e s₀`.

`exists_finiteType_euclidean` gives `T'`, `n` and `ℓ`. The required data on
`M` are:

- `U = e.source ∩ e⁻¹ T'`, which is open (`isOpen_extChartAt_preimage'`) and
  contains `s₀`;
- the family `s ↦ ℓ (e s)`.

Its holomorphy on `U` follows by composing the Euclidean differentiability
(`DifferentiableOn.mdifferentiableOn`) with the chart, which is differentiable
on its source (`mdifferentiableOn_extChartAt`). Injectivity transfers directly.
For the kernel inclusion, `μ (e.symm (e s)) = μ s` for `s ∈ e.source`. Hence
`{v | μ s v = 0} ⊆ range (ℓ (e s))` for `s ∈ U`, which is
`IsFiniteTypeOn 𝓘(ℂ, E) (fun s => {v | μ s v = 0}) U`.

## `hilbertFredholmCriterion` (Corollary 3.4)

Let `μ₀ = μ s₀`, a topological embedding between complex Hilbert spaces.

1. `μ₀` is antilipschitz (`ContinuousLinearMap.antilipschitz_of_isEmbedding`).
   So its range is closed (`AntilipschitzWith.isClosed_range`), and it is
   injective.
2. The closed range is complete. So it has an orthogonal projection, and the
   orthogonal complement is a closed complement
   (`Submodule.isTopCompl_orthogonal`, `IsTopCompl.closedComplemented`).
3. Hence `μ₀` has a continuous left inverse `L`
   (`ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range`):
   `L ∘ μ₀ = 1`.
4. For the family `μ - ν`,
   `L ∘ (μ - ν) s₀ - 1 = -(L ∘ ν s₀)`, which is compact because `ν s₀` is.
   The family `μ - ν` is holomorphic, since
   `φ ((μ s - ν s) v) = φ (μ s v) - φ (ν s v)`.
5. `fredholmCriterion` applied to `μ - ν` and `D = L` gives `U`, `n` and `ℓ`.
   Since `(μ s - ν s) v = 0 ↔ μ s v = ν s v` (`sub_eq_zero`), these witness
   `IsFiniteTypeOn 𝓘(ℂ, E) (fun s => {v | μ s v = ν s v}) U`.

## Provenance and differences from the source

Source: J. Bernstein and E. Lapid, *On the meromorphic continuation of
Eisenstein series*, J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`. §3.4 is on
pp.194–195 of the journal PDF (arXiv TeX lines 742–785): the Lemma with its
proof, and Corollary 3.4 with the one-line justification "every strict
embedding of Hilbertian spaces is left invertible".

The Euclidean argument follows the source's proof:

- left invertibility modulo finite rank;
- `μ_s = X_s - F` with `X_s` invertible near `s₀`;
- `ker (X_s - F) ⊆ X_s⁻¹ (range F)`.

The source composes with `D` and says "we may assume `B = C`". The Lean proof
instead keeps `μ` and puts `G` inside `X z`. The source takes for granted the
facts proved in the helper modules:

- `1 - K` is Fredholm;
- weak holomorphy gives norm continuity;
- `s ↦ X_s⁻¹` is holomorphic.

The Lean proof works in a single chart at `s₀` and shrinks to an open subset
of the chart domain. For the corollary, the source only asserts that a strict
embedding of Hilbertian spaces is left invertible. The Lean proof constructs
the left inverse from the closed range and its orthogonal complement.
