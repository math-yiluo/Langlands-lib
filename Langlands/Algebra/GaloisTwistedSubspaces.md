# Descent of twisted-stable subspaces of a matrix algebra

This internal module continues `Algebra/GaloisTwistedMatrix`. Let `K/k` be a
Galois extension, possibly infinite (`IsGalois k K`). Let `P σ` be invertible
matrices, and let `A ⊆ M_n(K)` be a `k`-subalgebra of twisted-fixed matrices
whose `K`-span is `M_n(K)`, so that `A` is a central simple `k`-form of
`M_n(K)`. The module proves two descent facts. They are the first steps of
the simple-weight comparison of Tits (*Représentations linéaires
irréductibles d'un groupe réductif sur un corps quelconque*, J. reine angew.
Math. 247 (1971), Proposition 3.4, pp. 204–205), in this development's
matrix formulation: subspaces of `Kⁿ` stable under the twisted Galois action
are realized by idempotents of the `k`-form. Tits instead descends such
subspaces to `k` through the submodule correspondence of §1.4
(pp. 197–198); the idempotent formulation is this development's own.

## Declarations

- `twistedAct P σ M = (P σ)⁻¹ · σ(M) · P σ` is the twisted Galois action on
  matrices. Its twisted-fixed points are the elements of `twistedFixed P`.
  `twistedAct_add`, `twistedAct_zero` and `twistedAct_smul` show it is additive
  and `σ`-semilinear. `twistedAct_of_mem` shows it fixes `twistedFixed P`.
- `le_span_inf_of_twisted_stable`: let `S ⊆ M_n(K)` be a `K`-subspace stable
  under every `twistedAct P σ`. Then `S` is spanned over `K` by its elements
  lying in `A`. A `k`-basis of `A` is a `K`-basis of `M_n(K)`, built from
  `linearIndependent_of_le_twistedFixed` and `Module.Basis.mk`. In these
  coordinates the twisted action is coordinatewise `σ` (proved by induction on
  finitely supported coordinate vectors). Then the published
  `GaloisSubmoduleDescent.eq_span_ground_vectors` gives a spanning set of
  vectors with coordinates in `k`, and these are elements of `A`.
- `exists_idempotent_ker_eq`: let `n` be nonempty and `U ⊆ Kⁿ` a subspace stable
  under `u ↦ σ⁻¹(P σ · u)` for every `σ`. Then there is an idempotent
  `e ∈ A` whose kernel is exactly `U`. The proof has three steps.
  1. `A` is a semisimple ring: it is simple and finite-dimensional, hence
     Artinian (Mathlib's `IsSimpleRing.isSemisimpleRing_iff_isArtinianRing`).
     So the left ideal `L` of elements of `A` vanishing on `U` has a
     complement. Writing `1 = e + f` gives an idempotent `e ∈ L` with
     `X = X e` for all `X ∈ L`. Hence `U ⊆ ker e`.
  2. Conversely, suppose `v ∉ U`. A linear functional vanishing on `U` but not
     on `v` (Mathlib's `exists_dual_map_eq_bot_of_notMem`) gives a rank-one
     matrix `M` that kills `U` but not `v`.
  3. The matrices killing `U` form a twisted-stable subspace. By
     `le_span_inf_of_twisted_stable`, `M` is a `K`-combination of elements of
     `L`. Every element of `L` kills `v` once `e v = 0`. So `e v ≠ 0`.

  Consequently `1 - e` is an idempotent of `A` with image `U`.

No continuity or cocycle condition on `σ ↦ P σ` is used.
