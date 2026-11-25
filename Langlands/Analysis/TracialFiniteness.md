# Finite dimensionality from a faithful tracial vector

## Statements

Throughout, `H` is a complex Hilbert space (`InnerProductSpace ℂ H`, `CompleteSpace H`), or a
complex Banach space in the density section.

* `restrictAlgHom B V hBV`: the restriction of a subalgebra `B` of `H →L[ℂ] H` to a
  `B`-invariant subspace `V`, as an algebra homomorphism `B →ₐ[ℂ] Module.End ℂ V`.
  `restrictAlgHom_apply` gives its value.
* `exists_mem_eq_on_finset` (density). `H` is a complex Banach space and `B` a subalgebra of
  bounded operators that leaves `V` invariant. Assume `B` acts transitively on `V`: for
  `u ≠ 0` and `w` in `V` some `b ∈ B` has `b u = w`. Then every `ℂ`-linear map
  `f : V →ₗ[ℂ] V` agrees with some element of `B` on any given finite subset of `V`.
* `commute_starProjection_of_invariant`: if a bounded operator `T` and its adjoint
  `star T` both preserve a subspace `K` that has an orthogonal projection, then `T`
  commutes with `K.starProjection`.
* `starProjection_mem_centralizer`: if `K` is invariant under every `s ∈ S` and every
  `star s`, then `K.starProjection` lies in `StarSubalgebra.centralizer ℂ S`.
* `inner_eq_inner_star_of_norm_eq` (polarization). Let `N` be a star subalgebra. If
  `‖x ξ‖ = ‖star x ξ‖` for all `x ∈ N`, then `⟪z ξ, w ξ⟫ = ⟪star w ξ, star z ξ⟫` for
  `z, w ∈ N`.
* `inner_starProjection_self`: `⟪ξ, P ξ⟫ = ‖P ξ‖²` for the orthogonal projection `P`
  onto a subspace.
* `finiteDimensional_of_tracial` (main theorem). Let `S` be a set of bounded operators on
  `H`, and let `N = StarSubalgebra.centralizer ℂ S` be its star-commutant. Let `ξ ∈ H`
  satisfy
  - `hnorm`: `‖x ξ‖ = ‖star x ξ‖` for all `x ∈ N` (`ξ` is tracial for `N`);
  - `hsep`: `x ξ = 0 → x = 0` for all `x ∈ N` (`ξ` is separating for `N`).

  Let `B` be a subalgebra contained in `N`, and `V` a subspace (not necessarily closed)
  that `B` leaves invariant and on which `B` acts transitively. Then
  `FiniteDimensional ℂ V`.
* `finiteDimensional_of_tracial'`: the same conclusion when, for `u ≠ 0` and `w` in `V`,
  some element of `N` that preserves `V` sends `u` to `w`. `B` is then the subalgebra of
  elements of `N` that preserve `V`.

## Provenance

This is an internal helper for the proof of the Remark of Renard IV.3.2
(`Langlands.Renard.CompactRepresentation.SingleCoefficientSquareIntegrabilityStatement`).
Renard leaves the Remark to the reader. In that proof, `H` is a space of square-integrable
functions and `S` the operators of the regular representation. `ξ` is the twisted
characteristic function of a compact open subgroup, and `V` is the image of the `K`-fixed
vectors of the representation. The theorem then gives the admissibility of an irreducible
smooth representation that has one nonzero square-integrable coefficient.

The trace inequality `dim ≤ ‖ξ‖² / ‖q ξ‖²` follows a countable-case argument, made here
independent of countability: the density step uses the Jacobson density theorem (`jacobson_density`) with
the bounded Schur lemma `Langlands.Analysis.exists_eq_smul_id_of_commutesOn` from
`Langlands/Analysis/BoundedSchur.lean`, so no Dixmier-type Schur lemma is needed. The
general facts are standard: the density theorem, polarization, and the trace property of a
tracial vector.

## Lean proof

* Density. Write `ρ = restrictAlgHom B V hBV` and `R = ρ.range`. Transitivity makes `V`
  a simple `R`-module (`isSimpleModule_iff_toSpanSingleton_surjective`). Every
  `R`-linear endomorphism `g` of `V` is `ℂ`-linear, because `ℂ` acts through
  `algebraMap ℂ R`, and it commutes with `B` in the sense of `CommutesOn`. So
  `exists_eq_smul_id_of_commutesOn` makes `g` a scalar. Hence `f` is linear over
  `Module.End R V`, and `jacobson_density` gives `r ∈ R` that agrees with `f` on the
  finite set. Any preimage `b ∈ B` of `r` works.
* Projection lemmas. For `x ∈ K`, `T (x - P x)` is orthogonal to `K`, because
  `⟪u, T y⟫ = ⟪star T u, y⟫` and `star T` preserves `K`. Splitting
  `x = P x + (x - P x)` then gives `T (P x) = P (T x)`. Membership in the centralizer
  needs `P` to commute with `s` and with `star s`, so the lemma is applied to `s` and to
  `star s`.
* Polarization. Apply `hnorm` to `z + c • w` for `c = 1, -1, I, -I`, and compare the two
  polarization identities `inner_eq_sum_norm_sq_div_four`.
* Main theorem.
  1. Trace property: `⟪ξ, (x * y) ξ⟫ = ⟪ξ, (y * x) ξ⟫` for `x, y ∈ N`, by adjoints and
     polarization.
  2. Fix `v ≠ 0` in `V`. Let `Q = {x | ∀ c ∈ B, c v = 0 → c x = 0}`, a closed subspace,
     and `q` its orthogonal projection. Each `c ∈ B` commutes with every `s ∈ S` and every
     `star s`. Hence `Q` is invariant under `S` and under the adjoints, so `q ∈ N`. Also
     `q v = v`. If `q ξ = 0`, then `hsep` gives `q = 0`, which contradicts `q v = v ≠ 0`.
     So `q ξ ≠ 0`.
  3. Trace inequality. Let `s` be a finite linearly independent family in `V`. Extend it
     to a basis and take the coordinate functionals `φ i`. By density, choose `a i ∈ B`
     agreeing with `m ↦ φ i m • v` on `s`. By transitivity, choose `c j ∈ B` with
     `c j v = j`. Then `(a i * c j) v` is `v` if `j = i` and `0` otherwise. By the
     definition of `Q` this gives `a i * c j * q = δ_{ij} q`. With `x j = c j * q` and
     `y i = q * a i`, both in `N`, `p = Σ_j x j * y j` is an idempotent in `N`. Let `r` be
     the orthogonal projection onto the closed subspace `ker (1 - p)`. Then `r ∈ N`,
     `r * p = p` and `p * r = r`. The trace property gives
     `card s · ‖q ξ‖² = ⟪ξ, p ξ⟫ = ⟪ξ, (r * p) ξ⟫ = ⟪ξ, (p * r) ξ⟫ = ‖r ξ‖² ≤ ‖ξ‖²`.
  4. So every linearly independent finite family in `V` has at most
     `⌊‖ξ‖² / ‖q ξ‖²⌋` elements. `rank_le` then bounds `Module.rank ℂ V` by a natural
     number, and `V` is finite dimensional.

The file imports `Langlands.Analysis.BoundedSchur` and Mathlib.
