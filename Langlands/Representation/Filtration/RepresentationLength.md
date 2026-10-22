# Composition length of actual representations

This internal module measures an actual representation `ρ : Representation k G V`
over a field `k` by Mathlib's module length of its module over the monoid
algebra:

- `repLength ρ := Module.length k[G] ρ.asModule`, a value in `ℕ∞` that is `⊤`
  exactly for representations without a finite composition series.

No topology, smoothness, or finiteness hypothesis enters. The coefficient field,
the monoid, and all carrier universes are independent.

## Results

- `repAsModuleEquiv e` turns an actual equivalence `e : ρ.Equiv σ` into a
  `k[G]`-linear equivalence of the monoid-algebra modules. Its forward map is
  Mathlib's `IntertwiningMap.equivLinearMapAsModule` and its inverse is `e.symm`.
  Hence `repLength_congr`: equivalent representations have equal length, also
  when their carriers live in different universes.
- `repLength_eq_add_of_exact`: if `f : ρ → σ` is injective, `g : σ → τ` is
  surjective, and the range of `f` equals the kernel of `g` (all as actual
  intertwining maps), then `repLength σ = repLength ρ + repLength τ`. The proof
  applies Mathlib's `Module.length_eq_add_of_exact` to the two intertwiners
  viewed as `k[G]`-linear maps.
- `repLength_eq_zero_iff`, `repLength_pos_iff`: the length is zero exactly when
  the carrier is a subsingleton, and positive exactly when it is nontrivial.
- `repLength_eq_one_iff`: the length is one exactly when `ρ.IsIrreducible`
  (Mathlib's `irreducible_iff_isSimpleModule_asModule` with
  `Module.length_eq_one_iff`).
- `repLength_eq_subrepresentation_add_quotient`: for an invariant subspace `S`,
  the length of `ρ` is that of `S.toRepresentation` plus that of the actual
  quotient representation, from the exact sequence given by the inclusion and
  the quotient map.
- `repLength_top`, `repLength_bot`: the full invariant subspace has the length
  of `ρ` (via the evident equivalence), and the zero subspace has length zero.
- `repLength_filtration_step`: in an `ObjectRepFiltration A n`, the step `i + 1`
  has the length of step `i` plus that of the `i`-th graded quotient. The exact
  sequence is the inclusion of step `i` into step `i + 1` followed by the
  published `gradedProjection`.
- `repLength_eq_sum_of_filtration`: the length of `A.ρ` is the sum of the
  lengths of all graded quotients of a finite object filtration, by induction
  on the steps from `subrepresentation_zero` to `subrepresentation_last`.
- `repLength_eq_of_hasSimpleFactors`: if a filtration with `n` steps has only
  irreducible graded quotients, then `repLength A.ρ = n`.

## Provenance

Internal. These are the standard facts that composition length is an additive
isomorphism invariant (Jordan–Hölder theory for modules), specialized to actual
representations through Mathlib's monoid-algebra module `ρ.asModule`. They serve
the two-block factor-matching proof of Bernstein–Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), §2.16(1), printed pages
449–450, where the length of Jacquet modules is used as an additive count.
No statement here is attributed to that source as a separate theorem.

Imported project constructions:

- `Filtration.ObjectDefinitions`: `ObjectRepFiltration`, its steps, graded
  quotients, graded projections, and `HasSimpleFactors`.

Author: Worker 286.
