# Optimal points (Kaletha–Prasad §13.4, definitions)

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §13.4 (printed
pp. 471–474, PDF pp. 502–505; the definitions are on printed p. 472, PDF
p. 503) defines the following objects:

- the period `ℓ` of the affine roots;
- the finite set `Σ` attached to a chamber `C`;
- rational affine functionals and rational points (Definition 13.4.1);
- optimal points (Definition 13.4.2).

This module formalizes these definitions with the basic finiteness and
nonemptiness facts that the text uses. They are stated for an abstract set `Ψ`
of affine functionals on a real affine space, and then for the actual affine
roots and the reduced building of supplied valuation building data.

The module contains no optimality theorem. The following are not formalized:

- the existence of optimal points (the linear-programming argument after
  Definition 13.4.2);
- the choice of points `x_S`, the set `O` and optimal numbers;
- Example 13.4.3 (`SL_3`);
- Lemma 13.4.4.

The 1 November 2024 corrections list no change to §13.4 (their Chapter 13
entries on PDF p. 49 concern 13.5.2, 13.6.2 and 13.8.5).

## Setting and Library inputs

`V` is a real vector space and `A` an affine space over `V`.
`Ψ : Set (A →ᵃ[ℝ] ℝ)` is a set of affine functionals, and `c : A` a point. All
chamber notions are taken from the Library:

- `facet Ψ c`, the facet of `c` (`Geometry.Building.AffineRootSystem`). When
  `c` is regular (`GalleryGeometry.IsRegular Ψ c`: no root vanishes at `c`),
  `facet Ψ c` is the chamber `C` containing `c`.
- `facetClosure Ψ c`, the closed facet: the points `y` such that every root
  either vanishes at `y` or has the same sign at `y` as at `c`. For regular
  `c`, this is KP's `C̄`. The Library proves that it is closed
  (`isClosed_facetClosure`) and lies in the topological closure of the facet
  (`facetClosure_subset_closure_facet`). It also proves KP's description
  `C̄ = {x | ψ(x) ≥ 0 for all ψ ∈ Δ}` (`mem_facetClosure_iff_simple_nonneg`).
- `positiveRoots Ψ C`, the roots positive on `C` (KP's `ψ > 0`, KP Definition
  1.3.18).
- `simpleAffineRoots Ψ C`, the simple affine roots of the Library (KP
  Definition 1.3.19). These are the positive indivisible roots whose hyperplane
  is a wall of `C`.
- `IsAffineRootSystemWithRankZero Ψ`, the corrected axioms AR 1–AR 4. AR 4 is
  used in the form `finite_bounded`, and the bounded-finiteness consequence
  `finite_bounded_at` comes from `Geometry.Building.AffineChamberSeparation`.
- For `B : ValuationBuildingData G`, the module uses `B.Apartment`,
  `B.affineRoots` (KP's `Ψ`), `B.ReducedBuilding`, `B.apartmentMap` and the
  `G(F)`-action. It also uses:
  - `isAffineRootSystemWithRankZero_affineRoots` and
    `exists_conjugateAffineFunctional_eq_add_two`, both from
    `Geometry.Building.ValuationAffineRootSystems`;
  - `conjugateAffineFunctional_mem_affineRoots`.

The abstract declarations are in the namespace
`Langlands.Geometry.Building.AffineRootSystem`. The declarations about
valuation building data are in `Langlands.Geometry.Building.ValuationBuildingData`.

## The period `ℓ`

KP: "Let `ℓ` be the smallest positive rational number such that for any affine
root `ψ`, `ψ + ℓ` is also an affine root."

- `rationalRootPeriods Ψ : Set ℝ` is the set of positive real numbers `t` such
  that `t` is the image of a rational number and `ψ + t ∈ Ψ` for every `ψ ∈ Ψ`.
  Here `t` stands for the constant affine function `AffineMap.const ℝ A t`.
- `rootPeriod Ψ := sInf (rationalRootPeriods Ψ)`. This is KP's `ℓ` whenever the
  least element exists (`rootPeriod_eq_of_isLeast`). If there is no positive
  rational period, the infimum of the empty set is `0` by Mathlib's convention
  for `ℝ`. Every statement below that uses `ℓ` as a period assumes
  `rootPeriod Ψ ∈ rationalRootPeriods Ψ` or proves it.
- `exists_isLeast_rationalRootPeriods hfin hne ht` assumes three things:
  - AR 4's bounded finiteness `hfin`: for `ψ ∈ Ψ` and `M`, only finitely many
    `η ∈ Ψ` with `η̇ = ψ̇` satisfy `|η - ψ| ≤ M` everywhere;
  - `Ψ` is nonempty;
  - `t` is a positive rational period.

  Under these assumptions the least positive rational period exists. Proof: fix
  `ψ ∈ Ψ`. The map `s ↦ ψ + s` is injective (evaluate at a point). It sends the
  periods `s ≤ t` into the roots `η` with `η̇ = ψ̇` and `|η - ψ| = s ≤ t`. That
  set is finite by `hfin`, so the periods in `(0, t]` form a finite nonempty
  set. Its minimum (`Set.exists_min_image`) is the least period.
- `IsAffineRootSystemWithRankZero.exists_isLeast_rationalRootPeriods` and
  `IsAffineRootSystemWithRankZero.isLeast_rootPeriod` state the same for an
  affine root system. The second says that `rootPeriod Ψ` itself is the least
  element.

Without the nonemptiness hypothesis the claim fails: for `Ψ = ∅`, every positive
rational number is a period and there is no least one.

## The set `Σ`

KP: "we will denote by `Σ` the finite set of affine roots `ψ` such that
`ψ > 0` and `ψ − ℓ < 0`", with signs taken on the fixed chamber `C`.

- `positiveRootsBelowPeriod Ψ c` is the set of `ψ ∈ positiveRoots Ψ (facet Ψ c)`
  with `ψ(y) - rootPeriod Ψ < 0` for every `y ∈ facet Ψ c`. This helper
  formula also makes sense on an arbitrary facet. It gives KP's `Σ` when
  `c` is regular and the least positive rational period exists. The
  condition is stated pointwise, so its definition does not need `ψ - ℓ`
  to have been shown to be a root.
- `positiveRootsBelowPeriod_subset`: `Σ ⊆ Ψ`.
- `mem_positiveRootsBelowPeriod_apply`: for `ψ ∈ Σ`, `0 < ψ(c) < ℓ`.
- `IsAffineRootSystemWithRankZero.finite_positiveRootsBelowPeriod`: `Σ` is
  finite (KP's "the finite set `Σ`"). Every `ψ ∈ Σ` satisfies
  `|ψ(c)| ≤ ℓ`, and the Library's `finite_bounded_at` at `c` bounds the number
  of such roots.
- `IsAffineRootSystemWithRankZero.add_intCast_mul_mem`: if `ℓ` is a period of
  an affine root system, then `ψ + kℓ ∈ Ψ` for all `ψ ∈ Ψ` and `k ∈ ℤ`.
  Subtraction of `ℓ` comes from AR 2 (`Ψ = -Ψ`): `ψ - ℓ = -((-ψ) + ℓ)`. The
  proof is by integer induction.
- `IsAffineRootSystemWithRankZero.positiveRootsBelowPeriod_nonempty hc hne hℓ`
  assumes that `c` is regular, `Ψ` is nonempty and `ℓ` is a period. Under these
  assumptions `Σ` is nonempty. KP use this implicitly, for instance in "Note
  that `S` is non-empty" in the proof of 13.4.4. Proof: take a root `η` with
  `η(c) > 0`, using `-ψ` if needed. Put `k = ⌈η(c)/ℓ⌉ - 1` and
  `θ = η - kℓ ∈ Ψ`. Then `0 < θ(c) ≤ ℓ`. The case `θ(c) = ℓ` is impossible,
  because `θ - ℓ` is a root vanishing at the regular point `c`. A root is
  positive or negative on the chamber
  (`IsChamber.mem_positiveRoots_or_mem_negativeRoots`). So `θ` is positive on
  `C` and `θ - ℓ` is negative on `C`, that is, `θ ∈ Σ`.

## Rationality (Definition 13.4.1)

- `IsRationalPoint Ψ x`: every `ψ ∈ Ψ` takes a value in `ℚ` at `x` (the
  second sentence of Definition 13.4.1).
- `indecomposablePositiveRoots Ψ C`: the roots positive on `C` that are not
  sums of two roots positive on `C`. This is the generator rule immediately
  preceding Definition 13.4.1 in §13.4.
- `IsRationalAffineFunctional Ψ c f` requires a regular `c` and an expression
  `f = ∑_{ψ ∈ s} q_ψ ψ` for a finite set
  `s ⊆ indecomposablePositiveRoots Ψ (facet Ψ c)` and rational `q_ψ`. This
  implements the first sentence of Definition 13.4.1 using that rule.
- `IsRationalAffineFunctional.apply_mem_range`: a rational affine functional
  takes a rational value at a rational point. Evaluation at `x` is additive, and
  `ℚ` is a subring of `ℝ`.

The generators here are distinct in definition from `simpleAffineRoots`, the
Library's wall roots from KP Definition 1.3.19. In a reduced affine system of
type `A₁`, both possible root slopes are nonzero and opposite. A sum of two
root slopes is either zero or twice one of the slopes, so *every* positive root
is indecomposable in the sense above, not just the two wall roots. The finite
sum in `IsRationalAffineFunctional` does not assert that the generator set is
finite or linearly independent. The optimal-point predicates use only the
rationality of points, not `IsRationalAffineFunctional`.

## Optimal points (Definition 13.4.2)

- `IsOptimalPointFor Ψ c S x` requires `IsRegular Ψ c`, so that the domain
  of optimization is the closure of a chamber, not of an arbitrary facet.
  Given a `Finset` `S` of affine functionals, it additionally requires
  `hS : S.Nonempty` and the following conditions:
  - `S ⊆ positiveRootsBelowPeriod Ψ c`;
  - `x ∈ facetClosure Ψ c`;
  - for all `y ∈ facetClosure Ψ c`,
    `S.inf' hS (ψ ↦ ψ y) ≤ S.inf' hS (ψ ↦ ψ x)` (KP's condition (1),
    `min_{ψ∈S} ψ(x) ≥ min_{ψ∈S} ψ(y)`);
  - `IsRationalPoint Ψ x` (KP's condition (2)).

  KP's `S` is a nonempty subset of the finite set `Σ`, so it is finite, and
  `Finset` loses nothing. Nonemptiness is part of the predicate, as in KP. The
  minimum is `Finset.inf'`, the minimum of a nonempty finite set.
- `isOptimalPointFor_iff` gives the same conditions without `Finset.inf'`.
  Condition (1) becomes: for every `y` in the closed chamber there is `φ ∈ S`
  with `φ(y) ≤ ψ(x)` for all `ψ ∈ S`.
- `isOptimalPointFor_singleton_iff`: `x` is optimal for `{ψ}` exactly when
  `c` is regular, `ψ ∈ Σ`, `x` is a rational point of the closed chamber, and
  `ψ` attains its maximum over the closed chamber at `x`.
- Projections: `IsOptimalPointFor.isRegular`, `IsOptimalPointFor.mem_facetClosure`,
  `IsOptimalPointFor.isRationalPoint`, `IsOptimalPointFor.subset`.
- `IsOptimalPoint Ψ x`: there are `c` and a finite set `S` with
  `IsOptimalPointFor Ψ c S x`, which already requires regularity of `c`.
  This is the second sentence of Definition 13.4.2
  inside one apartment: "a chamber `C ⊂ A` and a non-empty finite subset `S` of
  the `Σ` associated to `C`, such that `x ∈ C̄` is optimal for `S`". The
  chambers of `A` are exactly the sets `facet Ψ c` with `c` regular (the
  Library's `IsChamber`).
- `not_isOptimalPointFor_of_eq_empty` and `not_isOptimalPoint_of_eq_empty`: if
  `Ψ = ∅` there are no optimal points, because `Σ ⊆ Ψ` is empty and `S` must be
  a nonempty subset of it.

## Actual affine roots and the building

For `B : ValuationBuildingData G`:

- `add_two_mem_affineRoots`: `ψ ∈ B.affineRoots` implies
  `ψ + 2 ∈ B.affineRoots`. The Library provides two facts. First, some
  normalizer element `n` satisfies `n · ψ = ψ + 2` for every functional with
  the derivative of `ψ` (`exists_conjugateAffineFunctional_eq_add_two`).
  Second, normalizer conjugation preserves affine roots
  (`conjugateAffineFunctional_mem_affineRoots`).
- `two_mem_rationalRootPeriods_affineRoots`: `2` is a positive rational period.
- `isLeast_rootPeriod_affineRoots hne`: if `B.affineRoots` is nonempty, then
  `rootPeriod B.affineRoots` is the least positive rational period, i.e. KP's
  `ℓ` exists. The proof combines `isLeast_rootPeriod` with
  `isAffineRootSystemWithRankZero_affineRoots`.
- `rootPeriod_affineRoots_pos`, `rootPeriod_affineRoots_le_two`: `0 < ℓ ≤ 2`.
  The value of `ℓ` is not computed; the Library's normalization of the affine
  roots is not used beyond the period `2`.
- `positiveRootsBelowPeriod_affineRoots_finite_nonempty hne hc`: for nonempty
  actual affine roots and a regular point `c`, `Σ` is finite and nonempty.
- `IsOptimalPoint (y : B.ReducedBuilding)`: there are `g ∈ G(F)` and
  `x ∈ B.Apartment` with `g • B.apartmentMap x = y` and
  `AffineRootSystem.IsOptimalPoint B.affineRoots x`. This is the second sentence
  of Definition 13.4.2, "there exists an apartment `A` of `B`, a chamber
  `C ⊂ A`, …". In KP every apartment of `B(G)` is a `G(F)`-translate of
  `A(S)`, since the maximal split tori are `G(F)`-conjugate. The Library has
  no separate affine-root structure on `g · A(S)`. As for its
  `ValuationBuildingData.IsVertex`, `IsFacet` and `IsChamber`, the notion is
  transported: `y` is optimal in `g · A(S)` when `g⁻¹ · y` is the image of an
  optimal point of `A(S)`.
- `isOptimalPoint_apartmentMap`: optimal points of the apartment are optimal
  points of `B(G)`.
- `IsOptimalPoint.smul`: the set of optimal points of `B(G)` is
  `G(F)`-stable.
- `not_isOptimalPoint_of_affineRoots_eq_empty`: with no actual affine roots,
  `B(G)` has no optimal point. This is the empty-root boundary of Definition
  13.4.2 that the source ledger records for Proposition 13.6.7: for `G_m` over
  `ℚ_2`, `Σ` is empty. This module proves only that the definition then has no
  instances. It does not prove that the affine roots of a torus are empty.

## Not claimed

- The existence of optimal points for every nonempty `S ⊆ Σ` (KP's
  linear-programming argument: the polyhedra `C_i`, rationality of their
  vertices, and the maximum `c_j`), and the fact that `O` is locally finite.
- Example 13.4.3 and Lemma 13.4.4.
- Any comparison of the rational span of `indecomposablePositiveRoots` with
  that of `simpleAffineRoots`.
- The value of `ℓ` for the actual affine roots, or any relation between `ℓ`
  and the normalization of the valuation.
- Any statement about optimal points for `𝔤*` (KP refer to [MP94, §6.1]) or
  about optimal numbers.

## Provenance

The definitions transcribe KP §13.4 (printed p. 472, PDF p. 503).
Three choices are internal:

- `ℓ` is defined as an infimum, with its existence proved separately.
- `Σ` is stated pointwise on the chamber.
- The building-level predicate is expressed through `G(F)`-translates of the
  standard apartment.

The finiteness and nonemptiness lemmas make explicit facts that KP state
without proof ("the finite set `Σ`", "`S` is non-empty"). Their proofs are
internal. The Lean code is internal; no external code is adapted.
