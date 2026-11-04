# Boolean contraction of the surviving graded pieces

Author: Worker 1252. The imported signed cut diagrams, Boolean interval
diagrams, filtered subdiagrams, diagram equivalences and Coxeter minimality
results are earlier Library work by other authors.

This internal helper module serves the corrected Aubert Theorem 3.6 route.
It reduces the exactness of one graded piece of a filtered signed cut diagram
to the published exactness of the constant Boolean interval diagram. It also
proves the Coxeter facts that identify the cut sets surviving in a graded
piece and bound the top of their interval. It constructs no actual Jacquet
diagram or filtration step, and it proves no exactness of an actual graded
piece by itself. Those are applications of the results below. They need a
`BooleanContraction` of the actual graded piece and the Coxeter hypotheses.

## Coxeter part

The declarations live in `Langlands.Group.RelativeWeylIndexing`, for a
Coxeter system `cs` on simple indices `B`. `IsMinimal cs J I w` is the
published predicate saying that `w` has minimal length in `W_J w W_I`.

- `leftDescentSet cs w` is the finite set of simple `j` with
  `¬ ℓ(w) < ℓ(s_j w)`. `mem_leftDescentSet` unfolds it.
- `isMinimal_of_subset_left`: minimality in `W_J w W_I` implies minimality in
  `W_K w W_I` for `K ⊆ J`, because `W_K ⊆ W_J`.
- `right_length_lt_of_isMinimal`: minimality in `W_J w W_I` gives
  `ℓ(w) < ℓ(w s_i)` for every `i ∈ I`. This is one half of the published length
  criterion `minimalityLengthCriterion_proof`.
- `isMinimal_univ_sdiff_iff`: if `ℓ(w) < ℓ(w s_i)` for all `i ∈ I`, then `w` is
  minimal in `W_{S \ s} w W_I` exactly when `leftDescentSet cs w ⊆ s`. The proof
  rewrites with the same length criterion.
- `card_le_of_conj_mem`: if `w` is minimal in `W_K w W_I` and
  `w⁻¹ s_k w ∈ W_I` for every `k ∈ K`, then `|K| ≤ |I|`. The proof inverts the
  minimality (`isMinimal_inv`). It then applies the published
  `exists_conj_simple_eq_of_isMinimal` to write each `w⁻¹ s_k w` as a simple
  reflection `s_{f(k)}` with `f(k) ∈ I`. The map `f` is injective on `K` by
  `simple_reflection_injective`.
- `eq_of_standardSubgroup_conj`: if `W_K` and `W_{K'}` both consist of the
  elements `a` with `w⁻¹ a w ∈ W_I`, then `K = K'`. This follows from the
  published `standardSubgroup_injective`.
- `mem_inclusion_range_iff` describes the range of the published inclusion
  `RelativeWeyl.inclusion T L`. Its elements are the classes of normalizer
  elements of `T` lying in `L`.
- `mem_standardSubgroup_iff_of_leviConj` assumes the published
  `actualLeviWeylIdentification T L cs`. Let `m` be a normalizer element whose
  class is `w⁻¹`. Assume `x ∈ L I ↔ m⁻¹ x m ∈ L K` for all `x`, that is,
  `L K = m⁻¹ (L I) m`. Then `a ∈ W_K ↔ w⁻¹ a w ∈ W_I`. The proof transports
  conjugation by `m` through the two range descriptions.

## Survivors form a Boolean interval

The declarations in `Langlands.Aubert.CutComplex.BooleanInterval` are as
follows.

- `map_apply_of_active` and `map_apply_of_not_active` evaluate the published
  map of `BooleanInterval.diagram lower upper X`. The map evaluates the source
  coordinate when the source is active and is zero otherwise.
- `survivor_iff_active`: let the index type be finite and linearly ordered, and
  let `ℓ(w) < ℓ(w s_i)` for all `i ∈ I`. Then for every cut set `s`,
  `K ⊆ S \ s` together with minimality of `w` in `W_{S \ s} w W_I` is
  equivalent to `Active (leftDescentSet cs w) (S \ K) s`. That is,
  `leftDescentSet cs w ⊆ s ⊆ S \ K`.

`Diagram.Subdiagram.Survives cs I K w s` names the left-hand condition.

## Generic contraction

The declarations live in `Langlands.Aubert.CutComplex.Diagram.Subdiagram`.
Let `S` and `U` be subdiagrams of a signed cut diagram `D`. Then
`S.quotientDiagram U` is the published diagram with coordinates
`U.obj s / S.obj s`. Let `Surv` be a predicate on cut sets and `X` a complex
module. A structure `S.BooleanContraction U Surv X` consists of the following
fields.

- `coeff s hs : U.obj s →ₗ[ℂ] X` for every surviving `s`.
- `coeff_surjective`: each `coeff s hs` is surjective.
- `coeff_eq_zero_iff`: the kernel of `coeff s hs` is the lower step `S.obj s`.
- `coeff_natural`: for surviving `s ⊆ t`, `coeff t` composed with the actual
  transition `D.map` equals `coeff s`.
- `inactive`: if `s` does not survive, then `U.obj s ⊆ S.obj s`.

The structure contains no exactness or vanishing hypothesis about the
differentials.

`quotient_subsingleton_of_le` and `degree_subsingleton_of_le` say that the
coordinates and the homogeneous terms of the graded piece are zero when
`U ⊆ S` coordinatewise. In that case `quotient_exact_of_le` proves exactness
in every degree, and `quotient_injective_of_le` proves injectivity of every
homogeneous differential.

Given a contraction `C` and `hSurv : ∀ s, Surv s ↔ Active lower upper s`, the
results are as follows.

- `C.toBoolean hSurv s` descends the coefficient map to
  `U.obj s / S.obj s → (PLift (Active lower upper s) → X)`. It is well defined
  by `coeff_eq_zero_iff`. `toBoolean_mk` is its value on a class.
- `toBoolean_bijective` proves that it is bijective. Injectivity uses
  `coeff_eq_zero_iff` on active sets and `inactive` elsewhere. Surjectivity
  uses `coeff_surjective`.
- `booleanEquivalence` packages these maps as a published
  `CutComplex.Equivalence` from the graded piece to
  `BooleanInterval.diagram lower upper X`. Naturality on an active source is
  `coeff_natural`. On an inactive source both sides vanish, by `inactive`,
  the subdiagram property of `S` and `coeff_eq_zero_iff`.
- `range_eq_ker`: let `lower ⊆ upper` and `k + 1 < |upper|`. Then the range of
  the degree-`k` differential of the graded piece equals the kernel of the
  degree-`k+1` differential. The proof transfers the published
  `exact_below_allowed` along `degreeDifferential_exact_iff`.
- `injective_zero`: let `lower ⊆ upper` and `0 < |upper|`. Then the degree-zero
  differential is injective. The proof transfers `injective_before_allowed`
  along `degreeDifferential_injective_iff`.

## Specialization to the survivors at `w`

Let the index type be finite, and assume
`hconj : ∀ a, a ∈ W_K ↔ w⁻¹ a w ∈ W_I`. Let some `s₀` satisfy
`Survives cs I K w s₀`.

- `card_le_terminal_of_survives` proves `|S| - |I| ≤ |S \ K|`. Minimality
  restricts from `S \ s₀` to `K`, which is contained in it. Then
  `card_le_of_conj_mem` gives `|K| ≤ |I|`.
- `range_eq_ker_of_survives`: let `C` be a contraction over
  `Survives cs I K w`. Then for `k + 1 < |S| - |I|`, the degree-`k` range of the
  graded piece equals the degree-`k+1` kernel.
- `injective_zero_of_survives`: under the same data and `0 < |S| - |I|`, the
  degree-zero differential of the graded piece is injective.

Both proofs take right-`I`-minimality of `w` from `s₀`. They then use
`survivor_iff_active` as `hSurv`, with `lower = leftDescentSet cs w` and
`upper = S \ K`. Activity of `s₀` gives `lower ⊆ upper`. The cardinality
bound reduces the hypothesis to `range_eq_ker` and `injective_zero`.

## Provenance

The module is internal. It is the algebraic step of the corrected proof of
Theorem 3.6 that follows the graded targets of
`Langlands.Aubert.General.CorrectedFiltrationStatements` (Aubert's erratum,
Trans. AMS 348 (1996), pp. 4688–4690, with the Ban–Jantzen 2016 Section 4
repair). Those targets describe the `i`-th graded step. A nonzero coordinate
yields a standard `K` with `M K = m⁻¹ (M I) m`. On the survivors, surjections
`β` onto one coefficient have the lower step as kernel and are compatible with
the transitions; these are the fields of `BooleanContraction`. The
generic structure, the survivor interval from the left descents of `w` to
`S \ K`, and the bound `|K| ≤ |I|` are formulated and proved here. They are
not quoted from the sources. The Coxeter facts are standard for parabolic
double cosets. Here they are derived from the published minimality length
criterion, the conjugate simple reflection lemma, the injectivity of simple
reflections and of standard parabolic subgroups, and the actual Levi Weyl
identification.

## Sources

* A.-M. Aubert, *Erratum*, Trans. AMS 348 (1996), printed pp. 4688–4690.
* D. Ban and C. Jantzen, *The Langlands quotient theorem for finite central
  extensions of p-adic groups II: intertwining operators and duality*, Glasnik
  Matematički 51 (2016), Section 4.
