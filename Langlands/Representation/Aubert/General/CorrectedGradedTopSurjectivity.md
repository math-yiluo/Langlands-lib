# Surjectivity of the last graded differential of the corrected filtration

Author: Worker 1252. The actual Jacquet diagram, the corrected support
filtration, its graded pieces and the `FiniteFiltered.gradedMap` form
`gradedDifferential` are Worker 691's modules `General.JacquetCutDiagram` and
`General.CorrectedDegreeFiltration`. The Boolean contraction, the survivor
predicate `Survives`, `leftDescentSet` and the eliminator `graded_cases` are
this author's `General.CorrectedGradedContraction` and
`General.CorrectedGradedExactness`. The Coxeter length facts
`eq_of_forall_length_mul_simple_lt` (`Group.RelativeWeylLongestProof`),
`length_mul_of_right_minimal` and `minimalityLengthCriterion_proof`
(`Group.RelativeWeylMinimalityProof`), the free-coordinate exactness
`BooleanInterval.exact_of_free_coordinate` (`BooleanIntervalComplex`), the
rank-ordered enumeration `Support.rankOrderedEquiv` (`RankOrderedSupports`),
the two graded targets, the Levi Weyl identification and the support
category are earlier Library work by other authors.

This internal helper module serves the corrected Aubert Theorem 3.6 route
(Aubert, *Dualité dans le groupe de Grothendieck de la catégorie des
représentations lisses de longueur finie d'un groupe réductif p-adique*,
Trans. AMS 347 (1995), Thm. 3.6, and its erratum). It is derived glue and is
not a statement of the paper. It was written for Worker 757's top-degree
cokernel step, an unpublished module that this module does not import. Its
premise `hsurj` asks for surjectivity of the graded map into degree `|S| - |I|` at every
grade after a fixed grade `i₀`.

That premise does not hold at every grade unconditionally. A graded piece
with a Boolean contraction over the survivors at `w` is the constant interval
diagram from the left descents of `w` to `S \ K`, where
`W_K = w W_I w⁻¹`. Its last differential is surjective when the interval has
a free coordinate, that is, when the left descents of `w` are not all of
`S \ K`. Exactly one right-`I`-minimal `w` has no free coordinate, and its
piece is the top cokernel itself. So the premise holds for every `i > i₀`
when `w_{i₀}` is that element. The module proves this.

The theorems are conditional on the premises `hvan`, `htrans`, `hLevi` and
`hA` of `General.CorrectedGradedExactness`, the two published but unproved
graded targets, the Levi Weyl identification and membership of `A` in
`Alg({I})`. They prove none of them. They do not use the Bruhat cover. Write
`|S| = Fintype.card ι`, `w_i` for
`Support.rankOrderedElement cs.length i hi`, and `W_J` for
`standardSubgroup cs J`.

## Coxeter facts

These live in `Langlands.Group.RelativeWeylIndexing`, for any Coxeter system
`cs : CoxeterSystem Mx W` with `[Fintype B]` and `[DecidableEq B]`.

`inv_mul_eq_of_leftDescentSet_eq`: assume that `w` is right-`I`-minimal
(`ℓ(w) < ℓ(w s_i)` for `i ∈ I`), that `a ∈ W_K ↔ w⁻¹ a w ∈ W_I` for all `a`,
and that `leftDescentSet cs w = Finset.univ \ K`. Let `a ∈ W_I` have maximal
length in `W_I` and `w₀` maximal length in `W`. Then `(w a)⁻¹ = w₀`. The
proof checks that every `s_j` is a left descent of `w a` and applies
`eq_of_forall_length_mul_simple_lt` to `(w a)⁻¹`. Here
`ℓ(w b) = ℓ(w) + ℓ(b)` for `b ∈ W_I` by `length_mul_of_right_minimal`. For
`j ∈ K`, `s_j w a = w (w⁻¹ s_j w) a` with `(w⁻¹ s_j w) a ∈ W_I` of length at
most `ℓ(a)` and different from it, since `w⁻¹ s_j w` is a reflection. For
`j ∉ K`, `j` is a left descent of `w`, so `ℓ(s_j w a) ≤ ℓ(s_j w) + ℓ(a)`
`< ℓ(w) + ℓ(a)`.

`eq_of_leftDescentSet_eq`: with `[Fintype W]`, if `w` and `w'` both satisfy
these three hypotheses, for possibly different `K` and `K'`, then `w = w'`.
Both equal `w₀ a⁻¹` by the previous theorem, with the same choices of `a`
and `w₀`.

## Boolean pieces

These live in `Langlands.Aubert.CutComplex.Diagram.Subdiagram`, for
subdiagrams `S U` of a diagram over a finite linearly ordered `ι`.

`BooleanContraction.surjective_top`: let `C : S.BooleanContraction U Surv X`
with `Surv s ↔ BooleanInterval.Active lower upper s`. If `lower ⊆ upper`,
`lower ≠ upper` and `upper.card ≤ k + 1`, then degree differential `k` of
`S.quotientDiagram U` is surjective. A coordinate in `upper \ lower` is free,
so the Boolean equivalence and `exact_of_free_coordinate` give
`range = ker` for the differentials `k` and `k + 1`. Degree `k + 2` is zero,
because no cut set of that size survives (`quotient_subsingleton_of_le` with
`C.inactive`). So the kernel of differential `k + 1` is everything.

`card_le_of_conj`: if `a ∈ W_K ↔ w⁻¹ a w ∈ W_I` for all `a` and `w` is
minimal in `W_K w W_I`, then `I.card ≤ K.card`. It applies
`card_le_of_conj_mem` to `w⁻¹`.

`surjective_top_of_survives`: let `a ∈ W_K ↔ w⁻¹ a w ∈ W_I` for all `a`, let
some `s₀` satisfy `Survives cs I K w s₀`, let
`C : S.BooleanContraction U (Survives cs I K w) X`, and let
`leftDescentSet cs w ≠ Finset.univ \ K`. Then for `k + 1 = |S| - |I|`,
degree differential `k` of `S.quotientDiagram U` is surjective. By
`survivor_iff_active`, the survivors are the interval from the left descents
of `w` to `S \ K`. The survivor `s₀` makes it nonempty, so its ends are
ordered. Its top has size `|S| - |K| ≤ |S| - |I|` by `card_le_of_conj`, so
`surjective_top` applies.

## Actual graded pieces

These live in `Langlands.Aubert.General.JacquetComplex`, with the variables
of `General.CorrectedDegreeFiltration`.

`graded_surjective_top`: take `hvan`, `htrans`, `hLevi`, `hA`, `hi`, and
subdiagrams `Lo Up` of `jacquetDiagram ... A I` whose coordinates have the
members of steps `i` and `i + 1` (`hLo`, `hUp`). Assume `hfree`: for every
`K` with `a ∈ W_K ↔ w_i⁻¹ a w_i ∈ W_I` for all `a`, if `w_i` is
right-`I`-minimal, then `leftDescentSet cs w_i ≠ Finset.univ \ K`. Then for
`k + 1 = |S| - |I|`, degree differential `k` of `Lo.quotientDiagram Up` is
surjective. The proof uses `graded_cases`. In case A degree `k + 1` of the
quotient is zero (`degree_subsingleton_of_le`). In case B it is
`surjective_top_of_survives`.

`gradedDifferential_surjective_iff`: Worker 691's
`gradedDifferential ... i k` is surjective if and only if degree differential
`k` of `gradedDiagram ... i` is. It transfers along `gradedEquiv` and
`gradedEquiv_differential`.

`gradedDifferential_surjective_top_of_leftDescentSet_eq`: take `hvan`,
`htrans`, `hLevi`, `hA` and a grade `i₀` with
`hi₀ : i₀ < (Support.rankOrderedList cs.length).length`. Assume a `K₀` with
`a ∈ W_{K₀} ↔ w_{i₀}⁻¹ a w_{i₀} ∈ W_I` for all `a` (`hconj₀`), that `w_{i₀}`
is right-`I`-minimal (`hR₀`), and that
`leftDescentSet cs w_{i₀} = Finset.univ \ K₀` (`hD₀`). The conclusion has
the shape of Worker 757's `hsurj` for this `A`:

```
∀ k, k + 1 = Complex.terminalDegree I → ∀ i, i₀ < i →
  i < (Support.rankOrderedList cs.length).length →
  Function.Surjective (gradedDifferential ... T cs A I i k)
```

The proof rewrites with `gradedDifferential_surjective_iff` and applies
`graded_surjective_top` with `Iff.rfl` for `hLo` and `hUp`. For `hfree`, if
`w_i` had left descents `S \ K`, then `eq_of_leftDescentSet_eq` would give
`w_i = w_{i₀}`. Then `Support.rankOrderedEquiv` is injective, so `i = i₀`,
contradicting `i₀ < i`.

Nothing here identifies `w_{i₀}` from vanishing data or treats the grade
`i₀` itself.
