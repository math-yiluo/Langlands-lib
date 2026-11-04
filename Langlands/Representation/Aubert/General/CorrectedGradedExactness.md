# Exactness of the graded Jacquet pieces of the corrected filtration

Author: Worker 1252. The actual Jacquet diagram, the corrected support
filtration, its graded pieces and their finite lifting are Worker 691's
modules `General.JacquetCutDiagram` and `General.CorrectedDegreeFiltration`.
The Boolean contraction and Coxeter facts are this author's
`General.CorrectedGradedContraction`. The two graded targets, the Levi Weyl
identification and the support category are earlier Library work by other
authors.

This internal helper module serves the corrected Aubert Theorem 3.6 route
(Aubert, *Dualité dans le groupe de Grothendieck de la catégorie des
représentations lisses de longueur finie d'un groupe réductif p-adique*,
Trans. AMS 347 (1995), Thm. 3.6, and its erratum). It is conditional. It
assumes the following statements as premises and proves none of them.

- `hvan : CorrectedFiltration.CorrectedGradedVanishingTarget ...`, the
  published but unproved vanishing target. If grade `i` changes at the cut
  set `s`, it gives, for each normalizer lift `m` of `w⁻¹`, a standard
  `K ⊆ S \ s` with `M K = m⁻¹ (M I) m`.
- `htrans : CorrectedFiltration.CorrectedGradedTransitionTarget ...`, the
  published but unproved transition target. For such `K` it gives surjections
  `β_s` from step `i + 1` onto one fixed module. Their kernels are step `i`,
  and they are compatible with the actual transitions.
- `hLevi : actualLeviWeylIdentification T M cs`, the published target
  definition. The Weyl image of each `M J` is the standard subgroup `W_J`.
- `hA : IsInSupportCategory ... I ... A`, membership of `A` in `Alg({I})`.
- `hcover : CorrectedFiltration.IsBruhatCover T (P ∅) (P I)`. Only the two
  lifted theorems use it, through Worker 691's exhaustiveness lemma.
- For the two associated theorems at the end, three premises quantified over
  every `J` and `n : G` with `IsAssociate I J n` and
  `∀ x, x ∈ M J ↔ n⁻¹ * x * n ∈ M I`: `hcard` (`J.card = I.card`), `hsupp`
  (`A` lies in the support category at `J`) and `hcover` (the Bruhat cover
  `IsBruhatCover T (P ∅) (P J)`).

The variables are those of `General.CorrectedDegreeFiltration`. They are an
index type `ι` that is finite and linearly ordered, subgroup families
`P M U` with their semidirect, closedness, modulus and monotonicity data, the
closedness `hM` and Levi decompositions `hL` used by the support category,
an association predicate `IsAssociate`, and a subgroup `T` with finite Weyl
quotient and Coxeter system `cs`. The representation `A` is smooth, and
`I : Finset ι`. Write `w` for `Support.rankOrderedElement cs.length i hi`, the
`i`-th length-ordered Weyl element, and `|S| = Fintype.card ι`.

The definition `IsExactBefore` lives in `Langlands.Aubert.CutComplex.Diagram`.
All theorems live in `Langlands.Aubert.General.JacquetComplex`.

## The predicate `Diagram.IsExactBefore`

For a signed cut diagram `D` over a finite linearly ordered index type and
`n : ℕ`, `D.IsExactBefore n` is the conjunction of two statements:

- for every `k` with `k + 1 < n`, the range of `D.degreeDifferential k` equals
  the kernel of `D.degreeDifferential (k + 1)`;
- if `0 < n`, then `D.degreeDifferential 0` is injective.

It packages the exactness conclusions of this module and nothing more. It is
an internal definition, derived for this route. It is not a literature
definition. It says nothing about the terminal degree `n` itself.

## Generic graded pieces

The first three theorems use any subdiagrams `Lo` and `Up` of the actual
`jacquetDiagram ... A I`. Their coordinates at `s` must have the same members
as the `i`-th and `(i + 1)`-st corrected steps (premises `hLo` and `hUp`).

`graded_cases` is an eliminator for a proposition `Φ`. It needs
`hi : i < (Support.rankOrderedList cs.length).length`. It has two cases.

- Case A: every coordinate of `Up` lies in `Lo`.
- Case B: there are a standard `K`, a cut set `s₀` and a module `X`. Here
  `a ∈ W_K ↔ w⁻¹ a w ∈ W_I` holds for all `a`, and
  `Survives cs I K w s₀` holds. There is also a
  `Lo.BooleanContraction Up (Survives cs I K w) X`.

The proof is as follows. If steps `i + 1` and `i` agree at every `s`, case A
holds. Otherwise pick `s₀` where they differ and a normalizer lift `m` of
`w⁻¹` (`QuotientGroup.mk_surjective`). Then `hvan` gives `K ⊆ S \ s₀` with
`M K = m⁻¹ (M I) m`, and `mem_standardSubgroup_iff_of_leviConj hLevi` turns
this into the stated equality of Weyl subgroups. Minimality of `w` in
`W_{S \ s₀} w W_I` holds, since otherwise `CorrectedFiltration.step_succ_eq`
would make the two steps equal at `s₀`. Hence `s₀` survives. The contraction
coefficient at a surviving `s` is `SmoothRep.hom (β s ...)` from `htrans`,
composed with the inclusion of `Up.obj s` into step `i + 1`. Surjectivity,
kernel and naturality are those of `β`, transported along `hLo` and `hUp`.
For the `inactive` field, let `s` not survive. If `w` is not minimal in
`W_{S \ s} w W_I`, then `step_succ_eq` makes the steps equal. If `w` is
minimal, then `K ⊄ S \ s`. If the steps still differed at `s`, `hvan` would
give some `K' ⊆ S \ s` with `M K' = m⁻¹ (M I) m`. Then
`eq_of_standardSubgroup_conj` gives `K = K'`, which is a contradiction.

`graded_range_eq_ker`: for `k + 1 < |S| - |I|`, the degree differentials
`k` and `k + 1` of `Lo.quotientDiagram Up` satisfy `range = ker`. In case A
this is the published `quotient_exact_of_le`. In case B it is
`range_eq_ker_of_survives`.

`graded_injective_zero`: for `0 < |S| - |I|`, the degree-zero differential of
`Lo.quotientDiagram Up` is injective. It uses `quotient_injective_of_le` or
`injective_zero_of_survives`.

## Actual graded pieces and lifting

`gradedDiagram_range_eq_ker` and `gradedDiagram_injective_zero` state the same
two conclusions for Worker 691's `gradedDiagram ... i`. That diagram is
`(stepSubdiagram ... i).quotientDiagram (stepSubdiagram ... (i + 1))`, so
`hLo` and `hUp` hold by `Iff.rfl`.

`degreeDifferential_exact_of_targets` adds `hcover`. For
`k + 1 < |S| - |I|` it gives `range = ker` for the degree differentials `k`
and `k + 1` of the actual `jacquetDiagram ... A I`.
`degreeDifferential_injective_zero_of_targets` adds `hcover` and gives
injectivity of the actual degree-zero differential for `0 < |S| - |I|`. Both
apply Worker 691's `degreeDifferential_exact_of_graded` and
`degreeDifferential_injective_of_graded` to the graded results at every
`i < (Support.rankOrderedList cs.length).length`.

## The `FiniteFiltered.gradedMap` form

Worker 691's `gradedDifferential ... i k` is the
`FiniteFiltered.gradedMap` of the actual degree differential `k` on grade `i`
of `degreeFiltration`. `gradedDifferential_range_eq_ker` gives, for
`k + 1 < |S| - |I|`, `range = ker` for `gradedDifferential ... i k` and
`gradedDifferential ... i (k + 1)`. `gradedDifferential_injective_zero` gives
injectivity of `gradedDifferential ... i 0` for `0 < |S| - |I|`. Both take the
premises of `gradedDiagram_range_eq_ker`. They transfer its conclusions along
Worker 691's `gradedDifferential_exact_iff` and
`gradedDifferential_injective_iff`.

## Associated Jacquet diagrams

These two theorems have exactly the shape of the `hex` and `hinj` premises
of Worker 691's `isExactBeforeTerminal_of_jacquet`. That module is not
imported here.

`associated_degreeDifferential_exact_of_targets` takes `hvan`, `htrans`,
`hLevi`, `hcard`, `hsupp` and `hcover`. Its conclusion is the following.
For every `k` with `k + 1 < Complex.terminalDegree I`, and every `J`, `n` with
`IsAssociate I J n` and `∀ x, x ∈ M J ↔ n⁻¹ * x * n ∈ M I`, the degree
differentials `k` and `k + 1` of the actual `jacquetDiagram ... A J` satisfy
`range = ker`.

`associated_degreeDifferential_injective_zero_of_targets` takes the same
premises. If `0 < Complex.terminalDegree I`, then for every such `J` and `n`
the degree-zero differential of `jacquetDiagram ... A J` is injective.

In both proofs, `degreeDifferential_exact_of_targets` or
`degreeDifferential_injective_zero_of_targets` is applied at `J` with
`hsupp` and `hcover` at `J`. The bound
`Complex.terminalDegree I = |S| - |I|` is turned into `|S| - |J|` by
rewriting with `hcard`.

## Packaged forms

`gradedDiagram_isExactBefore` takes the premises of
`gradedDiagram_range_eq_ker`, without `k`. It gives
`(gradedDiagram ... i).IsExactBefore (|S| - |I|)`, from
`gradedDiagram_range_eq_ker` and `gradedDiagram_injective_zero`.

`jacquetDiagram_isExactBefore_of_targets` takes `hvan`, `htrans`, `hLevi`,
`hA` and `hcover`. It gives
`(jacquetDiagram ... A I).IsExactBefore (|S| - |I|)`, from
`degreeDifferential_exact_of_targets` and
`degreeDifferential_injective_zero_of_targets`.

## Provenance and scope

Everything here is derived. The module proves conditional consequences of the
published targets listed above. It uses no literature assertion beyond those
premises.

Nothing here compares the Jacquet diagram with the standard complex. Nothing
here treats the terminal degree or discharges any premise above.
