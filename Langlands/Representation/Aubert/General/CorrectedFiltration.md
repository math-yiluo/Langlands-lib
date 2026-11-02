# The corrected support filtration of the general Aubert complex

Implementation and documentation: Worker 379 (task
`0a1bd7fb-66c2-4dcc-a3c8-6619f6fa10b4`, the complex-and-targets unit of the
general Aubert program `46df6a68-5db4-4428-8044-05151d6ce1f6`). The complex, its
terms and its transition maps are Worker 194's (`Aubert.General.Complex`,
`Aubert.General.StandardComplex`).

This module constructs the support filtration that the 1996 erratum uses to prove
the corrected Theorem 3.6, in the form repaired by Ban and Jantzen (2016,
Section 4). For a source index `I` and a target index `J`, it filters the
normalized Jacquet module `r_I(E_J)` of the term `E_J = i_J r_J E` of the complex
by the images of functions supported on unions of Bruhat cells. It proves the
laws of this filtration that follow from the definitions. The graded pieces and
graded transition maps are the subject of the separate targets in
`CorrectedFiltrationStatements`. Nothing about them is asserted here.

## Source

Erratum, printed p. 4687: "Notons Θ l'ensemble des parties θ de W telles que, si
w ∈ θ et l(w) < l(w′), alors w′ ∈ θ. Soit Θ_J ⊂ Θ l'ensemble des θ ∈ Θ qui sont
stables par multiplication à gauche par W_J. Pour tout θ ∈ Θ_J, nous posons
G_θ := ⋃_{w∈θ} B w P_I et nous notons Ẽ^θ_J le sous-module de Ẽ_J formé des
éléments de Ẽ_J à support compact contenu dans G_θ." On p. 4688 the erratum
extends this to every `θ ∈ Θ` through the largest element of `Θ_J` contained in
`θ`, and on p. 4689 it chooses a chain `θ_1 = W ⊃ θ_2 ⊃ … ⊃ θ_{t+1} = ∅` with
singleton differences. Ban and Jantzen (Section 4, printed p. 161) replace the
left-invariant core by the two-sided one: "We define θ′ ⊂ θ to be the largest
subset which is left-invariant under multiplication by W_J and right-invariant
under multiplication by W_I." The image of `Ẽ^θ_J` in `Ẽ_{J,I} = r^G_{L_I}(Ẽ_J)`
is the erratum's `Ẽ^θ_{J,I}` (p. 4688).

## Generic layer

* `functionSupport σ X`, for a representation `σ` of a subgroup `P` of a
  topological group `G` and a set `X ⊆ G`, is the submodule of smooth induced
  functions `f` with `f(g) ≠ 0 ⇒ g ∈ X`. It is monotone in `X`, zero for
  `X = ∅` and everything for `X = G`. Right translation by `q` preserves it when
  `X q⁻¹ ⊆ X` (`functionSupport_smoothInduced`).
* `jacquetImage hQ hN A S hS`, for a decomposition `Q = L ⋉ N` with `N` closed and
  a `Q`-stable submodule `S` of a smooth representation `A` of `G`, is the image
  of `S` under the actual quotient map `Jacquet.Localization.mk` in the normalized
  Jacquet module `(jacquetFunctor hQ hN).obj A`. It is an `L`-subrepresentation,
  because the normalized action is `m · [v] = δ(m)^{-1/2} [m v]`. It is monotone
  in `S`, zero for `S = 0` and everything for `S = A` (the quotient map is
  surjective). An intertwiner `f : A ⟶ A'` with `f(S) ⊆ S'` maps the image of `S`
  into that of `S'` under the actual functor map (`jacquetImage_map`).

These two constructions are generic. They hold for any group and decomposition.

## Weyl cells

The Weyl group is the actual relative Weyl quotient
`Group.RelativeWeyl.Weyl T = N_G(T)/Z_G(T)` of a subgroup `T` of `G`.

* `cellSupport T B Q θ` is the set of `g = b n q` with `b ∈ B`, `q ∈ Q` and
  `n ∈ N_G(T)` a lift of some element of `θ ⊆ W`. All lifts are used, so no
  representatives are chosen. It is right `Q`-stable, monotone in `θ` and empty
  for `θ = ∅`.
* `IsBruhatCover T B Q` is the proposition that every element of `G` lies in some
  `B n Q` with `n ∈ N_G(T)`. Then `cellSupport T B Q W = G` (`cellSupport_univ`).
  For a connected reductive group this is the Bruhat decomposition
  `G = ⋃_{w} B w P_I`. It is a structural fact about the group and is used only
  as an explicit hypothesis of `step_length`.

## Modified supports

Given a Coxeter system `cs` on a finite group `W` with simple indices `ι`,
`modifiedSupport cs J I i` is the published `Support.modifiedRankSupport` for
`H = W_J`, `K = W_I` (`Group.RelativeWeylIndexing.standardSubgroup`) and the
Coxeter length: the largest subset of the `i`-th length-ordered prefix that is
left `W_J`- and right `W_I`-invariant. The length-ordered prefixes list the
elements by decreasing length, so they are the erratum's sets `θ` in increasing
indexing (see `RankOrderedSupports.md`).

* `modifiedSupport_monotone`: monotone in `i`.
* `modifiedSupport_antitone_target`: for `J' ⊆ J` it only grows,
  `θ_i'(J) ⊆ θ_i'(J')`, because `W_{J'} ≤ W_J`.
* `mem_modifiedSupport_succ_iff`: the `i`-th length-ordered element `w` lies in
  `θ_{i+1}'(J)` (equivalently, the modified support changes at `i`, by
  `modifiedRankSupport_succ_ne_iff`) if and only if `w` is the minimal-length
  element of its double coset `W_J w W_I`
  (`Group.RelativeWeylIndexing.IsMinimal cs J I w`). One direction is the
  published double-coset minimality `modifiedRankSupport_succ_minimal`. For the
  other, every other element of the double coset is strictly longer than `w`,
  by the published uniqueness of minimal double-coset representatives
  (`minimalRepresentativeUnique_proof`), so it lies in the length-upper prefix.

## The filtration of `r_I(E_J)`

The standard families `P M U` of `Aubert.General` and the data
`h hclosed hδ hP hU` are those of `StandardComplex`, with `P` monotone and `U`
antitone in the standard index. As in `StandardComplex`, the terms are indexed by
the removed roots `s`, so that `J = S \ s`:

* `term P M U h hclosed A s` is `Complex.termObject` for the removed-root
  families; it is definitionally `i_J r_J A` (`StandardComplex.termObject_eq`).
* `transition P M U h hclosed hδ hP hU A hst`, for `s ⊆ t` (so `J' ⊆ J`), is
  Worker 194's actual transition `φ^J_{J'}` as a morphism of smooth
  representations. At each point it applies the canonical quotient map
  `r_J A → r_{J'} A` (`Complex.transition_eval`).

For a subgroup `T` with `Weyl T` finite (with decidable equality) and a Coxeter
system `cs` on `Weyl T` indexed by the simple roots `ι`:

* `groupSupport P T cs I s i = cellSupport T (P ∅) (P I) (θ_i'(S \ s))` is the
  erratum's `G_{θ_i'}`, with `B = P ∅` the minimal standard parabolic.
* `inductionStep … A I s i` is the submodule of `E_J` of functions supported in
  `G_{θ_i'}`. It is `P_I`-stable (`inductionStep_stable`).
* `step … A I s i` is its image in `r_I(E_J) = (jacquetFunctor (h I) (hclosed I)).obj
  (term … A s)`: the erratum's `Ẽ^{θ_i'}_{J,I}`, an actual
  `M_I`-subrepresentation.

The support condition is "nonzero only on `G_{θ_i'}`". The erratum asks for
compact support contained in `G_θ`. A smooth induced function is locally constant,
so its nonzero set is open and closed. When `P_J \ G` is compact, as for
parabolic subgroups of reductive groups, the two conditions agree.

Proved laws:

* `step_monotone`: the steps increase with `i`.
* `step_zero`: the step at `0` is `0`.
* `step_length`: under `IsBruhatCover T (P ∅) (P I)`, the step at the cardinality
  of `W` is all of `r_I(E_J)`.
* `transition_mem_inductionStep` and `transition_mem_step`: the actual transition
  `φ^J_{J'}` maps functions supported in `G_{θ_i'(J)}` to functions supported in
  `G_{θ_i'(J')}`, and `r_I(φ^J_{J'})` maps each step of `r_I(E_J)` into the same
  step of `r_I(E_{J'})`. This is the erratum's sentence on p. 4689 ("elles
  respectent la filtration par Θ"). Its proof is pointwise: `φ` applies a linear
  map at each point, so the nonzero set shrinks, and
  `θ_i'(J) ⊆ θ_i'(J')`.
* `step_succ_eq`: if the `i`-th length-ordered element is not minimal in its
  double coset `W_J w W_I`, the steps at `i` and `i + 1` coincide, so the graded
  piece is zero.

## Scope

* The arbitrary smooth representation `A` has no finite-length condition. The
  filtration is indexed by the finite Weyl group, and its finiteness has nothing
  to do with the length of `A`.
* Nothing identifies `T`, `cs` or the families with an actual reductive group.
  For the rational points of a connected reductive group, `T` is the maximal split
  torus, `cs` is the Coxeter system of the relative Weyl group on the simple
  relative roots, and the families are the standard parabolic data. These
  identifications, and the Bruhat covering, belong to the structural framework
  (ledger requirements A01–A02 of the program). The public
  `Group.RelativeWeylIndexingTargets` records the corresponding Levi
  identifications.
* The graded identification `Ẽ^{θ_{i+1}'}_{J,I} / Ẽ^{θ_i'}_{J,I} ≅
  Ad(w⁻¹)(r_{wL_Iw⁻¹}(E))`, its vanishing outside the surviving indices, and the
  identity form of the graded transitions are the targets of
  `CorrectedFiltrationStatements`.

## Declarations

* Generic: `functionSupport`, `mem_functionSupport`, `functionSupport_mono`,
  `functionSupport_empty`, `functionSupport_univ`, `functionSupport_smoothInduced`,
  `jacquetImage`, `mem_jacquetImage`, `jacquetImage_mono`, `jacquetImage_eq_bot`,
  `jacquetImage_eq_top`, `jacquetImage_map`.
* Cells: `cellSupport`, `IsBruhatCover`, `cellSupport_mul_right`,
  `cellSupport_mono`, `cellSupport_empty`, `cellSupport_univ`.
* Coxeter: `modifiedSupport`, `modifiedSupport_monotone`,
  `modifiedSupport_antitone_target`, `mem_modifiedSupport_succ_iff`.
* Filtration: `term`, `transition`, `groupSupport`, `inductionStep`,
  `inductionStep_stable`, `step`, `step_monotone`, `step_zero`, `step_length`,
  `transition_mem_inductionStep`, `transition_mem_step`, `step_succ_eq`.

All are in namespace `Langlands.Aubert.General.CorrectedFiltration`. No
declaration uses axioms beyond Lean's standard ones.

## Sources

* A.-M. Aubert, *Erratum*, Trans. AMS 348 (1996), printed pp. 4687–4689.
* D. Ban and C. Jantzen, *The Langlands quotient theorem for finite central
  extensions of p-adic groups II: intertwining operators and duality*, Glasnik
  Matematički 51 (2016), Section 4, printed p. 161.
