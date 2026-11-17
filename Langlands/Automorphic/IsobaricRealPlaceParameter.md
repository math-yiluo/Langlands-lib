# Real-place parameters of isobaric constituent data

Worker 766, Task 7484. This is internal bookkeeping over the published `IsobaricData` and
`ArchimedeanPlaceParameterClasses` definitions. It concerns finite multisets of actual
positive-rank cuspidal classes, with every multiplicity retained, and constructs no
isobaric or parabolically induced automorphic representation.

For a number field `F` with the existing compactness assumption, an actual real place
`v : {v : NumberField.InfinitePlace F // v.IsReal}`, and `ds : List RealBlock`,
`IsobaricData.HasRealPlaceParameter D v ds` means that there are a natural number `b`, an enumeration
`σ : Fin b → PositiveRankCuspidalClass F` satisfying `Finset.univ.val.map σ = D`, and lists
`d : Fin b → List RealBlock`, such that every `d j` satisfies the existing literal predicate
`(σ j).HasRealPlaceParameter v (d j)` and `ds.Perm ((List.ofFn d).flatten)`.

All conditions of the cuspidal predicate are retained: its total rank equation and its
injective map from the literal standard-module K-finite space intertwining the compact and
Lie actions. Permutation closure is taken only after aggregation. In particular the
singleton lemma identifies the new relation with
`∃ ds', c.HasRealPlaceParameter v ds' ∧ ds.Perm ds'`, rather than with the literal cuspidal
predicate itself. No permutation invariance theorem about that literal predicate is used.
The only field universe is that of `F`; there is no spectral-presentation universe.

The elementary lemmas follow the enumeration:

- `HasRealPlaceParameter.realRank_eq` proves `realRank ds = D.rank`. A private finite-index
  induction shows that the rank of the flattened family is the sum of the ranks. Permutation
  preserves this sum, each literal cuspidal predicate supplies its rank equation, and the
  multiset enumeration supplies the final equality with `D.rank`.
- `HasRealPlaceParameter.of_perm` and `hasRealPlaceParameter_perm_iff` compose list
  permutations without changing the enumeration or the literal constituent witnesses.
- `hasRealPlaceParameter_zero_iff` proves that the zero datum has a parameter exactly when
  `ds = []`. Applying multiset cardinality makes the enumeration size zero, and the reverse
  direction uses empty families.
- `hasRealPlaceParameter_ofCuspidal_iff` uses cardinality to make the enumeration size one
  and multiset membership to identify that single class with `c`; the converse uses a
  one-term enumeration.
- `HasRealPlaceParameter.eq_zero_iff` proves, under the parameter hypothesis, `D = 0 ↔ ds = []`.
  The forward implication is the zero lemma; the reverse uses the parameter rank equation
  and the published positive-rank criterion `IsobaricData.rank_pos_iff`.

Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
(1989), registered source `arthur-clozel-1989-base-change`, Chapter III Definition 1.2,
printed p.199 / PDF p.213, and Theorem 5.1, printed pp.212–213 / PDF pp.226–227, motivate a
later strong-lifting support premise at every finite and infinite place. This aggregation
is an internal supporting definition, not a verbatim transcription of those results.

In the intended later real-place clause, a real upstairs place uses this same real block
list; a complex upstairs place uses the list `realParameterRestrictToComplex ds` defined in
`Langlands.LocalFactor.ArchimedeanRestriction`. The upstairs place is put in its actual
subtype using its `IsReal` or `IsComplex` proof. No new coordinate on a place is chosen here.
The local restriction formulas are motivated by the published real-Weil action identities;
those identities do not prove global compatibility.

This unit asserts no existence or uniqueness of parameters, classification of characters,
realization of isobaric representations, restricted sum-model isomorphism, or compatibility
with weak global base change. The latter remains an explicitly unproved external premise.
