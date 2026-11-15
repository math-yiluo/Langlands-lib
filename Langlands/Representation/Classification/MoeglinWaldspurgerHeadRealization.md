# Langlands heads inside products of segment heads along lists

Module `Langlands.Representation.Classification.MoeglinWaldspurgerHeadRealization`, namespace
`Langlands.MoeglinWaldspurger.Derivation`. Internal infrastructure for the derivative facts.

## Regrouping

* `castIso_listProd_append`: `listProd (l₁ ++ l₂) Y ≅ listProd l₁ (listProd l₂ Y)`, by
  induction on `l₁` with the binary congruence.
* `castIso_listProd_binary`: `(listProd l Y) × Z ≅ listProd l (Y × Z)` when `Y` and `Z` satisfy
  `PosOrIrr`, by induction with `castIso_assoc''`.
* `castIso_listProd_iterProd`: if every interval of `l` ends below `c - 1`, then
  `listProd l (A_c^K × Y) ≅ A_c^K × listProd l Y`. Such an interval is not linked with
  `[c, c]`, so `castIso_segHead_swap` and `castIso_commute` apply at each step.

## The empty datum and properties of `listProd`

* `empty_isIrreducible`, `empty_posOrIrr`, `empty_nontrivial`, `empty_hasFiniteLength`: the
  induced representation of the empty datum is one-dimensional
  (`SegmentProductOrderedAssembly.finrank_zeroDatum`), hence irreducible, nontrivial and of
  finite length.
* `listProd_hasFiniteLength`: binary products preserve finite length
  (`Aubert.binaryProduct_preservesFiniteLength`), and heads are irreducible.
* `segHead_nontrivial`, `head_nontrivial`, `binary_nontrivial_of`, `listProd_nontrivial`:
  irreducible representations are nontrivial, and binary products of nontrivial representations
  are nontrivial (`ProductVanishing.nontrivial_binary`).
* `head_leftReduced`: a segment head of the realized segment of `J` is left reduced for
  `ν^{x+y} ρ` when `J` does not end at `y`. This is the segment clause of the left cuspidal
  derivative lemma: the last cuspidal of the realized segment is `ν^{x+e} ρ`
  (`Interval.realize_last`), which differs from `ν^{x+y} ρ` by `cuspidalDatum_twist_injective`.
* `leftReduced_rankZero`: a rank-zero representation is left reduced, since `d + k = 0` is
  impossible for `d > 0`.
* `listProd_leftReduced`: products of finite-length left-reduced factors are left reduced
  (product clause of the left cuspidal derivative lemma).

## The Langlands subrepresentation realization along a list

* `NoPrec I J`: the realized segment of `J` does not precede that of `I`, written in interval
  coordinates (`realize_precedes_iff`).
* `lsub_listProd`: let `l` be a list with `l.Pairwise NoPrec`. Then every Langlands head of the
  realized multisegment of `l` embeds into `listProd l 1`, and every irreducible representation
  embedding into `listProd l 1` is a Langlands head of it. Proof: apply the hypothesis
  `LanglandsSubrepresentationRealization` to the datum `consHeads l empty`. Its blocks are
  segment heads. Its ordering condition is `l.Pairwise NoPrec`, read through
  `List.pairwise_ofFn` and `consHeads_segments`. Its multisegment is the realization of `l`, and
  its induced representation is `listProd l 1` (`consHeads_induced`). Ranks are matched by
  `listRank_eq` and `langlandsHead_degree`.

## The head version of the derivative-data wrapper

`LDrel_of_embeds_head` concludes `LDrel c (class of π) K S` from the following:

* `π ↪ A_c^K × Y`, with `Y` of finite length and left reduced;
* `Y` has an irreducible subrepresentation;
* every irreducible subrepresentation of `Y` is a Langlands head of the realization of `β`;
* `S` is the head class of `β`.

All irreducible subrepresentations of `Y` then have class `S` by `headClass_unique`, and
`LDrel_of_embedding` applies the comparison clause.
