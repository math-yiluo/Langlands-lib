# The inert part of the derivative facts

Module `Langlands.Representation.Classification.MoeglinWaldspurgerInert`, namespace
`Langlands.MoeglinWaldspurger.Derivation`. Author: Worker 5735.

## Helpers

* `sortE s`: the occurrences of `s` sorted by increasing ending (`List.mergeSort`), with
  `coe_sortE`, `mem_sortE` and `sortE_pairwise`.
* `pairwise_noPrec_of_ending_le`: a later interval with an ending at least as large never
  precedes an earlier one.
* `filter_notTwoEnd_eq`: the occurrences not ending at `c` or `c - 1` are those ending below
  `c - 1` together with those ending above `c`.
* `castIso_listProd_congr`, `embeds_listProd_congr`: `listProd l` preserves `CastIso` and
  `Embeds` in its tail argument.
* `castIso_listProd_unit`: `(listProd l 1) × H ≅ listProd l H`, by `castIso_listProd_binary`
  and `castIso_rankZero_left`.
* `embeds_head_binary`: if `l.Pairwise NoPrec` and `π_h` is a Langlands head of the realization
  of `l`, then `π_h × H ↪ listProd l H` (`lsub_listProd` and `castIso_listProd_unit`).
* `nontrivial_of_irr'`: irreducible representations are nontrivial.

## `inert_LDrel`

Hypotheses: every occurrence of `δ` ends at `c` or `c - 1`; `clsJ` is the head class of
`J = b.filter (TwoEnd c)`; `SJ` is the head class of `δ`; `LDrel c clsJ K SJ` holds; `cls` is
the head class of `b`; and `S` is the head class of `b.filter (¬ TwoEnd c) + δ`. Conclusion:
`LDrel c cls K S`. The two interfaces are hypotheses `hL` and `hLS`.

Proof. Let `low`, `Jl`, `high` and `δl` be the occurrences of `b` ending below `c - 1`, those
of `J`, those of `b` ending above `c`, and those of `δ`, each sorted by ending. Set
`H = listProd high 1`. For `M = Jl` or `M = δl`, the list `low ++ (M ++ high)` is sorted by
ending, so it satisfies `Pairwise NoPrec`. Its multiset is `b` for `M = Jl`, and
`b.filter (¬ TwoEnd c) + δ` for `M = δl`.

1. Let `π_J` be the head of `J`. Then `X = listProd low (π_J × H)` embeds into
   `listProd (low ++ (Jl ++ high)) 1`, by `embeds_head_binary` and regrouping. `X` has finite
   length and is nontrivial, so it has an irreducible subrepresentation `W`
   (`SegmentHeadSupport.exists_irreducible_subrepresentation`). By `lsub_listProd`, `W` is a
   Langlands head of `b`, so `W ≅ π` (`multisegmentHeadClassification`). Hence `π ↪ X`.
2. The derivative data of the class `clsJ` give `π_J ↪ A_c^K × D_J` with `D_J` irreducible, of
   class `SJ` and left reduced. So `π ↪ listProd low ((A_c^K × D_J) × H)`. By
   `castIso_iterProd_binary` this is `listProd low (A_c^K × (D_J × H))`, and by
   `castIso_listProd_iterProd` it is `A_c^K × Y` with `Y = listProd low (D_J × H)`. The
   occurrences in `low` end below `c - 1`.
3. `Y` has finite length and is left reduced: the factors in `low` and `high` do not end at `c`,
   `D_J` is reduced, and the product clause applies. `Y` is nontrivial, so it has an irreducible
   subrepresentation. `D_J` is isomorphic to the head of `δ`, so `embeds_head_binary` gives
   `Y ↪ listProd (low ++ (δl ++ high)) 1`. By `lsub_listProd`, every irreducible
   subrepresentation of `Y` is a Langlands head of `b.filter (¬ TwoEnd c) + δ`.
4. `LDrel_of_embeds_head` concludes.
