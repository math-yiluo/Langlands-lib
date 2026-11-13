# Word insertion through several rows and the Knuth-type system lemma

Worker 5734. This is the third helper module for the proof of
`Langlands.MoeglinWaldspurger.involutivity`. It imports
`MoeglinWaldspurgerInsertion`, and through it `MoeglinWaldspurgerRowInsertion`.
The declarations are in the namespace `Langlands.MoeglinWaldspurger.Involution`.
The definitions `combine` and `CF` are internal constructions for this proof, and
every theorem is a fact about the published `dual` and the helper insertions.
The lemmas are combinatorial facts derived for this proof. They are not
formalizations of statements from the literature.

## Counts from row outputs

`combine os cs` computes the bump counts at the current row. `os` lists the
outputs of the abstract row insertion (`none` for no bump, `some b` for a bumped
entry `b`), and `cs` lists the counts of the bumped entries one row lower. A
`none` gives count `0`. The `i`-th `some` gives one more than the `i`-th entry of
`cs`. `combine_map_some`, `combine_replicate` and `combine_replicate_nil`
evaluate `combine` on the output shapes that occur below.

## Word insertion at a row (`rdw`)

Let `R` be weakly decreasing with entries `≤ g + 1`, let the word `w` have letters
`≤ g + 1`, and let every interval of `z` end below `g`. Then inserting `w` at row
`g` of `place ↑R g + z` gives

```
((insW z (g - 1) bumped).1 + place ↑(rRun R w).1 g,
 combine (rRun R w).2 (insW z (g - 1) bumped).2),
```

where `bumped = (rRun R w).2.filterMap id` lists the bumped entries in order. So
row `g` evolves by the abstract insertion `rRun`, and the bumped entries are
inserted, in order, at row `g - 1`. The proof is by induction on `w`, matching
`rd1_none` with `rIns_none_iff`/`rIns_of_none` and `rd1_some` with `rIns_some`.

`exists_decomp` splits a multisegment with endings `≤ g` into its top row (as a
weakly decreasing list `R`) and a part `z'` ending below `g`. When `R ≠ []`,
`z'` has smaller cardinality (`card_place_pos`). This cardinality is the
induction measure of the next two theorems.

## Monotone counts

`m1`: if every interval of `z` ends at `≤ g` and `w` is a weakly decreasing word
with letters `≤ g + 1`, then the bump counts `(insW z g w).2` are weakly
decreasing. The proof is a strong induction on the cardinality of `z`. By
`rRun_decOuts` the outputs at row `g` are `A.map some ++ replicate k none`, with
`A` a weakly decreasing sublist of the row. So the counts are the counts of `A` at
row `g - 1`, each plus one, followed by `k` zeros. The induction hypothesis
applies to `A` and the lower part.

`mono`: let every interval of `y` end at `≤ f`, and let `n` be the bump count of
the round `insR y f (f + 1)`. Then every interval of `dual (insR y f (f + 1)).1`
that ends at `f` has beginning `≥ f + 1 - n`. Equivalently, it is no longer than
the interval `[f + 1 - n, f]` emitted by the round. If row `f` of `y` is empty,
no interval of the residual's dual ends at `f` (`dual_endings`). Otherwise the
round bumps the largest entry `c` (`rd1_some`). The residual's dual is computed by
`rowProc`. Its intervals at row `f` are `[f - r, f]`, where `r` runs through the
counts of the remaining row entries inserted after `c` at row `f - 1`. Its other
intervals end below `f` (`dual_endings`). By `m1` for the weakly decreasing row these counts
are at most the count `n - 1` of `c`.

## The system lemma

`CF r t r' s` (the count fact) states three things:

- `↑s + {r'} = ↑r + {t}` as multisets,
- `r' < t`,
- every `x ∈ s` with `r' < x` satisfies `t ≤ x`.

`system`: let every interval of `z` end at `≤ g`, let `KP P d Q e` hold, and let all
letters be `≤ g + 1`. Then the words `Y = P ++ d :: Q ++ [e]` and
`X = d :: (P ++ e :: Q)`, inserted at row `g`, produce the same multisegment. Their
bump-count lists have the forms `r ++ [t]` (for `Y`) and `r' :: s` (for `X`), with
`CF r t r' s`.

The proof is a strong induction on the cardinality of `z`. It uses
`exists_decomp`, `rdw` for both words, and the single-row lemma `Row.srl` on the
top row. The final top rows agree. The outputs fall into the two cases of
`SRLOut`.

- (EQ) Both words bump the same weakly decreasing word `A ++ [ε]`, so the lower
  rows agree. Let `cs₀` be the counts of `A` at row `g - 1` and `cε` the count of
  `ε`. The witnesses are
  `r = cs₀.map (· + 1) ++ replicate (k' + 1) 0`, `t = cε + 1`, `r' = 0`, and
  `s = (cs₀ ++ [cε]).map (· + 1) ++ replicate k' 0`, where `k = k' + 1`. The
  multiset identity is a count comparison. `0 < t` is immediate. For the third
  condition, a positive `x ∈ s` is `c + 1` with `c ∈ cs₀ ++ [cε]`, and `m1` for
  the weakly decreasing word `A ++ [ε]` gives `cε ≤ c`.
- (RW) The bumped words are `A₁ ++ a :: A₂ ++ [ε]` and `a :: (A₁ ++ ε :: A₂)`
  with `KP A₁ a A₂ ε`. The induction hypothesis applies one row lower, to the
  smaller multisegment `z'`. It gives equal lower parts and counts `ρ ++ [τ]`,
  `ρ' :: σ` with `CF ρ τ ρ' σ`. The witnesses are
  `r = ρ.map (· + 1) ++ replicate k 0`, `t = τ + 1`, `r' = ρ' + 1` and
  `s = σ.map (· + 1) ++ replicate k 0`. The count fact is preserved when every
  count is shifted by one and the same number `k` of zeros is added on both sides.
