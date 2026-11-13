# Abstract row insertion for weakly decreasing integer rows

Worker 5734. This is the first of three helper modules for the proof of
`Langlands.MoeglinWaldspurger.involutivity`. The proof module is
`MoeglinWaldspurgerInvolutivityProof`. This module imports only Mathlib. It does not
mention multisegments. Every definition here is an internal construction for the
involutivity proof. None formalizes a definition from the literature. In the
namespace `Langlands.MoeglinWaldspurger.Row` it proves facts about one row of
integers under a Schensted-type insertion. The module
`MoeglinWaldspurgerKnuthSystem` uses these facts to describe a row of a
multisegment.

## Definitions

- `Desc l` says that the integer list `l` is weakly decreasing
  (`l.Pairwise (fun x y => y ≤ x)`).
- `rIns R a` inserts the letter `a` into the row `R`. If some entry of `R` is
  strictly smaller than `a`, the first such entry `s` is replaced by `a`, and the
  output is `some s`. Otherwise `a` is appended at the end, and the output is
  `none`. For a weakly decreasing row, this is Schensted row insertion with the
  order reversed. The bumped entry is the largest entry below `a`.
- `rRun R w` inserts the letters of the word `w` from left to right. It returns
  the final row and the list of outputs, one per letter (`rRun_length`).

## Basic facts

- `rIns_cons_lt`, `rIns_cons_ge`, `rRun_cons` and `rRun_append` unfold the
  definitions.
- `rIns_prefix`, `rRun_prefix` and `rRun_front` say that leading entries at least
  as large as every inserted letter are never touched.
- `mem_rIns` says that every entry of the new row is an old entry or the letter.
  `rIns_desc` says that insertion keeps a row weakly decreasing.
- `rIns_none_iff` says that the output is `none` exactly when every entry is
  `≥ a`. `rIns_of_none` says that the row is then `R ++ [a]`.
- `rIns_some` treats a weakly decreasing row with output `some m`. Then `m ∈ R`,
  `m < a`, and every entry of `R` below `a` is `≤ m`. As multisets, the new row
  is `R.erase m + {a}`.
- `rRun_allBelow` and `rRun_nil_row` compute the insertion of a weakly decreasing
  word whose letters all exceed every row entry. Each letter in turn replaces the
  next row entry, and the remaining letters are appended.
- `rRun_decOuts` treats a weakly decreasing word inserted into a weakly
  decreasing row. Its outputs have the form `A.map some ++ replicate k none`,
  where `A` is a sublist of the row. So the bumped entries form a weakly
  decreasing subsequence of the row, and they occur before all appended letters.
  The proof is by induction on the row, with a case split on whether its first
  entry is below the first letter.

## The single-row lemma

`KP P d Q e` (a Knuth pair) says three things: `P ++ d :: Q` is weakly
decreasing, every entry of `P` is `≥ e`, and `d < e`. The theorem `srl`
compares two words letter by letter, for a weakly decreasing row `R` and such a
pair:

- `Y = P ++ d :: Q ++ [e]`,
- `X = d :: (P ++ e :: Q)`.

It proves two things:

1. The two words produce the same final row.
2. The output lists satisfy `SRLOut R d oY oX`. This means
   `oY = A.map some ++ replicate k none ++ [some ε]`, where every entry of `A` is
   in `R`, and `ε ∈ R` or `ε = d`. In addition, one of the following holds.
   - (EQ) `k > 0`, `A ++ [ε]` is weakly decreasing, and
     `oX = none :: ((A ++ [ε]).map some ++ replicate (k - 1) none)`. The
     same letters are bumped in the same order. Only one `none` moves to the
     front.
   - (RW) `R ≠ []` and `A = A₁ ++ a :: A₂` with `KP A₁ a A₂ ε`, and
     `oX = some a :: ((A₁ ++ ε :: A₂).map some ++ replicate k none)`. Here the
     bumped words are again the two words of a Knuth pair, one level down.

`SRLOut.mono` enlarges the row in this conclusion. `SRLOut.cons_hi` adds a new
first row entry `s ≥ d` whose extra output is first in `Y` and second in `X`. The `KP.*`
lemmas list elementary consequences of `KP`, and `KP.tail` drops the first
entry of `P`.

The proof of `srl` is by induction on the row `R = s :: R'`.

- Base case `srl_base`: every row entry is `< d`. This includes the empty row.
  The two processes are computed explicitly with `rRun_allBelow` and
  `rRun_prefix`. Both end with the row `P ++ e :: T`, where `T` is the row after
  inserting `Q` into the part of `R` that is not used up. In `Y`, the last letter
  `e` bumps `d`. In `X`, the first letter `d` becomes the first row entry. It
  bumps the old first entry `s` when `R = s :: R'`, and it is appended when
  `R = []`. Then the auxiliary computation `hrow` handles the remaining letters
  `P ++ e :: Q`. The case `R = []` gives (EQ) with `A = []` and `ε = d`. The
  case `R = s :: R'` gives (RW) with `A₁ = []` and `a = s`.
- Case (α): every entry of `P` and `e` are at most `s`. Then `s` is never
  bumped by either word. The claim follows from the induction hypothesis by
  `rRun_front` and `SRLOut.mono`.
- Case (β): `P = p :: P'` with `d ≤ s < p`. In both words the letter `p` bumps
  `s`, and `p` then stays fixed. In `X` the letter `d` is first inserted into
  the rest of the row. The remaining runs are the two runs of the induction
  hypothesis for `R'` and `P'`. `SRLOut.cons_hi` accounts for the extra output
  `some s`, which is the first output of `Y` and the second output of `X`.
- Case (γ): `P = []` with `d ≤ s < e`. In `Y` the last letter `e` bumps `s`. In
  `X` the letter `e` bumps `s` directly after `d` is inserted below `s`. The
  outputs are compared using `rRun_decOuts` for the word `d :: Q`. This gives
  (EQ) when the run of `d :: Q` bumps nothing, and (RW) with `A₁ = []` otherwise.

The base case covers every row whose first entry is `< d`. So the inductive step
can assume `d ≤ s`, and then (α), (β) and (γ) cover all cases.
