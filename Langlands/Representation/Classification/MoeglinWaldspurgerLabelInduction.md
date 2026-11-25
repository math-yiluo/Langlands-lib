# The derivative-comparison induction for the MW recursion

Module `Langlands.Representation.Classification.MoeglinWaldspurgerLabelInduction`,
namespace `Langlands.MoeglinWaldspurger.Derivation`.

Fix a cuspidal datum `ρ` (saturated universe) and a real `x`. `HeadClass b n c` says that `c`
is the class of a Langlands head of `realize ρ x b` in rank `n`; `LabelClass b n c` that `c` is
a weak Zelevinsky label of `realize ρ x b`.

`DerivativeFacts LD` packages five facts about an abstract relation `LD c cls K S`, meant to
say that the irreducible class `cls` has highest left derivative of order `K` with respect to
the cuspidal `ν^{x+c} ρ`, with irreducible derivative `S`:

1. `unique`: equal data determine the class (Jantzen's lemma);
2. `unblocked`: if every occurrence of `b` ends at `c` or `c - 1` and no occurrence ending at
   `c - 1` precedes one ending at `c`, a Langlands head of `b` has data (number of occurrences
   ending at `c`, head of the shortened multisegment);
3. `inert`: the data of a Langlands head of `b` are those of its occurrences ending at `c` or
   `c - 1`, with the other occurrences added to the derivative;
4. `zmax`: a Zelevinsky label at the greatest support point `y` has data
   (number of `[y, y]`, label of the multisegment without them);
5. `zsocle`: adding an interval `I` with the greatest ending to a Zelevinsky label increases the
   order at `I.beginning` by one and replaces `I` by its left shortening in the derivative.

`labelClass_of_headClass` proves, from these facts and the two combinatorial targets
`TopUnmatchedCompatibility` and `ChainUnmatchedCompatibility`, that every head class of `a` is a
label class of `dual a`, by strong induction on the weight.

* `a = 0`: Theorem P and `adjustedOperator_rankZero` identify the rank-zero head with the label.
* Otherwise let `r` be the first round, `c` the beginning of the emitted interval and
  `a₁ = r.residual`. The label `V` of `dual a = r.emitted :: dual a₁` has data
  `(card (unmatched a₁ c) + 1, S)` by `zsocle`, using the induction hypothesis for `a₁` and for
  `leftDerivative a₁ c`. The head of `a` has data `(card (unmatched a c), S)`, where `S` is the
  head of `leftDerivative a c`. `headData_of_twoEnd` gives this whenever the part `J` of the
  multisegment ending at `c` or `c - 1` is strictly smaller. It applies `inert`, the induction
  hypothesis for `J`, `zmax` at the greatest point `c` of `dual J` and
  `TopUnmatchedCompatibility`. This covers the residual `a₁` always, and `a` whenever the round
  selects more than one interval or some occurrence of `a` ends below `c - 1`. In the remaining
  case (one selected interval, all occurrences ending at `c` or `c - 1`), `unblocked` applies
  (`unblocked_of_tail_nil`). `ChainUnmatchedCompatibility`
  identifies `dual (leftDerivative a c)` with `[c+1, e] + dual (leftDerivative a₁ c)` and the
  orders, so `unique` gives `cls = V`.

`labelCorrectness_of_derivativeFacts` gives the target `LabelCorrectness` of the assembly
module when such an `LD` exists on every cuspidal line.
