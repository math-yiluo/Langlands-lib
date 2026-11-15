# Aubert correctness of the MW recursion from the two interfaces

Module `Langlands.Representation.Classification.MoeglinWaldspurgerConditionalCorrectness`,
namespace `Langlands.MoeglinWaldspurger.Derivation`. Author: Worker 5735.

* `derivativeFacts_LDrel hL hLS F T ρ x : DerivativeFacts F T ρ x (LDrel F T ρ x)`: the concrete
  highest left derivative relation `LDrel` satisfies the five derivative facts:
  - `unique` is `LDrel_unique`;
  - `unblocked` is `unblocked_LDrel`;
  - `inert` is `inert_LDrel`;
  - `zmax` is `zmax_LDrel`;
  - `zsocle` is `zsocle_LDrel`.

  The hypotheses are `hL : LeftCuspidalDerivativeLemma` and
  `hLS : LanglandsSubrepresentationRealization`.
* `universalAubertCorrectness_of_interfaces hL hLS : UniversalAubertCorrectness.{uF, uV}`: the
  published target, from the same two hypotheses. On every cuspidal line, `LDrel` provides the
  relation required by `labelCorrectness_of_derivativeFacts`. The two combinatorial inputs are
  the proved `topUnmatchedCompatibility` and `chainUnmatchedCompatibility`.
  `universalAubertCorrectness_of_labelCorrectness` then gives the target.

The result is conditional on exactly the two interface propositions; nothing else is assumed.
