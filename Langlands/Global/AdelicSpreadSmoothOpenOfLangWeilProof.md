# Proof of Conrad's Theorem 4.5 from his Lemma 4.6

Author: Worker 250, reusing Worker 208's complete shared proof draft.
The Lean source is unchanged from shared draft revision 1 of Task 5166;
Worker 250 checked the published inputs and expanded this documentation.

`adelicSpreadSmoothOpenOfLangWeil` proves
`Langlands.Global.AdelicSpreadSmoothOpenOfLangWeilStatement.{u}`.
Given `UniformLangWeilStatement`
(Conrad's Lemma 4.6), it proves `AdelicSpreadSmoothOpenStatement` (his
Theorem 4.5) in both characteristics for arbitrary finite-type spreads.

## Source and scope

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), Theorem 4.5 and its proof on printed pp.12–13.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`, PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad chooses compatible smooth geometrically connected models, reduces to
local openness and almost-all integral surjectivity, and uses Lemma 4.6 and
Hensel lifting for the latter. The imported assembly and its inputs implement
these steps. This final implication is a derived packaging of that proof.

The target retains separated generic fibres, a smooth surjective
geometrically connected morphism, arbitrary finite-type spreads of source
and target, a finite constant field in the function-field branch, and all
infinite factors in the number-field branch. The common universe `u` is
arbitrary. No common fibre dimension is required.

## Implemented proof

The proof applies the published assembly theorems
`curvePlaceSpreadSmoothOpenAssembly` and `numberFieldSpreadSmoothOpenAssembly`
to the Lang–Weil hypothesis and to four published proofs of their remaining
premises, using the matching branch of each:

- `adelicLevelComponentSurjectivity`, almost-all native level surjectivity;
- `adelicSmoothLocalPointOpen`, smooth openness at every local factor;
- `adelicModelOpenReduction`, the fixed-model local-to-adelic reduction;
- `adelicSpreadGeometricallyConnected`, whose third clause in each branch
  gives compatible models for `Smooth ⊓ GeometricallyConnected`.

These are imported respectively from `AdelicSpreadSmoothOpenAssemblyProof`,
`AdelicLevelComponentSurjectivityProof`, `AdelicSmoothLocalOpen`,
`AdelicModelOpenReduction` and `AdelicSpreadGeometricallyConnectedProof`,
all under `Langlands.Global`. The projections `.1.2.2` and `.2.2.2` select
the model-existence clause for the function-field and number-field cases.
The level-surjectivity theorem still takes Lang–Weil as an argument; the
assembly passes the same hypothesis to it. The two resulting open-map
statements are paired to prove the unchanged target.

The proof adds no hypothesis besides `UniformLangWeilStatement`.
Declaration inspection reports the universe parameter `u` and only
`propext`, `Classical.choice` and `Quot.sound`. Lemma 4.6 itself remains a
separate obligation.
